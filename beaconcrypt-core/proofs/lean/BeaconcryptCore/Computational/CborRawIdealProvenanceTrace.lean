-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance

/-! Ideal provenance reads only accept ordinals and returned sessions, plus successful build sessions and assigned key IDs. This public projection forgets build payloads, serialized frames, finish tags and unrelated entries. Its constructive transport below preserves provenance without assuming equality of complete games or transcripts. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawIdealProvenanceTrace

open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentIdealProvenance (BuiltIn Prov)
open PqxdhDeploymentIdealTrace (sessionAt peerOf)
open PqxdhDeploymentTranscript (buildOf acceptCount)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhRecordLiftOrigins (Origins)
variable {KemSK : Type}

inductive Registration where
  | accept (session : Option Nat)
  | built (session : Nat) (keyId : Std.U64)

def entryShape : Entry → Option Registration
  | ⟨.inl (.inr (.accept _)), reply⟩ => some (.accept reply)
  | ⟨.inl (.inr (.build session _)), some response⟩ => some (.built session response.keyId)
  | _ => none

def shape (transcript : List Entry) : List Registration := transcript.filterMap entryShape

def acceptReplies (registrations : List Registration) : List (Option Nat) :=
  registrations.filterMap fun entry => match entry with
  | .accept session => some session
  | .built _ _ => none

def firstKey (session : Nat) : List Registration → Option Std.U64
  | [] => none
  | .accept _ :: rest => firstKey session rest
  | .built index keyId :: rest => if index = session then some keyId else firstKey session rest

theorem acceptReplies_shape (transcript : List Entry) :
    acceptReplies (shape transcript) = PqxdhDeploymentIdealTrace.acceptReplies transcript := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · exact ih
      · cases command
        all_goals first
          | exact ih
          | simpa only [shape, entryShape, List.filterMap_cons, acceptReplies,
              PqxdhDeploymentIdealTrace.acceptReplies] using congrArg (List.cons _) ih
          | (cases reply <;> exact ih)
      · exact ih

theorem built_shape (transcript : List Entry) (session : Nat)
    (response : PqxdhServerRegistrationPublication.Response) (built : BuiltIn transcript session response) :
    Registration.built session response.keyId ∈ shape transcript := by
  obtain ⟨payload, member⟩ := built
  exact List.mem_filterMap.mpr ⟨⟨.inl (.inr (.build session payload)), some response⟩, member, rfl⟩

theorem shape_built (transcript : List Entry) (session : Nat) (keyId : Std.U64)
    (member : Registration.built session keyId ∈ shape transcript) :
    ∃ response, BuiltIn transcript session response ∧ response.keyId = keyId := by
  obtain ⟨entry, present, shaped⟩ := List.mem_filterMap.mp member
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases shaped
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases shaped
        | some response =>
            simp only [entryShape, Option.some.injEq, Registration.built.injEq] at shaped
            obtain ⟨rfl, key⟩ := shaped
            exact ⟨response, ⟨payload, present⟩, key⟩
    | _ => cases shaped
  · cases shaped

theorem firstKey_shape (transcript : List Entry) (session : Nat) :
    firstKey session (shape transcript) = (buildOf transcript session).map (·.keyId) := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · exact ih
      · cases command with
        | build index payload =>
            cases reply with
            | none => exact ih
            | some response =>
                by_cases same : index = session
                · simp [shape, entryShape, firstKey, buildOf, same]
                · simpa [shape, entryShape, firstKey, buildOf, same] using ih
        | _ => exact ih
      · exact ih

theorem acceptCount_eq (left right : List Entry) (same : shape left = shape right) :
    acceptCount left = acceptCount right := by
  rw [← PqxdhDeploymentIdealTrace.acceptReplies_length, ← PqxdhDeploymentIdealTrace.acceptReplies_length,
    ← acceptReplies_shape left, same, acceptReplies_shape]

theorem sessionAt_eq (left right : List Entry) (same : shape left = shape right) (index : Nat) :
    sessionAt left index = sessionAt right index := by
  rw [sessionAt, sessionAt, ← acceptReplies_shape left, same, acceptReplies_shape]

theorem peerOf_eq {count : Nat} (target : Target count) (left right : List Entry)
    (same : shape left = shape right) : peerOf target left = peerOf target right := by
  unfold peerOf
  rw [sessionAt_eq left right same]
  congr 1
  funext session
  rw [← firstKey_shape left, same, firstKey_shape]

theorem built_transport (left right : List Entry) (same : shape left = shape right)
    (session : Nat) (response : PqxdhServerRegistrationPublication.Response) (built : BuiltIn right session response) :
    ∃ original, BuiltIn left session original ∧ original.keyId = response.keyId := by
  apply shape_built left session response.keyId
  rw [same]
  exact built_shape right session response built

/-- Provenance transports through the actual registration shape; serialized payload equality is unnecessary. -/
theorem prov_transport {count : Nat} (target : Target count) (left right : List Entry)
    (same : shape left = shape right) (environment : EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2)
    (holds : Prov target left environment world origins) : Prov target right environment world origins := by
  refine ⟨holds.ann, holds.peerKey, holds.ownerKey, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← acceptCount_eq left right same]
    exact holds.accepts
  · intro early
    obtain ⟨sessions, pending, builds⟩ := holds.early early
    refine ⟨sessions, pending, ?_⟩
    intro session response built
    obtain ⟨original, old, _keyId⟩ := built_transport left right same session response built
    exact builds session original old
  · intro session coordinate marked
    obtain ⟨selected, slot, pending⟩ := holds.marked session coordinate marked
    refine ⟨selected, slot, ?_⟩
    intro open_
    obtain ⟨returned, unbuilt⟩ := pending open_
    refine ⟨?_, ?_⟩
    · rw [← sessionAt_eq left right same]
      exact returned
    · intro response built
      obtain ⟨original, old, _keyId⟩ := built_transport left right same session response built
      exact unbuilt original old
  · intro session coordinate response marked built
    obtain ⟨original, old, keyId⟩ := built_transport left right same session response built
    simpa only [keyId] using holds.built session coordinate original marked old
  · intro keyId coordinate peer
    rw [← peerOf_eq target left right same]
    exact holds.peerOf keyId coordinate peer

theorem prov_iff {count : Nat} (target : Target count) (left right : List Entry)
    (same : shape left = shape right) (environment : EnvState KemSK SplitBk)
    (world : PqxdhRecordLiftWorld.State 2) (origins : Origins 2) :
    Prov target left environment world origins ↔ Prov target right environment world origins :=
  ⟨prov_transport target left right same environment world origins,
    prov_transport target right left same.symm environment world origins⟩

end BeaconcryptCore.Computational.CborRawIdealProvenanceTrace

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.acceptReplies_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.acceptReplies_shape
/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.built_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.built_shape
/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.shape_built' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.shape_built

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.firstKey_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.firstKey_shape

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.acceptCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.acceptCount_eq

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.sessionAt_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.sessionAt_eq

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.peerOf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.peerOf_eq

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.built_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.built_transport

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.prov_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.prov_transport

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.prov_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceTrace.prov_iff
