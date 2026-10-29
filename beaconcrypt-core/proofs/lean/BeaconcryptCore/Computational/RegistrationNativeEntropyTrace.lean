-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyCompile
import BeaconcryptCore.Computational.PqxdhDeploymentTranscript

/-! Decode the private old transcript by removing metadata transport and restoring original public HMAC messages. Registration, coins, records, test/fresh and all Mode O replies remain literal. Functions that ignore HMAC entries, including registration summaries and target lookup projections, are unchanged by this decoding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyTrace
open PqxdhDeploymentInterface (Entry)
open RegistrationNativeEntropyInterface (decode metadata userHmac)
variable {A S : Type}

def stripEntry : Entry → Option Entry
  | ⟨.inl (.inr (.hmac key message)), reply⟩ => match decode message with
      | some (.hmac original) => some ⟨.inl (.inr (.hmac key original)), reply⟩
      | _ => none
  | entry => some entry

def strip (transcript : List Entry) : List Entry := transcript.filterMap stripEntry

/-- Creation metadata is private adapter bookkeeping and contributes no native transcript entry. -/
theorem strip_metadata (key reply : PqxdhSecretInputKdf.HmacBlock) (mlPin : Pqxdh.Bytes) :
    stripEntry ⟨.inl (.inr (.hmac key (metadata mlPin))), reply⟩ = none := by
  simp only [stripEntry, RegistrationNativeEntropyInterface.decode_metadata]

/-- The original HMAC key, message and full reply are restored exactly. -/
theorem strip_hmac (key reply : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    stripEntry ⟨.inl (.inr (.hmac key (userHmac message))), reply⟩ =
      some ⟨.inl (.inr (.hmac key message)), reply⟩ := by
  simp only [stripEntry, RegistrationNativeEntropyInterface.decode_userHmac]

/-- Decoding preserves chronological concatenation. -/
theorem strip_append (first second : List Entry) : strip (first ++ second) = strip first ++ strip second :=
  List.filterMap_append

private theorem projection_entry (observe : Entry → Option A)
    (free : ∀ key message reply, observe ⟨.inl (.inr (.hmac key message)), reply⟩ = none) (entry : Entry) :
    (stripEntry entry).bind observe = observe entry := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    rename_i key message
    cases decoded : decode message with
    | none => simp only [stripEntry, decoded, Option.bind_none, free]
    | some transport => cases transport <;>
        simp only [stripEntry, decoded, Option.bind_none, Option.bind_some, free]
  · rfl

/-- Every registration-only projection retains exactly its original selected entries and ordering. -/
theorem projection_strip (observe : Entry → Option A)
    (free : ∀ key message reply, observe ⟨.inl (.inr (.hmac key message)), reply⟩ = none)
    (transcript : List Entry) : (strip transcript).filterMap observe = transcript.filterMap observe := by
  unfold strip
  rw [List.filterMap_filterMap]
  exact congrArg (fun action => transcript.filterMap action) (funext (projection_entry observe free))

private theorem fold_entry (action : S → Entry → S)
    (free : ∀ before key message reply, action before ⟨.inl (.inr (.hmac key message)), reply⟩ = before)
    (before : S) (entry : Entry) :
    (stripEntry entry).elim before (action before) = action before entry := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    rename_i key message
    cases decoded : decode message with
    | none => simp only [stripEntry, decoded, Option.elim_none, free]
    | some transport => cases transport <;>
        simp only [stripEntry, decoded, Option.elim_none, Option.elim_some, free]
  · rfl

/-- A state update that ignores HMAC entries has the same complete final state after transcript decoding. -/
theorem foldl_strip (action : S → Entry → S)
    (free : ∀ before key message reply, action before ⟨.inl (.inr (.hmac key message)), reply⟩ = before)
    (transcript : List Entry) (before : S) : (strip transcript).foldl action before = transcript.foldl action before := by
  induction transcript generalizing before with
  | nil => rfl
  | cons entry rest ih =>
      have one := fold_entry action free before entry
      cases found : stripEntry entry with
      | none =>
          have same : before = action before entry := by simpa only [found, Option.elim_none] using one
          simpa only [strip, List.filterMap_cons, found, List.foldl_cons, ← same] using ih before
      | some next =>
          have same : action before next = action before entry := by simpa only [found, Option.elim_some] using one
          simpa only [strip, List.filterMap_cons, found, List.foldl_cons, same] using ih (action before next)

private theorem count_projection (predicate : Entry → Bool) (transcript : List Entry) :
    (transcript.filterMap fun entry => if predicate entry then some () else none).length = transcript.countP predicate := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih => cases chosen : predicate entry <;> simp [chosen, ih]

/-- Accept/create/record counters ignore transport HMAC entries, so no extra target or record factor is introduced. -/
theorem countP_strip (predicate : Entry → Bool)
    (free : ∀ key message reply, predicate ⟨.inl (.inr (.hmac key message)), reply⟩ = false)
    (transcript : List Entry) : (strip transcript).countP predicate = transcript.countP predicate := by
  rw [← count_projection, ← count_projection]
  exact congrArg List.length (projection_strip
    (fun entry => if predicate entry then some () else none) (fun key message reply => by rw [free]; rfl) transcript)

/-- The exact public owner lifecycle and created pin list are unchanged by decoding. -/
theorem summarize_strip (transcript : List Entry) :
    PqxdhDeploymentTranscript.summarize (strip transcript) = PqxdhDeploymentTranscript.summarize transcript :=
  foldl_strip PqxdhDeploymentTranscript.step (fun _ _ _ _ => rfl) transcript _

private theorem findSome_head (observe : Entry → Option A) (transcript : List Entry) :
    transcript.findSome? observe = (transcript.filterMap observe).head? := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
      cases found : observe entry <;>
        simp only [List.findSome?_cons, List.filterMap_cons, found, List.head?_cons, ih]

/-- Original first-bundle/accept/build/finish lookups are unchanged, including failed transport-adjacent calls. -/
theorem findSome_strip (observe : Entry → Option A)
    (free : ∀ key message reply, observe ⟨.inl (.inr (.hmac key message)), reply⟩ = none)
    (transcript : List Entry) : (strip transcript).findSome? observe = transcript.findSome? observe := by
  rw [findSome_head, findSome_head, projection_strip observe free]

end BeaconcryptCore.Computational.RegistrationNativeEntropyTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_metadata' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_hmac' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_hmac
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.strip_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.projection_strip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.projection_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.foldl_strip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.foldl_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.countP_strip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.countP_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.summarize_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.summarize_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.findSome_strip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyTrace.findSome_strip
