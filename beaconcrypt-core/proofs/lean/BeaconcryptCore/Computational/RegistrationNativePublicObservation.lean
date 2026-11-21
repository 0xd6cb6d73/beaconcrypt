-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyRestore
import BeaconcryptCore.Computational.RegistrationNativeLedgerHiding
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! The entropy transport's complete native mode-P transcript is restored using only the old mode-P transcript. Its functional first-accept scanner uses the same first occurrence as `acceptOf`, counting decodable failed accepts before it. No raw plaintext or private fresh-message comparison enters either function. These are observation and first-payload correspondences; bounded canonical target coverage and identification of the scanner ordinal with the existing `AcceptedAt` event remain separate obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicObservation
abbrev OldPublic := PqxdhDeploymentInterface.PublicEntry .P
abbrev NativePublic := RegistrationNativeLedgerHiding.PublicEntry
open RegistrationNativeEntropyInterface (decode)
open RegistrationNativeLedgerHiding (view)

def restoreEntry (mailbox : Pqxdh.Bytes) : OldPublic → Pqxdh.Bytes × Option NativePublic
  | ⟨.inl (.inl coin), reply⟩ => (mailbox, some ⟨.inl (.inl coin), reply⟩)
  | ⟨.inl (.inr (.create edPin keyId)), reply⟩ =>
      (mailbox, some ⟨.inl (.inr (.create edPin mailbox keyId)), reply⟩)
  | ⟨.inl (.inr (.bundle owner)), reply⟩ => (mailbox, some ⟨.inl (.inr (.bundle owner)), reply⟩)
  | ⟨.inl (.inr (.accept raw)), reply⟩ => (mailbox, some ⟨.inl (.inr (.accept raw)), reply⟩)
  | ⟨.inl (.inr (.build session payload)), reply⟩ => (mailbox, some ⟨.inl (.inr (.build session payload)), reply⟩)
  | ⟨.inl (.inr (.finish owner raw)), reply⟩ => (mailbox, some ⟨.inl (.inr (.finish owner raw)), reply⟩)
  | ⟨.inl (.inr (.hmac key message)), reply⟩ => match decode message with
      | some (.metadata mlPin) => (mlPin, none)
      | some (.hmac original) => (mailbox, some ⟨.inl (.inr (.hmac key original)), reply⟩)
      | none => (mailbox, none)
  | ⟨.inl (.inr (.hash bytes)), reply⟩ => (mailbox, some ⟨.inl (.inr (.hash bytes)), reply⟩)
  | ⟨.inl (.inr (.serverSend keyId plaintext)), reply⟩ => (mailbox, some ⟨.inl (.inr (.serverSend keyId plaintext)), reply⟩)
  | ⟨.inl (.inr (.serverRaw raw)), reply⟩ => (mailbox, some ⟨.inl (.inr (.serverRaw raw)), reply⟩)
  | ⟨.inl (.inr (.beaconSend owner plaintext)), reply⟩ => (mailbox, some ⟨.inl (.inr (.beaconSend owner plaintext)), reply⟩)
  | ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩ => (mailbox, some ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩)
  | ⟨.inr secrecy, reply⟩ => (mailbox, some ⟨.inr secrecy, reply⟩)

def restoreFrom (mailbox : Pqxdh.Bytes) : List OldPublic → Pqxdh.Bytes × List NativePublic
  | [] => (mailbox, [])
  | first :: rest =>
      let selected := restoreEntry mailbox first
      let later := restoreFrom selected.1 rest
      (later.1, selected.2.toList ++ later.2)

theorem entry_public (mailbox : Pqxdh.Bytes) (old : PqxdhDeploymentInterface.Entry) :
    restoreEntry mailbox (old.view .P) =
      let restored := RegistrationNativeEntropyRestore.entry mailbox old
      (restored.1, restored.2.map view) := by
  rcases old with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    rename_i key message
    cases decoded : decode message with
    | none => simp only [PqxdhDeploymentInterface.Entry.view, PqxdhDeploymentInterface.project,
        restoreEntry, RegistrationNativeEntropyRestore.entry, decoded, Option.map_none]
    | some transport =>
        cases transport
        all_goals simp only [PqxdhDeploymentInterface.Entry.view, PqxdhDeploymentInterface.project,
          restoreEntry, RegistrationNativeEntropyRestore.entry, decoded]
        all_goals rfl
  · rfl

theorem restore_public (mailbox : Pqxdh.Bytes) (transcript : List PqxdhDeploymentInterface.Entry) :
    restoreFrom mailbox (transcript.map (PqxdhDeploymentInterface.Entry.view .P)) =
      let restored := RegistrationNativeEntropyRestore.decodeFrom mailbox transcript
      (restored.1, restored.2.map view) := by
  induction transcript generalizing mailbox with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, restoreFrom, entry_public, RegistrationNativeEntropyRestore.decodeFrom]
      rw [ih]
      simp only [List.map_append, Option.toList_map]

def acceptPublic (session : Nat) : NativePublic → Option Pqxdh.Bytes
  | ⟨.inl (.inr (.accept raw)), some handle⟩ => if handle = session then some raw else none
  | _ => none

def parsedPublic (wire : RegistrationNativeWire.Wire) (entry : NativePublic) : Bool :=
  match entry.1 with
  | .inl (.inr (.accept raw)) => (RegistrationNativeWire.readInit wire raw).isSome
  | _ => false

def firstFrom (wire : RegistrationNativeWire.Wire) (session parsed : Nat) : List NativePublic → Option (Nat × Pqxdh.Bytes)
  | [] => none
  | first :: rest => match acceptPublic session first with
      | some raw => some (parsed, raw)
      | none => firstFrom wire session (parsed + if parsedPublic wire first then 1 else 0) rest

def firstAccept (wire : RegistrationNativeWire.Wire) (session : Nat) : List NativePublic → Option (Nat × Pqxdh.Bytes) :=
  firstFrom wire session 0

theorem first_payload (wire : RegistrationNativeWire.Wire) (session parsed : Nat) (transcript : List NativePublic) :
    (firstFrom wire session parsed transcript).map Prod.snd = transcript.findSome? (acceptPublic session) := by
  induction transcript generalizing parsed with
  | nil => rfl
  | cons first rest ih =>
      cases accepted : acceptPublic session first
      all_goals simp only [firstFrom, accepted, List.findSome?_cons, Option.map_some, ih]

theorem acceptOf_public (session : Nat) (transcript : List RegistrationNativeInterface.Entry) :
    (transcript.map view).findSome? (acceptPublic session) =
      PqxdhDeploymentTranscript.acceptOf (transcript.map RegistrationNativeInterface.Entry.erase) session := by
  simp only [List.findSome?_map, PqxdhDeploymentTranscript.acceptOf]
  apply congrArg (fun observe => transcript.findSome? observe)
  funext entry
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    cases reply <;> rfl
  · rfl

/-- The native mode-P transcript in the actual restored ledger is a finite function of the original mode-P transcript. -/
theorem ledger_public (before : PqxdhDeploymentSecrecy.Ledger) :
    (RegistrationNativeEntropyRestore.ledger before).transcript.map view =
      (restoreFrom [] (before.transcript.map (PqxdhDeploymentInterface.Entry.view .P))).2 := by
  exact (congrArg Prod.snd (restore_public [] before.transcript)).symm

/-- The scanner returns the same first successful session input as the original acceptance lookup. -/
theorem first_acceptOf (wire : RegistrationNativeWire.Wire) (session : Nat)
    (transcript : List RegistrationNativeInterface.Entry) :
    (firstAccept wire session (transcript.map view)).map Prod.snd =
      PqxdhDeploymentTranscript.acceptOf (transcript.map RegistrationNativeInterface.Entry.erase) session := by
  exact (first_payload wire session 0 (transcript.map view)).trans (acceptOf_public session transcript)

/-- Restoring two transcripts with the same original mode-P view gives the same functional parsed-accept selector. -/
theorem restored_first_public (wire : RegistrationNativeWire.Wire) (session : Nat)
    (first second : PqxdhDeploymentSecrecy.Ledger)
    (same : first.transcript.map (PqxdhDeploymentInterface.Entry.view .P) =
      second.transcript.map (PqxdhDeploymentInterface.Entry.view .P)) :
    firstAccept wire session ((RegistrationNativeEntropyRestore.ledger first).transcript.map view) =
      firstAccept wire session ((RegistrationNativeEntropyRestore.ledger second).transcript.map view) := by
  rw [ledger_public, ledger_public, same]

end BeaconcryptCore.Computational.RegistrationNativePublicObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.entry_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.entry_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.restore_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.restore_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.first_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.first_payload
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.acceptOf_public' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.acceptOf_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.ledger_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.ledger_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.first_acceptOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.first_acceptOf
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicObservation.restored_first_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicObservation.restored_first_public
