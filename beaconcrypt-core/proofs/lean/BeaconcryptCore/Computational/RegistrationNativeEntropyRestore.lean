-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyTrace
import BeaconcryptCore.Computational.RegistrationNativeLedger

/-! Reconstruct the complete native Mode O analysis transcript from the old transport transcript. The latest public ML pin is attached to each literal create entry, user HMAC messages are restored, and every original raw plaintext reply remains private and unchanged. The original hidden test/fresh state is retained verbatim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyRestore
open RegistrationNativeEntropyInterface (decode metadata userHmac)
open RegistrationNativeEntropyTrace (strip stripEntry)
abbrev OldEntry := PqxdhDeploymentInterface.Entry
abbrev NativeEntry := RegistrationNativeInterface.Entry

def entry (mailbox : Pqxdh.Bytes) : OldEntry → Pqxdh.Bytes × Option NativeEntry
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

def decodeFrom (mailbox : Pqxdh.Bytes) : List OldEntry → Pqxdh.Bytes × List NativeEntry
  | [] => (mailbox, [])
  | first :: rest =>
      let selected := entry mailbox first
      let later := decodeFrom selected.1 rest
      (later.1, selected.2.toList ++ later.2)

def ledger (before : PqxdhDeploymentSecrecy.Ledger) : RegistrationNativeLedger.State :=
  let decoded := decodeFrom [] before.transcript
  ⟨{ before with transcript := decoded.2.map RegistrationNativeInterface.Entry.erase }, decoded.2⟩

/-- The metadata marker changes only the latest public pin and emits no native entry. -/
theorem entry_metadata (before mlPin : Pqxdh.Bytes) (key reply : PqxdhSecretInputKdf.HmacBlock) :
    entry before ⟨.inl (.inr (.hmac key (metadata mlPin))), reply⟩ = (mlPin, none) := by
  simp only [entry, RegistrationNativeEntropyInterface.decode_metadata]

/-- User HMAC calls restore the exact original message and retain the full actual primitive reply. -/
theorem entry_hmac (before message : Pqxdh.Bytes) (key reply : PqxdhSecretInputKdf.HmacBlock) :
    entry before ⟨.inl (.inr (.hmac key (userHmac message))), reply⟩ =
      (before, some ⟨.inl (.inr (.hmac key message)), reply⟩) := by
  simp only [entry, RegistrationNativeEntropyInterface.decode_userHmac]

/-- Erasing only the additional ML pin gives the exact transport-stripped original entry. -/
theorem entry_erase (before : Pqxdh.Bytes) (old : OldEntry) :
    (entry before old).2.map RegistrationNativeInterface.Entry.erase = stripEntry old := by
  rcases old with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    rename_i key message
    cases decoded : decode message with
    | none => simp only [entry, stripEntry, decoded, Option.map_none]
    | some transport => cases transport <;> simp only [entry, stripEntry, decoded] <;> rfl
  · rfl

/-- Decoding adaptive transcript segments threads the latest mailbox and preserves complete native entry ordering. -/
theorem from_append (before : Pqxdh.Bytes) (first second : List OldEntry) :
    decodeFrom before (first ++ second) =
      let left := decodeFrom before first
      let right := decodeFrom left.1 second
      (right.1, left.2 ++ right.2) := by
  induction first generalizing before with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append, decodeFrom, ih, List.append_assoc]

/-- The complete original transcript is retained after stripping only adapter metadata and HMAC transport tags. -/
theorem from_erase (before : Pqxdh.Bytes) (transcript : List OldEntry) :
    (decodeFrom before transcript).2.map RegistrationNativeInterface.Entry.erase = strip transcript := by
  induction transcript generalizing before with
  | nil => rfl
  | cons first rest ih =>
      have one := congrArg Option.toList (entry_erase before first)
      rw [Option.toList_map] at one
      simp only [decodeFrom, List.map_append, ih]
      rw [one]
      cases found : stripEntry first <;> simp only [strip, List.filterMap_cons, found,
        Option.toList, List.nil_append, List.cons_append]

/-- Restored native ledgers satisfy the same exact original-transcript projection invariant as the actual native source. -/
theorem ledger_consistent (before : PqxdhDeploymentSecrecy.Ledger) :
    RegistrationNativeLedger.Consistent (ledger before) := rfl

/-- Private tests and fresh-message draws are not resampled, decoded or discarded by this adapter. -/
theorem ledger_secrets (before : PqxdhDeploymentSecrecy.Ledger) :
    (ledger before).ledger.test = before.test ∧ (ledger before).ledger.fresh = before.fresh := ⟨rfl, rfl⟩

/-- The restored original ledger has the literal transport-decoded transcript. -/
theorem ledger_transcript (before : PqxdhDeploymentSecrecy.Ledger) :
    (ledger before).ledger.transcript = strip before.transcript := from_erase [] before.transcript

end BeaconcryptCore.Computational.RegistrationNativeEntropyRestore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_metadata' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_hmac' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_hmac
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.entry_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.from_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.from_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.from_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.from_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_consistent' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_secrets' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_secrets
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_transcript' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRestore.ledger_transcript
