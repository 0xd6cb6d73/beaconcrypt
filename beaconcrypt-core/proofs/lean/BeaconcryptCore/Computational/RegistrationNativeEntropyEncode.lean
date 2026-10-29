-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation

/-! The exact compiler image of a complete native analysis transcript. Creation emits its public metadata marker followed by the original create reply; HMAC transport retains the original primitive reply. The original private test and fresh states are copied verbatim. These encodings are proof maps and are never available to the environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyEncode
open RegistrationNativeEntropyInterface (metadata userHmac)
open RegistrationNativeEntropyTrace (strip stripEntry)
open PqxdhSecretInputKdf (zeroSalt)
abbrev NativeEntry := RegistrationNativeInterface.Entry
abbrev OldEntry := PqxdhDeploymentInterface.Entry

def entry : NativeEntry → List OldEntry
  | ⟨.inl (.inr (.create edPin mlPin keyId)), reply⟩ =>
      [⟨.inl (.inr (.hmac zeroSalt (metadata mlPin))), zeroSalt⟩,
       ⟨.inl (.inr (.create edPin keyId)), reply⟩]
  | ⟨.inl (.inr (.hmac key message)), reply⟩ =>
      [⟨.inl (.inr (.hmac key (userHmac message))), reply⟩]
  | native => [native.erase]

def transcript (native : List NativeEntry) : List OldEntry := native.flatMap entry

def pin (before : Pqxdh.Bytes) : NativeEntry → Pqxdh.Bytes
  | ⟨.inl (.inr (.create _ mlPin _)), _⟩ => mlPin
  | _ => before

def mailbox (native : List NativeEntry) : Pqxdh.Bytes := native.foldl pin []

def ledger (native : RegistrationNativeLedger.State) : PqxdhDeploymentSecrecy.Ledger :=
  { native.ledger with transcript := transcript native.transcript }

/-- One native entry decodes exactly, with the latest creation pin as the only mailbox change. -/
theorem entry_decode (before : Pqxdh.Bytes) (native : NativeEntry) :
    RegistrationNativeEntropyRestore.decodeFrom before (entry native) = (pin before native, [native]) := by
  rcases native with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
  · rfl

/-- Each encoded entry erases only its native ML creation pin. -/
theorem entry_strip (native : NativeEntry) : strip (entry native) = [native.erase] := by
  have decoded := RegistrationNativeEntropyRestore.from_erase [] (entry native)
  rw [entry_decode] at decoded
  exact decoded.symm

/-- Transcript concatenation preserves complete native command ordering. -/
theorem transcript_append (first second : List NativeEntry) :
    transcript (first ++ second) = transcript first ++ transcript second := List.flatMap_append

/-- The transport image erases to the exact original native transcript projection. -/
theorem transcript_strip (native : List NativeEntry) :
    strip (transcript native) = native.map RegistrationNativeInterface.Entry.erase := by
  induction native with
  | nil => rfl
  | cons first rest ih =>
      simp only [transcript, List.flatMap_cons, RegistrationNativeEntropyTrace.strip_append,
        entry_strip, List.map_cons] at *
      exact congrArg (List.cons first.erase) ih

/-- Complete decoding recovers every public ML pin, raw reply and original entry from the actual compiler image. -/
theorem transcript_decode (before : Pqxdh.Bytes) (native : List NativeEntry) :
    RegistrationNativeEntropyRestore.decodeFrom before (transcript native) =
      (native.foldl pin before, native) := by
  induction native generalizing before with
  | nil => rfl
  | cons first rest ih =>
      simp only [transcript] at ih
      simp only [transcript, List.flatMap_cons, RegistrationNativeEntropyRestore.from_append,
        entry_decode, ih, List.foldl_cons, List.singleton_append]

/-- The reconstructed ledger equals the actual native ledger whenever its derived transcript invariant holds. -/
theorem ledger_restore (native : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent native) :
    RegistrationNativeEntropyRestore.ledger (ledger native) = native := by
  cases native with
  | mk old complete =>
      cases old with
      | mk original test fresh =>
          change original = complete.map RegistrationNativeInterface.Entry.erase at consistent
          subst original
          simp only [ledger, RegistrationNativeEntropyRestore.ledger, transcript_decode]

/-- The original secrecy designation is unchanged on the exact native compiler image. -/
theorem designate (crypto : Pqxdh.Crypto) {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (native : RegistrationNativeLedger.State) (consistent : RegistrationNativeLedger.Consistent native) :
    PqxdhDeploymentTranscript.designate crypto codec serverKid (ledger native).transcript =
      PqxdhDeploymentTranscript.designate crypto codec serverKid native.ledger.transcript := by
  have decoded := RegistrationNativeEntropyDesignation.designate_strip crypto codec serverKid
    (transcript native.transcript)
  rw [transcript_strip, ← consistent] at decoded
  exact decoded.symm

end BeaconcryptCore.Computational.RegistrationNativeEntropyEncode

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.entry_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.entry_decode
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.entry_strip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.entry_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_strip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_strip
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.transcript_decode
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.ledger_restore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.ledger_restore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.designate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyEncode.designate
