-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectedEvents
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! A broad native designation retains its successful session handle while selecting the parsed accept attempt that actually returned it. The parsed ordinal counts decodable failed attempts as well. The witness keeps the complete original native accept entry and its prefix; it imposes no equality with an earlier bundle and no membership condition on the incoming ML key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTarget
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open RegistrationNativeEvents (parsedAccept parsedAcceptCount)
open PqxdhDeploymentInterface (Handle Budget)

/-- The original successful session remains separate from the selected parsed-call ordinal. -/
def AcceptedAt (wire : Wire) (transcript : List Entry) (session parsed : Nat) : Prop :=
  ∃ before raw packet after,
    transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after ∧
    parsedAcceptCount wire before = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet

/-- The first coordinate selects an actual parsed call, while the session in the original designation remains existential. -/
def DesignatedAt (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (transcript : List Entry) (target : Fin budget.accept × Fin budget.capacity) (handle : Handle) : Prop :=
  ∃ session : Fin budget.accept,
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget (transcript.map Entry.erase) handle = some (session, target.2) ∧
    AcceptedAt wire transcript session.val target.1.val

private theorem erase_accept (entry : Entry) (raw : Pqxdh.Bytes) (session : Nat)
    (equal : entry.erase = (⟨.inl (.inr (.accept raw)), some session⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = ⟨.inl (.inr (.accept raw)), some session⟩ := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases equal
  · cases command <;> cases equal
    rfl
  · cases equal

/-- The native reader used by public designation is the actual bounded six-field Init reader. -/
theorem candidate_parsed (wire : Wire) (raw : Pqxdh.Bytes)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (found : PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate) :
    ∃ packet, RegistrationNativeWire.readInit wire raw = some packet := by
  cases parsed : RegistrationNativeWire.readInit wire raw with
  | none =>
      simp [PqxdhDeploymentTranscript.candidateOf, PqxdhRegistrationJointRawSignatures.candidate,
        RegistrationNativeWire.ledgerCodec, parsed] at found
  | some packet => exact ⟨packet, rfl⟩

/-- Both Server and Beacon designation identify the original successful native accept entry and its exact parsed prefix. -/
theorem designated_accept (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64)
    (budget : Budget) (transcript : List Entry) (handle : Handle)
    (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget (transcript.map Entry.erase) handle = some target) :
    ∃ parsed, AcceptedAt wire transcript target.1.val parsed := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some crypto _ serverKeyId budget _ handle target designated
  obtain ⟨raw, candidate, _, _, accepted, read, _⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys crypto _ serverKeyId _ handle target.1.val target.2.val plain
  obtain ⟨packet, parsed⟩ := candidate_parsed wire raw candidate read
  have member := PqxdhDeploymentKemTransfer.acceptOf_mem _ target.1.val raw accepted
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  have same := erase_accept entry raw target.1.val erased
  subst entry
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp nativeMember
  exact ⟨parsedAcceptCount wire before, before, raw, packet, after, split, rfl, parsed⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedTarget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTarget.candidate_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTarget.candidate_parsed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTarget.designated_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTarget.designated_accept
