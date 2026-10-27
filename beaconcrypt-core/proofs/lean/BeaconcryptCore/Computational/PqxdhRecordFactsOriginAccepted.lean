-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished

/-! Actual successful raw receives retain the same optional plaintext and a source-oriented ideal dictionary witness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsOriginReceive PqxdhRecordFactsOriginPublished
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The actual plaintext reply is caller-known or matches a seal at this receiver's installed slot and opposite physical direction. -/
def Accepted (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) : Prop :=
  PqxdhRecordLiftFlat.KnownAt control handle ∨
    ∃ label, handleSlot control handle = some label.slot ∧ label.direction = !handleDirection handle ∧
      ∃ frame, codec.frameRead raw = some frame ∧
      ∃ entry ∈ (secret.keys label).1.successfulSeals, Matches frame entry ∧ entry.input.plaintext = opened.plaintext

/-- Every successful actual owner receive is classified from its selected source storage without assuming that selection hidden or honest. -/
theorem ownerReceive_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control result.2 handle raw opened := by
  cases storedKind : owner.kernel with
  | known kernel =>
    exact Or.inl (known_of_handleKernel control handle kernel (by simpa only [storedKind] using stored))
  | hidden slot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
    repeat' split at supported
    case h_2.isTrue =>
      simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      obtain ⟨kept, label, labelSlot, direction, decoded, parsed, old, member, matched, plaintext⟩ :=
        kernel_receive_origin modes ideal replace setup codec (handleRole handle) slot entry
          (handleKernel_oriented control safe handle _ (by simpa only [storedKind] using stored))
          _ _ before inner reached opened returned
      refine Or.inr ⟨label, ?_, ?_, decoded, parsed, old, ?_, matched, plaintext⟩
      · simpa only [labelSlot] using handleKernel_slot control handle slot entry (by simpa only [storedKind] using stored)
      · simpa only [handleRole_direction] using direction
      · simpa only [kept.seals] using member
    all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals simp only [supported, reduceCtorEq] at returned

/-- The complete actual raw owner command keeps the same successful plaintext witness through its publication callback. -/
theorem ownerRun_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun (some handle) sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control result.2 handle raw opened := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerReceive_accepted modes ideal replace setup codec control safe handle owner stored
    raw before received receiveSupported opened returned

/-- A caller-known installed handle has no hidden installation slot in the public ideal view. -/
theorem known_no_slot (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (known : PqxdhRecordLiftFlat.KnownAt control handle) : handleSlot control handle = none := by
  cases handle with
  | peer keyId =>
    obtain ⟨server, peer, kernel, existing, found, stored⟩ := known
    simp only [handleSlot, peerSlot, existing, Option.bind_some, found, stored, StoredKernel.origin]
  | owner index =>
    obtain ⟨shell, kernel, found⟩ := known
    simp only [handleSlot, ownerSlot, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.Phase.origin, StoredKernel.origin]

/-- Two decoded frames matching one actual seal entry have identical sequence, sender and complete payload. -/
theorem matches_unique (first second : RawCtxReceive.DecodedFrame) (entry : CtxSuccessfulSeal)
    (left : Matches first entry) (right : Matches second entry) : first = second := by
  have sequenceEq : first.sequence = second.sequence := UScalar.eq_of_val_eq (left.1.trans right.1.symm)
  have senderEq : first.sender = second.sender := UScalar.eq_of_val_eq (left.2.1.trans right.2.1.symm)
  cases first; cases second; simp_all only [Matches]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.ownerReceive_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.ownerReceive_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.ownerRun_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.ownerRun_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.known_no_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.known_no_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.matches_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted.matches_unique
