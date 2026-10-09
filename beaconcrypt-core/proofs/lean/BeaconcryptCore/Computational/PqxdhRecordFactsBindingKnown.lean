-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence

/-! Actual caller-known owner and dispatcher commitment witnesses. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsBindingEvidence PqxdhRecordFactsOriginHandles
open PqxdhRecordLiftWorldCompiler (Label StoredKernel Owner)
open PqxdhDeploymentInterface (Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The literal external record bytes decode to a commitment already present in the actual shared ROM. -/
def SharedRecord (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (secret : CtxPrivate n) (raw : Pqxdh.Bytes) : Prop :=
  ∃ frame, codec.frameRead raw = some frame ∧ SharedCommit frame secret.base.primitive.2

/-- Every later shared-cache extension preserves the same raw-byte witness. -/
theorem SharedRecord.grows (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (before after : CtxPrivate n) (raw : Pqxdh.Bytes)
    (cache : before.base.primitive.2 ≤ after.base.primitive.2) (witness : SharedRecord codec before raw) :
    SharedRecord codec after raw := by
  obtain ⟨frame, decoded, cached⟩ := witness
  exact ⟨frame, decoded, SharedCommit.grows frame _ _ cache cached⟩

/-- A successful actual owner send using caller-known storage has a shared-ROM commitment witness for its returned bytes. -/
theorem ownerSend_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (owner : Owner n) (kernel : ConcreteRatchetKernel) (known : owner.kernel = .known kernel)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    SharedRecord codec result.2 encrypted.ciphertext := by
  simp only [PqxdhRecordLiftProtocol.ownerSend] at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.kernelSend, known, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact known_send_cached modes replace setup codec readBack kernel _ before inner reached encrypted returned

/-- An actual successful caller-known owner receive identifies the accepted raw frame's shared-ROM commitment. -/
theorem ownerReceive_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Owner n) (kernel : ConcreteRatchetKernel) (known : owner.kernel = .known kernel)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    SharedRecord codec result.2 raw := by
  simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [PqxdhRecordLiftProtocol.kernelReceive, known, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    rename_i notEmpty value frame decoded valid
    exact ⟨frame, decoded, known_receive_cached modes replace setup codec kernel frame.sequence
      ⟨raw, frame, owner.associatedData⟩ before inner reached opened returned⟩
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals simp only [supported, reduceCtorEq] at returned

/-- A known owner's successful send commitment survives the actual publication callback with its literal tag. -/
theorem ownerRun_send_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (owner : Owner n) (kernel : ConcreteRatchetKernel) (known : owner.kernel = .known kernel)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n) (result : (Option RawCtxSourceSend.Encrypted × Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inl plaintext) owner)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    SharedRecord codec result.2 encrypted.ciphertext := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerSend_shared modes replace setup codec readBack owner kernel known sender plaintext before sent sendSupported encrypted returned

/-- A known owner's successful raw receive commitment survives publication, including the absent Server receive tag. -/
theorem ownerRun_receive_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Owner n) (kernel : ConcreteRatchetKernel) (known : owner.kernel = .known kernel)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    SharedRecord codec result.2 raw := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerReceive_shared modes replace setup codec owner kernel known raw before received receiveSupported opened returned

/-- Successful actual Server sends from a caller-known peer retain the commitment of the returned ciphertext. -/
theorem serverSend_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (keyId : Std.U64)
    (known : PqxdhRecordLiftFlat.KnownAt control (.peer keyId))
    (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    SharedRecord codec result.2 encrypted.ciphertext := by
  obtain ⟨server, peer, kernel, existing, found, stored⟩ := known
  simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
    simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ownerRun_send_shared modes replace setup codec readBack
    (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) kernel stored _ server.sender plaintext
    before inner reached encrypted returned

/-- Successful actual Beacon sends from a caller-known owner retain the commitment of the returned ciphertext. -/
theorem beaconSend_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (known : PqxdhRecordLiftFlat.KnownAt control (.owner owner))
    (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    SharedRecord codec result.2 encrypted.ciphertext := by
  obtain ⟨shell, kernel, found⟩ := known
  simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
    simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ownerRun_send_shared modes replace setup codec readBack
    (PqxdhRecordLiftWorldCompiler.beaconOwner shell (.known kernel) (control.ownerRaw owner)) kernel rfl
    _ shell.identityKeyId plaintext before inner reached encrypted returned

/-- Successful actual Beacon receives at a caller-known owner retain the exact accepted raw commitment. -/
theorem beaconReceive_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (known : PqxdhRecordLiftFlat.KnownAt control (.owner owner))
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    SharedRecord codec result.2 raw := by
  obtain ⟨shell, kernel, found⟩ := known
  simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
    simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ownerRun_receive_shared modes replace setup codec
    (PqxdhRecordLiftWorldCompiler.beaconOwner shell (.known kernel) (control.ownerRaw owner)) kernel rfl
    _ shell.identityKeyId raw before inner reached opened returned

/-- Successful actual Server receives at the routed caller-known peer retain the exact accepted raw commitment. -/
theorem serverReceive_shared (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (raw : Pqxdh.Bytes) (handle : Handle)
    (routed : receivingHandle route .server raw = some handle)
    (known : PqxdhRecordLiftFlat.KnownAt control handle) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    SharedRecord codec result.2 raw := by
  cases header : route raw with
  | none => simp only [receivingHandle, header, Option.map_none, reduceCtorEq] at routed
  | some keyId =>
    simp only [receivingHandle, header, Option.map_some, Option.some.injEq] at routed
    subst handle
    obtain ⟨server, peer, kernel, existing, found, stored⟩ := known
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, header, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ownerRun_receive_shared modes replace setup codec
      (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) kernel stored _ server.sender raw
      before inner reached opened returned

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.SharedRecord.grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.SharedRecord.grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerSend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerSend_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerReceive_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerReceive_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerRun_send_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerRun_send_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerRun_receive_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.ownerRun_receive_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.serverSend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.serverSend_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.beaconSend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.beaconSend_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.beaconReceive_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.beaconReceive_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.serverReceive_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnown.serverReceive_shared
