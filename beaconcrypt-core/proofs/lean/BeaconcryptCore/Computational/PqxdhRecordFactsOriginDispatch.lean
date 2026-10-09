-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted

/-! Exact source record dispatch preserves the selected physical handle and actual record witnesses. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsOriginPublished PqxdhRecordFactsOriginAccepted
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The receive witness survives the actual publication tag, which may be absent on a routed Server receive. -/
theorem ownerRun_accepted_tag (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (tag : PqxdhDeploymentInterface.FrameTag)
    (sender : Std.U64) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
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

/-- Every successful routed Server receive identifies its actual selected peer and exact source receive witness. -/
theorem serverReceive_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    ∃ handle, receivingHandle route .server raw = some handle ∧ Accepted codec control result.2 handle raw opened := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | some server =>
    cases routed : route raw with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    | some keyId =>
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        simp only [supported, reduceCtorEq] at returned
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        refine ⟨.peer keyId, by simp only [receivingHandle, routed, Option.map_some], ?_⟩
        apply ownerRun_accepted_tag modes ideal replace setup codec control safe (.peer keyId)
          (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ _ server.sender raw
          before inner reached opened returned
        simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
          PqxdhRecordLiftWorldCompiler.serverOwner]


/-- Every successful Beacon receive retains its actual owner handle and source receive witness. -/
theorem beaconReceive_accepted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened) :
    Accepted codec control result.2 (.owner owner) raw opened := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_accepted_tag modes ideal replace setup codec control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ _ shell.identityKeyId raw before inner reached opened returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- Every returned Server ciphertext is attributed to the requested peer's actual source sender. -/
theorem serverSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    Published codec control result.2 (.peer keyId) encrypted := by
  rcases existing : control.server with _ | server
  · simp_all only [PqxdhRecordLiftProtocol.serverStep, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · rcases found : server.peers keyId with _ | peer
    · simp_all only [PqxdhRecordLiftProtocol.serverStep, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, reduceCtorEq]
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply ownerRun_published modes ideal replace setup codec readback control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ server.sender plaintext
        before inner reached encrypted returned
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Every returned Beacon ciphertext is attributed to the requested owner's actual source sender. -/
theorem beaconSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    Published codec control result.2 (.owner owner) encrypted := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp_all only [PqxdhRecordLiftProtocol.beaconStep, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · simp_all only [PqxdhRecordLiftProtocol.beaconStep, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_published modes ideal replace setup codec readback control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ shell.identityKeyId plaintext before inner reached encrypted returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.ownerRun_accepted_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.ownerRun_accepted_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.serverReceive_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.serverReceive_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.beaconReceive_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.beaconReceive_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.serverSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.serverSend_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.beaconSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch.beaconSend_published

