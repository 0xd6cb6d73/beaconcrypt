-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend

/-! Dictionary provenance under the actual dynamic source record dispatcher. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginBuffers PqxdhRecordFactsOriginSend
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReceive
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (FrameTag Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Caller-known receives preserve every already attributed hidden dictionary entry. -/
theorem knownReceive_closed (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (before : CtxPrivate n) (closed : Closed claims before)
    (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownReceive kernel target context)).run before)) :
    Closed claims result.2 := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact closed

/-- Every actual kernel receive retains the already attributed ideal dictionaries. -/
theorem kernelReceive_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (before : CtxPrivate n) (closed : Closed claims before)
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context)).run before)) :
    Closed claims result.2 := by
  cases stored with
  | known kernel =>
    simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact knownReceive_closed modes replace setup codec claims before closed kernel target context inner reached
  | hidden slot kernel =>
    simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have kept := receive_retained modes ideal replace setup codec
      (RawCtxChainReceive.normalBegin kernel target context) before inner reached
    intro label entry member
    rw [kept.seals label] at member
    simpa only [kept.produced] using closed label entry member

/-- Parser refusals and the complete owner receive preserve existing dictionary attribution. -/
theorem ownerReceive_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (before : CtxPrivate n) (closed : Closed claims before)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (raw : Pqxdh.Bytes)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before)) :
    Closed claims result.2 := by
  simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact kernelReceive_closed modes ideal replace setup codec claims before closed owner.kernel _ _ inner reached
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact closed

/-- The complete source owner-receive command preserves dictionary attribution and empties its writer buffer. -/
theorem ownerRun_receive_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed claims before)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before)) :
    Closed claims result.2 ∧ result.2.base.pending = [] := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  exact publish_buffered_closed modes replace setup codec claims tag received.2
    (closed_buffered claims tag received.2
      (ownerReceive_closed modes ideal replace setup codec claims before closed owner raw received receiveSupported))
    published publishSupported

/-- The literal Server send dispatcher retains dictionary provenance, including absent peers and failing writers. -/
theorem serverSend_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (plaintext : Pqxdh.Bytes) (keyId : Std.U64)
    (before : CtxPrivate n) (closed : Closed (Claims control) before) (empty : before.base.pending = [])
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before)) :
    Closed (Claims result.1.2) result.2 ∧ result.2.base.pending = [] := by
  have progress := PqxdhRecordLiftProtocolHistory.server_step codec.frameRead route (.inl (plaintext, keyId)) control safe result.1
    (PqxdhRecordLiftFlat.support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported)
  have prior : Closed (Claims control) result.2 ∧ result.2.base.pending = [] := by
    cases existing : control.server with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨closed, empty⟩
    | some server =>
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨closed, empty⟩
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        apply ownerRun_send_closed modes ideal replace setup codec control safe (.peer keyId)
          (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ server.sender plaintext
          before closed inner reached
        simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
          PqxdhRecordLiftWorldCompiler.serverOwner]
  exact ⟨closed_claims_mono (Claims control) (Claims result.1.2)
    (claims_step control result.1.2 progress) result.2 prior.1, prior.2⟩

/-- The literal Beacon send dispatcher retains dictionary provenance through absent, inactive and established owners. -/
theorem beaconSend_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed (Claims control) before) (empty : before.base.pending = [])
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before)) :
    Closed (Claims result.1.2) result.2 ∧ result.2.base.pending = [] := by
  have progress := PqxdhRecordLiftProtocolHistory.beacon_step codec.frameRead owner (.inl plaintext) control safe result.1
    (PqxdhRecordLiftFlat.support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported)
  have prior : Closed (Claims control) result.2 ∧ result.2.base.pending = [] := by
    cases found : control.owners[owner]? with
    | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨closed, empty⟩
    | some phase =>
      cases phase with
      | inactive phase =>
        simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨closed, empty⟩
      | established shell kernel =>
        simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        apply ownerRun_send_closed modes ideal replace setup codec control safe (.owner owner)
          (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner)) _ shell.identityKeyId plaintext
          before closed inner reached
        simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]
  exact ⟨closed_claims_mono (Claims control) (Claims result.1.2)
    (claims_step control result.1.2 progress) result.2 prior.1, prior.2⟩

/-- The actual routed Server receive preserves dictionary attribution on every missing-peer and selected-peer path. -/
theorem serverReceive_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (raw : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed (Claims control) before) (empty : before.base.pending = [])
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before)) :
    Closed (Claims result.1.2) result.2 ∧ result.2.base.pending = [] := by
  have progress := PqxdhRecordLiftProtocolHistory.server_step codec.frameRead route (.inr raw) control safe result.1
    (PqxdhRecordLiftFlat.support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported)
  have prior : Closed (Claims control) result.2 ∧ result.2.base.pending = [] := by
    cases existing : control.server with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨closed, empty⟩
    | some server =>
      cases routed : route raw with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨closed, empty⟩
      | some keyId =>
        cases found : server.peers keyId with
        | none =>
          simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact ⟨closed, empty⟩
        | some peer =>
          simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
            simulateQ_map, StateT.run_map, support_map] at supported
          obtain ⟨inner, reached, rfl⟩ := supported
          exact ownerRun_receive_closed modes ideal replace setup codec (Claims control) _
            (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) server.sender raw
            before closed inner reached
  exact ⟨closed_claims_mono (Claims control) (Claims result.1.2)
    (claims_step control result.1.2 progress) result.2 prior.1, prior.2⟩

/-- The actual Beacon receive preserves dictionary attribution for absent, inactive and established owners. -/
theorem beaconReceive_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (raw : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed (Claims control) before) (empty : before.base.pending = [])
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before)) :
    Closed (Claims result.1.2) result.2 ∧ result.2.base.pending = [] := by
  have progress := PqxdhRecordLiftProtocolHistory.beacon_step codec.frameRead owner (.inr raw) control safe result.1
    (PqxdhRecordLiftFlat.support_run_fst (ctxInterpreter modes replace setup codec) _ before result supported)
  have prior : Closed (Claims control) result.2 ∧ result.2.base.pending = [] := by
    cases found : control.owners[owner]? with
    | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨closed, empty⟩
    | some phase =>
      cases phase with
      | inactive phase =>
        simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨closed, empty⟩
      | established shell kernel =>
        simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact ownerRun_receive_closed modes ideal replace setup codec (Claims control) _
          (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner)) shell.identityKeyId raw
          before closed inner reached
  exact ⟨closed_claims_mono (Claims control) (Claims result.1.2)
    (claims_step control result.1.2 progress) result.2 prior.1, prior.2⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.knownReceive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.knownReceive_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.kernelReceive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.kernelReceive_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.ownerReceive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.ownerReceive_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.ownerRun_receive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.ownerRun_receive_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.serverSend_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.serverSend_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.beaconSend_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.beaconSend_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.serverReceive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.serverReceive_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.beaconReceive_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginWorld.beaconReceive_closed
