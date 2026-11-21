-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep

/-! Actual send dispatch and receive preservation for temporal publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReceive PqxdhRecordFactsOriginPublicationStep
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle Entry)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every new Server-send seal names its actual requested peer and literal writer outcome. -/
theorem serverSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label (.peer keyId) ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  rcases existing : control.server with _ | server
  · simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · rcases found : server.peers keyId with _ | peer
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Or.inl member
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply ownerRun_entry modes ideal replace setup codec readback control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ server.sender plaintext
        before inner reached label entry member
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- Every new Beacon-send seal names its actual requested owner and literal writer outcome. -/
theorem beaconSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (owner : Nat) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label (.owner owner) ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, PqxdhDeploymentNative.absent, found,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_entry modes ideal replace setup codec readback control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ shell.identityKeyId plaintext before inner reached label entry member
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- A complete kernel receive keeps every hidden seal dictionary unchanged. -/
theorem kernelReceive_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before : CtxPrivate n)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  cases stored with
  | known kernel =>
    simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
      support_map] at reached
    obtain ⟨native, nativeReached, rfl⟩ := reached
    exact fun _ => rfl
  | hidden slot kernel =>
    simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, simulateQ_map,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact (receive_retained modes ideal replace setup codec
      (RawCtxChainReceive.normalBegin kernel target context) before inner reached).seals

/-- Every actual owner receive retains the pre-query seal dictionaries, including parser and validation rejection. -/
theorem ownerReceive_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact kernelReceive_seals modes ideal replace setup codec owner.kernel _ _ before inner reached
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact fun _ => rfl

/-- The actual owner receive and optional publication tag preserve every pre-query seal dictionary. -/
theorem ownerRun_receive_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (sender : Std.U64) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerReceive_seals modes ideal replace setup codec owner raw before received receiveSupported

/-- The raw Server dispatcher preserves every dictionary through absent routing, selection and actual receive. -/
theorem serverReceive_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact fun _ => rfl
  | some server =>
    cases routed : route raw with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact fun _ => rfl
    | some keyId =>
      cases found : server.peers keyId with
      | none =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact fun _ => rfl
      | some peer =>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
          simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact ownerRun_receive_seals modes ideal replace setup codec _
          (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) server.sender raw before inner reached

/-- The raw Beacon dispatcher preserves every dictionary, including absent and unestablished owners. -/
theorem beaconReceive_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat) (raw : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inr raw) control)).run before)) :
    ∀ label, (result.2.keys label).1.successfulSeals = (before.keys label).1.successfulSeals := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, PqxdhDeploymentNative.absent, found,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact fun _ => rfl
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact fun _ => rfl
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact ownerRun_receive_seals modes ideal replace setup codec _
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      shell.identityKeyId raw before inner reached

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.serverSend_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.serverSend_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.beaconSend_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.beaconSend_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.kernelReceive_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.kernelReceive_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.ownerReceive_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.ownerReceive_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.ownerRun_receive_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.ownerRun_receive_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.serverReceive_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.serverReceive_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.beaconReceive_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch.beaconReceive_seals
