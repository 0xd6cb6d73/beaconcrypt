-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconChargedReceive
import BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram
/-! The actual Beacon record controller retains its initial marker and its conditional ongoing marker. Source KDF operands are private; their public accounting operations are independent of those operands. Hash and opening callbacks remain arbitrary stateful operations in the same monad. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconChargedSource
open RegistrationBeaconBoundSource (PublicAgreement atRoot frame context observe)
open PqxdhSecretInputKdf (RootOutput)
open RawCtxSelectedChain (nativeKernel)
open PqxdhServerAuthSendFactor (resolve)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
noncomputable def primitive (read : QueryImpl RegistrationRawReceiveBridge.Spec m) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec m :=
  read ∘ₛ (RegistrationRawReceiveBridge.modelAdapter ∘ₛ RawCtxSourceOpen.nativeAdapter)

theorem receive_source (read : QueryImpl RegistrationRawReceiveBridge.Spec m) (erased : Std.Array U8 227#usize)
    (descriptor : PublicAgreement) (root : RootOutput) (kernel : ConcreteRatchetKernel) :
    simulateQ read
      (RegistrationRawReceiveBridge.finishModel (atRoot descriptor root) <$>
        simulateQ RegistrationRawReceiveBridge.modelAdapter
          (RecordEffectsReceiveProgram.receive erased kernel 1#u64 descriptor.application
            descriptor.binding.associated_data descriptor.candidate.server_binding.identity_key_id)) =
      (fun result => observe descriptor result.1 result.2) <$>
        simulateQ (primitive read)
          (if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
              (absBytes descriptor.binding.associated_data) (frame descriptor) then
            simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel 1#u64 (context descriptor))
          else pure (kernel, .None)) := by
  have exactModel := RecordEffectsReceiveBridge.decoded_native_model erased kernel
    descriptor.candidate.server_binding.identity_key_id [] (frame descriptor) (absBytes descriptor.binding.associated_data)
    descriptor.application descriptor.binding.associated_data rfl rfl
  simp only [RecordEffectsReceiveProgram.decoded, frame, ite_true] at exactModel
  rw [exactModel]
  simp only [simulateQ_map, Functor.map_map, ← QueryImpl.simulateQ_compose]
  rfl

theorem owner_factor (read : QueryImpl RegistrationRawReceiveBridge.Spec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (charge : m Unit)
    (kdf : ∀ request, primitive read (.inl request) = charge *> pure (RawCtxSourceHkdf.response source.crypto request))
    (descriptor : PublicAgreement) (root : RootOutput) :
    (fun result => observe descriptor result.1 result.2) <$>
      simulateQ (primitive read)
        (if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
            (absBytes descriptor.binding.associated_data) (frame descriptor) then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive
              (nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
                (PqxdhServerAuthBeaconFactor.initial (PqxdhServerAuthSendFactor.other source root)))
              1#u64 (context descriptor))
        else pure
          (nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
            (PqxdhServerAuthBeaconFactor.initial (PqxdhServerAuthSendFactor.other source root)), .None)) =
      (if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (absBytes descriptor.binding.associated_data) (frame descriptor) then charge else pure ()) *>
        simulateQ (primitive read) (RegistrationBeaconSeed.program source descriptor (PqxdhServerAuthKeySchedule.fromRoot source root)) := by
  rw [← RegistrationBeaconSeed.labelled_program]
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (frame descriptor)
  · simp only [valid, ite_true, ← QueryImpl.simulateQ_compose]
    rw [RegistrationBeaconChargedReceive.primitive_receive (primitive read) source charge kdf,
      RegistrationBeaconChargedReceive.execute, Functor.map_map]
    simp only [seqRight_eq_bind, map_bind]
    apply bind_congr
    intro charged
    unfold RegistrationBeaconSeed.labelled
    rw [PqxdhServerAuthCtxMaterial.factor_source]
    simp only [valid, ite_true]
    exact PqxdhServerAuthBeaconFactor.program_settlement source (primitive read)
      (PqxdhServerAuthSendFactor.factor source root).1
      (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
      (observe descriptor) (fun _ _ => rfl) _
      (PqxdhServerAuthBeaconFactor.begin_ready _ 1#u64 (context descriptor) ⟨_, rfl⟩ rfl)
  · simp only [valid, ite_false, simulateQ_pure, map_pure, seqRight_eq_bind, pure_bind,
      RegistrationBeaconSeed.labelled]
    rfl

theorem source_factor (read : QueryImpl RegistrationRawReceiveBridge.Spec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (initialCharge ratchetCharge : m Unit)
    (initial : ∀ request, read (.inl (.initialKdf request)) = initialCharge *> pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request)))
    (kdf : ∀ request, primitive read (.inl request) = ratchetCharge *> pure (RawCtxSourceHkdf.response source.crypto request))
    (erased : Std.Array U8 227#usize) (descriptor : PublicAgreement) (root : RootOutput) :
    simulateQ read (RegistrationBeaconPostRootServices.beacon erased (atRoot descriptor root)) = (do
      let _ ← initialCharge
      let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
        (absBytes descriptor.binding.associated_data) (frame descriptor) then ratchetCharge else pure ()
      simulateQ (primitive read) (RegistrationBeaconSeed.program source descriptor (PqxdhServerAuthKeySchedule.fromRoot source root))) := by
  have started := (PqxdhBeaconPhase2Publication.initial_request descriptor.candidate
    (PqxdhRootTableInitialization.rootArray root)).1
  simp only [RegistrationBeaconPostRootServices.beacon, registration.begin_beacon_completion, atRoot,
    ratchet.RatchetChain.as_bytes, started, bind_tc_ok, RegistrationBeaconPostRootServices.continueWith,
    RegistrationBeaconPostRootServices.fromInitial, registration.BeaconInitialKdf.request,
    pqxdh.concrete.InitialRatchetKdfPending.impl.request,
    PqxdhInitialRatchetComplementarity.beaconPending, simulateQ_bind, simulateQ_spec_query]
  rw [initial]
  simp only [seqRight_eq_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro charged
  have kernelRun := PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
    (RawCtxSourceHkdf.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩)
  have initialEq := PqxdhServerAuthBeaconFactor.initial_source source root
  simp only [PqxdhInitialRatchetComplementarity.beaconPending] at kernelRun initialEq
  rw [initialEq] at kernelRun
  rw [kernelRun]
  simp only [RawCtxInterpretedOpening.bindResult]
  refine (receive_source read erased descriptor root _).trans ?_
  have factored := owner_factor read source ratchetCharge kdf descriptor root
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
    (absBytes descriptor.binding.associated_data) (frame descriptor)
  all_goals simpa only [valid, ite_true, ite_false, seqRight_eq_bind, pure_bind] using factored

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedSource.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedSource.receive_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedSource.owner_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedSource.owner_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedSource.source_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedSource.source_factor

end BeaconcryptCore.Computational.RegistrationBeaconChargedSource
