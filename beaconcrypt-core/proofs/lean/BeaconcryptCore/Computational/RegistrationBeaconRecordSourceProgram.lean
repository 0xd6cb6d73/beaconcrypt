-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconService

/-! The actual first Beacon record is factored before interpreting its public hash effects. Source HKDF and AEAD remain their concrete deterministic functions; every commitment query remains an explicit EnvEffects request. This permits the later stateful native interpretation to retain the same cache, counters and optional failure states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram
open RegistrationBeaconBoundSource (PublicAgreement atRoot frame context observe)
open PqxdhRecordLiftInterface (EnvEffects)
open PqxdhSecretInputKdf (RootOutput)
open RawCtxSelectedChain (nativeKernel)
open PqxdhServerAuthSendFactor (resolve)
variable {n : Nat}

noncomputable def read (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRawReceiveBridge.Spec (OracleComp (EnvEffects n)) :=
  RegistrationBoundSourceCompiler.rawCompiler source writer ∘ₛ RegistrationNativePairedBeaconService.read source

noncomputable def primitive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp (EnvEffects n)) :=
  read source writer ∘ₛ (RegistrationRawReceiveBridge.modelAdapter ∘ₛ RawCtxSourceOpen.nativeAdapter)

/-- The real source KDF is evaluated locally; it neither queries the public hash channel nor substitutes an independent key. -/
theorem primitive_kdf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest) :
    primitive (n := n) source writer (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request) := by
  rfl

/-- Native decoding, optional plaintext representation and final admission agree before any public effect is interpreted. -/
theorem receive_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array U8 357#usize)
    (descriptor : PublicAgreement) (root : RootOutput) (kernel : ConcreteRatchetKernel) :
    simulateQ (read (n := n) source writer)
      (RegistrationRawReceiveBridge.finishModel (atRoot descriptor root) <$>
        simulateQ RegistrationRawReceiveBridge.modelAdapter
          (RecordEffectsReceiveProgram.receive erased kernel 1#u64 descriptor.application
            descriptor.binding.associated_data descriptor.candidate.server_binding.identity_key_id)) =
      (fun result => observe descriptor result.1 result.2) <$>
        simulateQ (primitive source writer)
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

noncomputable def fromFactor (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (value : PqxdhServerAuthSendFactor.Factor) :
    OracleComp (EnvEffects n) (RustM RegistrationBeaconRecordExecutor.Result) :=
  if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (frame descriptor) then
    (fun result => observe descriptor (resolve result.1) result.2) <$>
      simulateQ (PqxdhServerAuthBeaconFactor.primLabels (primitive source writer) source value.1)
        (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFactor.initial value.2) 1#u64 (context descriptor))
  else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩))

noncomputable def fromOutput (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :=
  fromFactor (n := n) source writer descriptor (PqxdhServerAuthCtxMaterial.factor output)

/-- The old initial receive chain disappears through actual receive settlement, including every failed opening and unchanged primitive effect. -/
theorem owner_factor (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (root : RootOutput) :
    (fun result => observe descriptor result.1 result.2) <$>
      simulateQ (primitive (n := n) source writer)
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
      fromOutput source writer descriptor (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  unfold fromOutput
  rw [PqxdhServerAuthCtxMaterial.factor_source]
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (frame descriptor)
  · simp only [fromFactor, valid, ite_true, ← QueryImpl.simulateQ_compose]
    rw [PqxdhServerAuthBeaconFactor.primitive_receive (primitive source writer) source (primitive_kdf source writer),
      Functor.map_map]
    exact PqxdhServerAuthBeaconFactor.program_settlement source (primitive source writer)
      (PqxdhServerAuthSendFactor.factor source root).1
      (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root))
      (observe descriptor) (fun _ _ => rfl) _
      (PqxdhServerAuthBeaconFactor.begin_ready _ 1#u64 (context descriptor) ⟨_, rfl⟩ rfl)
  · simp only [fromFactor, valid, ite_false, simulateQ_pure, map_pure]
    rfl



/-- The real sequence-one continuation is the open native program, before any shared World effects are interpreted. -/
theorem output_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    fromOutput (n := n) source writer descriptor output =
      simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer)
        (RegistrationNativePairedBeaconService.program source descriptor output) := by
  have generic := RegistrationBeaconSeed.labelled_program (primitive (n := n) source writer) source descriptor output
  simpa only [fromOutput, fromFactor, RegistrationBeaconSeed.labelled,
    RegistrationNativePairedBeaconService.program, primitive, read,
    RegistrationNativePairedBeaconService.opening, QueryImpl.simulateQ_compose] using generic

/-- The actual initial64 callback uses the source function without any public oracle effect. -/
theorem initial_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest) :
    read (n := n) source writer (.inl (.initialKdf request)) =
      pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto request)) := by
  rfl

/-- Actual initial64 and ongoing76 are the same source108 entry, with all later hash effects still explicit. -/
theorem source_factor (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array U8 357#usize)
    (descriptor : PublicAgreement) (root : RootOutput) :
    simulateQ (read (n := n) source writer)
      (RegistrationBeaconPostRootServices.beacon erased (atRoot descriptor root)) =
      fromOutput source writer descriptor (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  have started := (PqxdhBeaconPhase2Publication.initial_request descriptor.candidate
    (PqxdhRootTableInitialization.rootArray root)).1
  simp only [RegistrationBeaconPostRootServices.beacon, registration.begin_beacon_completion, atRoot,
    ratchet.RatchetChain.as_bytes, started, bind_tc_ok, RegistrationBeaconPostRootServices.continueWith,
    RegistrationBeaconPostRootServices.fromInitial, registration.BeaconInitialKdf.request,
    pqxdh.concrete.InitialRatchetKdfPending.impl.request,
    PqxdhInitialRatchetComplementarity.beaconPending, simulateQ_bind, simulateQ_spec_query]
  rw [initial_source]
  simp only [pure_bind]
  have kernelRun := PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
    (RawCtxSourceHkdf.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, SYM_RATCHET_INFO⟩)
  have initialEq := PqxdhServerAuthBeaconFactor.initial_source source root
  simp only [PqxdhInitialRatchetComplementarity.beaconPending] at kernelRun initialEq
  rw [initialEq] at kernelRun
  rw [kernelRun]
  simp only [RawCtxInterpretedOpening.bindResult]
  exact (receive_source source writer erased descriptor root _).trans (owner_factor source writer descriptor root)

noncomputable def native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (EnvEffects n)) :=
  read source writer ∘ₛ RegistrationRawReceiveBridge.nativeAdapter

/-- The complete extracted first-record controller and its bound108 open service have identical public primitive programs. -/
theorem controller_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array U8 357#usize)
    (descriptor : PublicAgreement) (root : RootOutput) :
    simulateQ (native (n := n) source writer) (RegistrationBeaconRecordExecutor.begin (atRoot descriptor root)) =
      simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer)
        (RegistrationNativePairedBeaconService.program source descriptor (PqxdhServerAuthKeySchedule.fromRoot source root)) := by
  rw [native, QueryImpl.simulateQ_compose, RegistrationBeaconPostRootServices.beacon_exact erased,
    source_factor, output_program]

end BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.primitive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.primitive_kdf

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.receive_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.owner_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.owner_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.output_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.output_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.initial_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.source_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.source_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.controller_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram.controller_source
