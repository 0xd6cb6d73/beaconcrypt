-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconPostRootServices
import BeaconcryptCore.Computational.RegistrationBoundSource
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor
import BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial

/-! Actual Beacon completion consumes the authenticated binding before its sequence-one opening. An internal decoded frame exposes its already retained ciphertext, pinned sender and fixed sequence; it is an executable service interface rather than a replacement wire decoder. The native final admission, optional plaintext representation and completed binding remain in the output. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBeaconBoundSource
open PqxdhSecretInputKdf (RootOutput)
open RawCtxSelectedChain (nativeKernel)
open PqxdhServerAuthSendFactor (resolve)
variable {Auxiliary : Type}

structure PublicAgreement where
  candidate : pqxdh.BeaconRegistrationCandidate
  binding : session.CompletedRegistrationBinding
  application : Slice U8

def atRoot (descriptor : PublicAgreement) (root : RootOutput) : agreement.BeaconAgreement :=
  ⟨descriptor.candidate, descriptor.binding, ⟨PqxdhRootTableInitialization.rootArray root⟩, descriptor.application⟩

def frame (descriptor : PublicAgreement) : RawCtxReceive.DecodedFrame :=
  { sender := descriptor.candidate.server_binding.identity_key_id
    sequence := 1#u64
    payload := TranscriptAuthParts.absSlice descriptor.application }

def context (descriptor : PublicAgreement) : RawCtxWholeOwner.OpenContext :=
  ⟨[], frame descriptor, absBytes descriptor.binding.associated_data⟩

noncomputable def primitive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) : QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RegistrationRawReceiveBridge.implementation source writer ∘ₛ (RegistrationRawReceiveBridge.modelAdapter ∘ₛ
    RawCtxSourceOpen.nativeAdapter)

def observe (descriptor : PublicAgreement) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) : RustM RegistrationBeaconRecordExecutor.Result :=
  RegistrationRawReceiveBridge.finishAdmission (atRoot descriptor RegistrationBoundKeySchedule.zero) (kernel, reply)

theorem primitive_kdf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : SymmetricRatchetKdfRequest) :
    primitive (Auxiliary := Auxiliary) source writer (.inl request) =
      pure (RawCtxSourceHkdf.response source.crypto request) := by
  rfl

/-- Actual source record admission has precisely the internal decoded-frame service, including malformed payloads and optional primitive failures. -/
theorem receive_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array U8 227#usize)
    (descriptor : PublicAgreement) (root : RootOutput) (kernel : ConcreteRatchetKernel) :
    simulateQ (RegistrationRawReceiveBridge.implementation (Auxiliary := Auxiliary) source writer)
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
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (RustM RegistrationBeaconRecordExecutor.Result) :=
  if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (frame descriptor) then
    (fun result => observe descriptor (resolve result.1) result.2) <$>
      simulateQ (PqxdhServerAuthBeaconFactor.primLabels (primitive source writer) source value.1)
        (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFactor.initial value.2) 1#u64 (context descriptor))
  else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩))

noncomputable def fromOutput (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :=
  fromFactor (Auxiliary := Auxiliary) source writer descriptor (PqxdhServerAuthCtxMaterial.factor output)

/-- The old initial receive chain disappears through actual receive settlement, including every failed opening and unchanged primitive effect. -/
theorem owner_factor (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : PublicAgreement) (root : RootOutput) :
    (fun result => observe descriptor result.1 result.2) <$>
      simulateQ (primitive (Auxiliary := Auxiliary) source writer)
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


/-- The actual typed initial callback and complete sequence-one source controller consume the same 108-byte entry as the Server, retaining the actual native completion and shared state. -/
theorem source_factor (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (erased : Std.Array U8 227#usize)
    (descriptor : PublicAgreement) (root : RootOutput) :
    RegistrationBeaconRecordExecutor.execute (Auxiliary := Auxiliary) source writer (atRoot descriptor root) =
      fromOutput source writer descriptor (PqxdhServerAuthKeySchedule.fromRoot source root) := by
  apply StateT.ext
  intro state
  rw [RegistrationBeaconPostRootServices.beacon_shared source writer erased]
  have started := (PqxdhBeaconPhase2Publication.initial_request descriptor.candidate
    (PqxdhRootTableInitialization.rootArray root)).1
  simp only [RegistrationBeaconPostRootServices.beacon, registration.begin_beacon_completion, atRoot,
    ratchet.RatchetChain.as_bytes, started, bind_tc_ok, RegistrationBeaconPostRootServices.continueWith,
    RegistrationBeaconPostRootServices.fromInitial, registration.BeaconInitialKdf.request,
    pqxdh.concrete.InitialRatchetKdfPending.impl.request,
    PqxdhInitialRatchetComplementarity.beaconPending, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [show (RegistrationRawReceiveBridge.implementation source writer
      (.inl (.initialKdf ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩))).run state =
      pure (.Some (RawCtxSourceHkdf.initialResponse source.crypto
        ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩), state) from rfl]
  simp only [pure_bind]
  have kernelRun := PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
    (RawCtxSourceHkdf.initialResponse source.crypto
      ⟨PqxdhRootTableInitialization.rootArray root, INITIAL_RATCHET_INFO⟩)
  have initialEq := PqxdhServerAuthBeaconFactor.initial_source source root
  simp only [PqxdhInitialRatchetComplementarity.beaconPending] at kernelRun initialEq
  rw [initialEq] at kernelRun
  rw [kernelRun]
  simp only [RawCtxInterpretedOpening.bindResult]
  exact congrArg (fun work => work.run state)
    ((receive_source source writer erased descriptor root _).trans (owner_factor source writer descriptor root))

end BeaconcryptCore.Computational.RegistrationBeaconBoundSource

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBoundSource.primitive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBoundSource.primitive_kdf

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBoundSource.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBoundSource.receive_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBoundSource.owner_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBoundSource.owner_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBoundSource.source_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBoundSource.source_factor
