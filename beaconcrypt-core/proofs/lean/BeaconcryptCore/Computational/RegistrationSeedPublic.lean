-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationPublicationKernelErasure

/-! The actual first-record capability depends on the generated seed only through its advanced whole kernel. All public source fields, the already bound AD, sequence-one context and selected position-one material remain unchanged when that private kernel is replaced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationSeedPublic
open RegistrationPublicationKernelErasure (mapOk)

private theorem material_assemble (key next : PqxdhSecretInputKdf.RootOutput)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) :
    PqxdhOrderedChainHybrids.material (RawCtxKdfRequestTable.assemble (key, next, nonce)) = (key, nonce) :=
  congrArg (fun parts => (parts.1, parts.2.2))
    (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.apply_symm_apply (key, next, nonce))

/-- Changing either generated chain coordinate changes only the private advanced kernel, through both actual native KDF resumes. -/
theorem selected_map (initial : registration.ServerInitialKdf) (root : Std.Array Std.U8 32#usize)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending root)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed₁ seed₂ : PqxdhRecordLiftSeed.Seed)
    (kernel₂ : ConcreteRatchetKernel) (kernelRun : PqxdhRecordLiftSeed.serverKernel seed₂ = .ok kernel₂) :
    RegistrationSeedErasure.selected initial
        (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ seed₂.2))
        (RawCtxKdfRequestTable.fullResponse (PqxdhDeploymentHiddenLayout.joinOutput material seed₂).1) =
      mapOk (RegistrationKernelErasure.selected kernel₂) <$>
        RegistrationSeedErasure.selected initial
          (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ seed₁.2))
          (RawCtxKdfRequestTable.fullResponse (PqxdhDeploymentHiddenLayout.joinOutput material seed₁).1) := by
  obtain ⟨bound, boundRun, _boundBytes⟩ := registration_key_id_binding_abs initial.candidate.key_id
  have contextRun : record_effects.SealFrameContext.registration initial.application
      initial.candidate.key_id initial.candidate.server_identity_key_id initial.binding.associated_data =
      .ok (serverRecordContext initial bound) := by
    simp [record_effects.SealFrameContext.registration, boundRun,
      pqxdh.RegistrationKeyIdBinding.as_bytes, serverRecordContext]
  simp only [PqxdhRecordLiftSeed.serverKernel, ConcreteRatchetKernel.from_counters,
    ratchet.refined.RefinedRatchet.from_counters, ratchet.control.RatchetState.from_counters,
    ratchet.control.SequenceCache.empty, ratchet.refined.empty_material_slots, bind_tc_ok,
    RustM.ok.injEq] at kernelRun
  rw [← kernelRun]
  simp only [RegistrationSeedErasure.selected, registration.ServerInitialKdf.resume,
    pqxdh.server_abort_candidate, RegistrationSeedErasure.initial_kernel initial root role,
    pqxdh.ServerRegistrationCandidate.impl.key_id, pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id,
    session.RegistrationBinding.impl.associated_data, contextRun, bind_tc_ok]
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty initial.application = .ok result := ⟨_, rfl⟩
  simp only [ConcreteRatchetKernel.from_counters, ratchet.refined.RefinedRatchet.from_counters,
    ratchet.control.RatchetState.from_counters, ratchet.control.SequenceCache.empty,
    ratchet.refined.empty_material_slots, bind_tc_ok, record_effects.begin_record_send,
    serverRecordContext, emptyRun]
  cases empty
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, core.option.Option.is_none,
    core.option.Option.is_some, bind_tc_ok, begin_send, ratchet.control.advance_send]
  all_goals simp only [ite_eq_right (by decide : 0#u64 ≠ core.num.U64.MAX),
    show (0#u64 + 1#u64 : RustM _) = .ok 1#u64 from rfl,
    bind_tc_ok, ratchet.control.SendKey.impl.sequence,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
    beq_self_eq_true, ratchet.control.RatchetState.impl.send_sequence, ite_true,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
    registration.ServerInitialSeal.resume, record_effects.RecordSendKdf.resume, SendKdf.resume,
    PqxdhDeploymentHiddenLayout.joinOutput, PqxdhRecordLiftSeed.response_step,
    PqxdhRecordLiftSeed.assembled_next, material_assemble]
  all_goals simp only [Bool.true_eq_false, decide_false, Bool.false_eq_true, ite_false, bind_tc_ok,
    RawCtxMaterialInterpretation.rust_map_ok, mapOk, RegistrationKernelErasure.selected]

/-- Both actual native resumes establish raw registration encoding before sealing. -/
theorem selected_raw (initial : registration.ServerInitialKdf)
    (initialResponse : pqxdh.concrete.InitialRatchetKdfResponse) (response : RatchetKdfResponse)
    (selected : registration.ServerRecordAead)
    (actual : RegistrationSeedErasure.selected initial initialResponse response = .ok (.Ok selected)) :
    selected.pending.seal.context.encoding = .Raw := by
  obtain ⟨kernel, bound, next, _kernelRun, _boundRun, _boundBytes, initialRun, _state,
      _entry, context, _sequence, _request⟩ := server_kdf_prefix_refines initial initialResponse
  obtain ⟨ready, readyRun, _state, retainedContext, _sequence, _control⟩ := server_step_kdf_refines next response
  simp only [RegistrationSeedErasure.selected, initialRun, bind_tc_ok, readyRun,
    RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
  subst selected
  rw [retainedContext, context]
  rfl

/-- At the actual public primitive interface, replacing the generated seed changes only the kernel retained in a successful hash capability. All AEAD/hash/raw-write effects and failures are identical. -/
theorem factored_raw_map (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed₁ seed₂ : PqxdhRecordLiftSeed.Seed)
    (kernel₂ : ConcreteRatchetKernel) (kernelRun : PqxdhRecordLiftSeed.serverKernel seed₂ = .ok kernel₂) :
    simulateQ RegistrationRawSealBridge.nativeAdapter
        (RegistrationBoundKeySchedule.factored initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₂)) =
      RegistrationKernelErasure.mapResult kernel₂ <$>
        simulateQ RegistrationRawSealBridge.nativeAdapter
          (RegistrationBoundKeySchedule.factored initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₁)) := by
  obtain ⟨selected, actual, _kernel⟩ := RegistrationBoundKeySchedule.factored_kernel initial material seed₁
  have mapped := selected_map (RegistrationBoundKeySchedule.restore initial)
    (PqxdhRootTableInitialization.rootArray RegistrationBoundKeySchedule.zero) rfl material seed₁ seed₂ kernel₂ kernelRun
  rw [actual, RawCtxMaterialInterpretation.rust_map_ok, mapOk] at mapped
  simp only [RegistrationBoundKeySchedule.factored, PqxdhDeploymentHiddenLayout.joinOutput] at actual mapped ⊢
  rw [actual, mapped]
  simp only [RegistrationServerRecordExecutor.continueResult]
  exact RegistrationKernelErasure.fromAead_map kernel₂ selected
    (selected_raw (RegistrationBoundKeySchedule.restore initial) _ _ selected actual)

private theorem map_state_apply {State Input Output : Type} (f : Input → Output)
    (work : StateT State ProbComp Input) (state : State) :
    (f <$> work).run state = Prod.map f id <$> work.run state := by
  change (work state >>= fun value => pure (f value.1, value.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- The complete actual shared source interpretation preserves the same cache and auxiliary state under hidden-seed replacement. -/
theorem factored_source_map {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed₁ seed₂ : PqxdhRecordLiftSeed.Seed)
    (kernel₂ : ConcreteRatchetKernel) (kernelRun : PqxdhRecordLiftSeed.serverKernel seed₂ = .ok kernel₂)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationRecordPrimitives.implementation source writer)
        (RegistrationBoundKeySchedule.factored initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₂))).run state =
      Prod.map (RegistrationKernelErasure.mapResult kernel₂) id <$>
        (simulateQ (RegistrationRecordPrimitives.implementation source writer)
          (RegistrationBoundKeySchedule.factored initial (PqxdhDeploymentHiddenLayout.joinOutput material seed₁))).run state := by
  rw [← RegistrationRawSealBridge.program_projection source writer,
    ← RegistrationRawSealBridge.program_projection source writer,
    factored_raw_map initial material seed₁ seed₂ kernel₂ kernelRun, simulateQ_map, map_state_apply]

end BeaconcryptCore.Computational.RegistrationSeedPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedPublic.selected_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedPublic.selected_map

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedPublic.selected_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedPublic.selected_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedPublic.factored_raw_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedPublic.factored_raw_map

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedPublic.factored_source_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedPublic.factored_source_map
