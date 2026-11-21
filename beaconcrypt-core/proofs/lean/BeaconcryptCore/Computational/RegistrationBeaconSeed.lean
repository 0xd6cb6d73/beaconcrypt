-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconBoundSource
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld

/-! The actual first Beacon receive requests one selected step. Its opening arguments contain the first message material and public context; a successful native completion retains the generated post-sequence-one kernel. The initial receive chain is absent from the executable factored service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconSeed
open PqxdhSecretInputKdf (RootOutput)
open RawCtxSelectedChain (Slot)
open PqxdhServerAuthBeaconFactor (initial)

private def first {Context : Type} (right : RootOutput) (context : Context) :
    RawCtxChainReceive.Kdf Slot Slot RatchetMaterial Context :=
  ⟨initial right, context, 1#u64, (initial right).control,
    Std.Array.repeat 50#usize .None, 0#u8, 0#u8, 1#u8, .hidden⟩

private theorem begin_one {Context : Type} (right : RootOutput) (context : Context) :
    RawCtxChainReceive.beginReceive (initial right) 1#u64 context = .ok (.kdfRequested (first right context)) := by
  simp only [RawCtxChainReceive.beginReceive, initial, first, ratchet.control.plan_receive_until]
  simp_scalar [control.RATCHET_MAX_GAP]
  simp only [ite_eq_right (by decide : ¬1#u64 ≤ 0#u64),
    show UScalar.cast .U64 0#u8 = 0#u64 from rfl,
    show UScalar.cast .U8 1#u64 = 1#u8 from rfl,
    show UScalar.cast .U8 0#u64 = 0#u8 from rfl,
    show (1#u64 - 0#u64 : RustM _) = ok 1#u64 from rfl,
    show (1#u64 - 1#u64 : RustM _) = ok 0#u64 from rfl,
    show (50#u64 - 0#u64 : RustM _) = ok 50#u64 from rfl,
    lift, bind_tc_ok, ite_eq_right (by decide : ¬50#u64 < 0#u64),
    ite_eq_right (by decide : (1#u64) ≠ 0#u64)]
  simp only [control.RatchetState.receive_cache_len, bind_tc_ok,
    refined_receive_slots_are_empty, refined_receive_slots_are_empty_loop, loop.eq_def,
    refined_receive_slots_are_empty_loop.body, ite_eq_right (by decide : ¬0#u8 > 0#u8),
    ite_true, empty_material_slots]
  rfl


private def selected {Context : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial Context :=
  ⟨initial right, context, .PreparedReceiveFutureCase
    ⟨⟨0#u64, 1#u64, ⟨Std.Array.repeat 50#usize 0#u64, 0#u8⟩⟩,
      step.1, Std.Array.repeat 50#usize .None, 1#u64, step.2, 0#u8, 0#u8⟩⟩

private theorem resume_one {Context : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) :
    RawCtxChainReceive.resume (first right context) (.ok step) = .ok (.openRequested (selected right context step)) := by
  simp only [RawCtxChainReceive.resume, first, initial,
    ite_eq_right (by decide : (1#u8) ≠ 0#u8), ite_true, control.advance_receive_target,
    ite_eq_right (by decide : 0#u64 ≠ core.num.U64.MAX),
    show (0#u64 + 1#u64 : RustM _) = ok 1#u64 from rfl,
    bind_tc_ok, ite_true, pending_receive_is_valid,
    control.RatchetState.impl.receive_sequence, control.RatchetState.impl.send_sequence,
    control.RatchetState.receive_cache_len]
  simp only [ite_eq_right (by decide : ¬1#u64 ≤ 0#u64),
    show UScalar.cast .U64 0#u8 = 0#u64 from rfl,
    show UScalar.cast .Usize 0#u8 = 0#usize from by scalar_tac,
    show (1#u64 - 0#u64 : RustM _) = ok 1#u64 from rfl,
    show (0#u64 + 1#u64 : RustM _) = ok 1#u64 from rfl,
    show (0#usize + 0#usize : RustM _) = ok 0#usize from
      (control.uscalar_add_eq_ok 0#usize 0#usize (by scalar_tac)).elim
        (fun z hz => hz.1.trans (congrArg ok (by have := hz.2; scalar_tac))),
    lift, bind_tc_ok, ite_true, control.lookup_receive_key_unfold,
    control.lookup_receive_key_loop, loop.eq_def, control.lookup_receive_key_loop.body,
    ite_eq_right (by decide : ¬0#u8 < 0#u8), core.option.Option.is_some,
    Bool.false_eq_true, ite_false,
    control.capacity_eq_ok,
    ite_eq_right (by decide : ¬0#usize > UScalar.cast .Usize 50#u64),
    receive_control_prefix_matches, receive_control_prefix_matches_loop,
    receive_control_prefix_matches_loop.body,
    ite_eq_left (by scalar_tac : 0#usize < UScalar.cast .Usize 50#u64),
    ite_eq_left (by decide : 50#u8 > 0#u8),
    ite_eq_right (by scalar_tac : ¬0#usize ≥ UScalar.cast .Usize 50#u64),
    ite_eq_left (by decide : 0#u8 ≥ 0#u8)]
  rw [control.array_index_eq_ok _ _ (by scalar_tac)]
  simp only [show (0#usize).val = 0 from by scalar_tac, bind_tc_ok,
    pending_receive_slots_are_valid, pending_receive_slots_are_valid_loop,
    loop.eq_def, pending_receive_slots_are_valid_loop.body,
    ite_eq_right (by decide : ¬0#u8 > 0#u8)]
  rfl


private theorem normal_begin_one {Context : Type} (right : RootOutput) (context : Context) :
    RawCtxChainReceive.normalBegin (initial right) 1#u64 context = .kdfRequested (first right context) :=
  RustM.ok.inj ((RawCtxChainReceive.normalBegin_exact _ _ _).symm.trans (begin_one right context))

private theorem normal_resume_one {Context : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) :
    RawCtxChainReceive.normalResume (first right context) step = .openRequested (selected right context step) :=
  RustM.ok.inj ((RawCtxChainReceive.normalResume_exact _ _).symm.trans (resume_one right context step))

private theorem one_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (response : RatchetKdfResponse)
    (right : RootOutput) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source response)
      (RawCtxChainReceive.execute (initial right) 1#u64 context) =
      (do
        let reply ← PqxdhServerAuthBeaconFactor.primLabels prim source response
          (.inr (selected right context (RawCtxSelectedChain.step source response .hidden)))
        pure (RawCtxChainReceive.normalFinish
          (selected right context (RawCtxSelectedChain.step source response .hidden)) reply)) := by
  simp only [RawCtxChainReceive.execute, normal_begin_one, RawCtxChainReceive.program.eq_3,
    simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthBeaconFactor.primLabels,
    show (first right context).request = Slot.hidden from rfl, pure_bind,
    normal_resume_one, RawCtxChainReceive.program.eq_2, simulateQ_pure]

private theorem selected_call {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (response₁ response₂ : RatchetKdfResponse)
    (right₁ right₂ : RootOutput) (context : RawCtxWholeOwner.OpenContext)
    (next₁ next₂ : Slot) (material : RatchetMaterial) :
    PqxdhServerAuthBeaconFactor.primLabels prim source response₁ (.inr (selected right₁ context (next₁, material))) =
      PqxdhServerAuthBeaconFactor.primLabels prim source response₂ (.inr (selected right₂ context (next₂, material))) := by
  rfl


private def settled (right : RootOutput) (next : Slot) : PqxdhServerAuthSendFactor.Kernel :=
  { control := ⟨0#u64, 1#u64, ⟨Std.Array.repeat 50#usize 0#u64, 0#u8⟩⟩
    send_chain := .known (RawCtxFreshChainCut.concreteChain right)
    receive_chain := next
    receive_slots := Std.Array.repeat 50#usize .None }

private theorem finish_some {Context Plaintext : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) (plaintext : Plaintext) :
    RawCtxInterpretedOpening.finish (selected right context step) (.Some plaintext) =
      .ok (settled right step.1, .Some plaintext) := by
  simp only [RawCtxInterpretedOpening.finish, selected, initial, publish_future_receive, lift,
    bind_tc_ok, control.capacity_eq_ok,
    show UScalar.cast .Usize 0#u8 = 0#usize from by scalar_tac,
    ite_eq_right (by scalar_tac : ¬0#usize > UScalar.cast .Usize 50#u64),
    show (UScalar.cast .Usize 50#u64 - 0#usize : RustM _) =
        ok (UScalar.cast .Usize 50#u64) from
      (control.uscalar_sub_eq_ok (UScalar.cast .Usize 50#u64) 0#usize (by scalar_tac)).elim
        (fun z hz => hz.1.trans (congrArg ok (by have := hz.2; scalar_tac))),
    publish_future_receive_slots, publish_future_receive_slots_loop, loop.eq_def,
    publish_future_receive_slots_loop.body, ite_eq_right (by decide : ¬0#u8 > 0#u8)]
  rfl

private theorem normal_finish_some {Context Plaintext : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) (plaintext : Plaintext) :
    RawCtxChainReceive.normalFinish (selected right context step) (.Some plaintext) =
      (settled right step.1, .Some plaintext) :=
  RustM.ok.inj ((RawCtxChainReceive.normalFinish_exact _ _).symm.trans (finish_some right context step plaintext))

private theorem normal_finish_none {Context Plaintext : Type} (right : RootOutput) (context : Context)
    (step : Slot × RatchetMaterial) :
    RawCtxChainReceive.normalFinish (selected right context step) (.None : core.option.Option Plaintext) =
      (initial right, .None) :=
  RustM.ok.inj ((RawCtxChainReceive.normalFinish_exact _ _).symm.trans rfl)

private theorem step_full (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (output : PqxdhFullSecretInputKdf.FullOutput) :
    RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden =
      (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output)),
        RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output)) := by
  simp only [RawCtxSelectedChain.step, RawCtxFreshChainCut.decoded_parts]

private theorem settled_world (right next : RootOutput) :
    PqxdhServerAuthSendFactor.resolve (settled right (.known (RawCtxFreshChainCut.concreteChain next))) =
      PqxdhRecordLiftWorld.kernel .beacon (next, right) := by
  have precise := PqxdhRecordLiftWorld.kernel_exact .beacon (next, right)
  change PqxdhRecordLiftSeed.beaconKernel (next, right) = .ok _ at precise
  exact RustM.ok.inj precise


def replace (kernel : ConcreteRatchetKernel) : RustM RegistrationBeaconRecordExecutor.Result →
    RustM RegistrationBeaconRecordExecutor.Result
  | .ok (.Ok completed) => .ok (.Ok { completed with kernel })
  | result => result

private theorem observe_replace (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (kernel₁ kernel₂ : ConcreteRatchetKernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    RegistrationBeaconBoundSource.observe descriptor kernel₂ reply =
      replace kernel₂ (RegistrationBeaconBoundSource.observe descriptor kernel₁ reply) := by
  cases reply with
  | none => rfl
  | some opened =>
    simp only [RegistrationBeaconBoundSource.observe, RegistrationRawReceiveBridge.finishAdmission]
    cases represented : RegistrationAuthenticationShared.openedBytes (some opened.plaintext) with
    | none => rfl
    | some plaintext => simp only; split_ifs <;> rfl

/-- The labelled sequence-one source continuation allows any effectful opening interpreter while retaining the exact source KDF factor. -/
noncomputable def labelled {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    m (RustM RegistrationBeaconRecordExecutor.Result) :=
  let value := PqxdhServerAuthCtxMaterial.factor output
  if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then
    (fun result => RegistrationBeaconBoundSource.observe descriptor
      (PqxdhServerAuthSendFactor.resolve result.1) result.2) <$>
      simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source value.1)
        (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFactor.initial value.2) 1#u64
          (RegistrationBeaconBoundSource.context descriptor))
  else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩))

private theorem labelled_one {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    labelled prim source descriptor output =
      if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then
        (fun reply =>
          let result := RawCtxChainReceive.normalFinish
            (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
              (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
                RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))) reply
          RegistrationBeaconBoundSource.observe descriptor (PqxdhServerAuthSendFactor.resolve result.1) result.2) <$>
          PqxdhServerAuthBeaconFactor.primLabels (prim) source
            (RawCtxKdfRequestTable.fullResponse output.1)
            (.inr (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
              (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
                RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))))
      else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩)) := by
  simp only [labelled,
    PqxdhServerAuthCtxMaterial.factor, one_program, step_full, bind_pure_comp]
  simp only [Functor.map_map]
  have queryEq := congrArg (fun step : Slot × RatchetMaterial =>
    (show m (core.option.Option RawCtxWholeOwner.Decrypted) from
    PqxdhServerAuthBeaconFactor.primLabels (prim)
      source (RawCtxKdfRequestTable.fullResponse output.1)
      (.inr (selected output.2 (RegistrationBeaconBoundSource.context descriptor) step)))) (step_full source output.1)
  dsimp only at queryEq
  rw [queryEq]
  rfl


private theorem fromOutput_one {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor output =
      if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then
        (fun reply =>
          let result := RawCtxChainReceive.normalFinish
            (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
              (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
                RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))) reply
          RegistrationBeaconBoundSource.observe descriptor (PqxdhServerAuthSendFactor.resolve result.1) result.2) <$>
          PqxdhServerAuthBeaconFactor.primLabels (RegistrationBeaconBoundSource.primitive source writer) source
            (RawCtxKdfRequestTable.fullResponse output.1)
            (.inr (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
              (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
                RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))))
      else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩)) :=
  labelled_one (RegistrationBeaconBoundSource.primitive source writer) source descriptor output

/-- At fixed first-message material, the complete native reply and every shared primitive effect change only the whole successfully installed Beacon kernel. -/
theorem output_map {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output₁ output₂ : PqxdhServerAuthKeySchedule.Output)
    (sameMaterial : PqxdhOrderedChainHybrids.material output₂.1 = PqxdhOrderedChainHybrids.material output₁.1) :
    RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor output₂ =
      replace (PqxdhRecordLiftWorld.kernel .beacon (PqxdhOrderedChainHybrids.nextChain output₂.1, output₂.2)) <$>
        RegistrationBeaconBoundSource.fromOutput source writer descriptor output₁ := by
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
  · simp only [fromOutput_one, valid, ite_true, Functor.map_map]
    rw [sameMaterial]
    have sameCall := selected_call (RegistrationBeaconBoundSource.primitive (Auxiliary := Auxiliary) source writer)
      source (RawCtxKdfRequestTable.fullResponse output₂.1) (RawCtxKdfRequestTable.fullResponse output₁.1)
      output₂.2 output₁.2 (RegistrationBeaconBoundSource.context descriptor)
      (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output₂.1)))
      (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output₁.1)))
      (RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output₁.1))
    rw [sameCall]
    apply map_congr
    intro reply
    cases reply with
    | none => simp only [normal_finish_none]; rfl
    | some plaintext =>
      simp only [normal_finish_some, settled_world]
      exact observe_replace descriptor _ _ (.Some plaintext)
  · simp only [fromOutput_one, valid, ite_false, map_pure]
    rfl


private theorem material_assemble (key next : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) :
    PqxdhOrderedChainHybrids.material (RawCtxKdfRequestTable.assemble (key, next, nonce)) = (key, nonce) :=
  congrArg (fun parts => (parts.1, parts.2.2))
    (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.apply_symm_apply (key, next, nonce))

def fixedSeed : PqxdhRecordLiftSeed.Seed := (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)

noncomputable def thin {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material) :=
  RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor
    (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed)

/-- Independent generated chains are retained solely in the successful native Beacon kernel; the thin executable reads only the first-message material and actual public binding. -/
theorem split {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      replace (PqxdhRecordLiftWorld.kernel .beacon seed) <$> thin source writer descriptor material := by
  have sameMaterial : PqxdhOrderedChainHybrids.material (PqxdhDeploymentHiddenLayout.joinOutput material seed).1 =
      PqxdhOrderedChainHybrids.material (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed).1 := by
    simp only [PqxdhDeploymentHiddenLayout.joinOutput, material_assemble]
  have result := output_map (Auxiliary := Auxiliary) source writer descriptor
    (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed)
    (PqxdhDeploymentHiddenLayout.joinOutput material seed) sameMaterial
  simpa only [PqxdhDeploymentHiddenLayout.joinOutput_next,
    show (PqxdhDeploymentHiddenLayout.joinOutput material seed).2 = seed.2 from rfl, Prod.mk.eta, thin] using result

structure PublicCompleted where
  control : pqxdh.BeaconEstablished
  binding : session.SessionBinding
  application : Slice U8

def publicResult : RustM RegistrationBeaconRecordExecutor.Result →
    RustM (core.result.Result PublicCompleted pqxdh.BeaconAborted)
  | .ok (.Ok completed) => .ok (.Ok ⟨completed.control, completed.binding, completed.application⟩)
  | .ok (.Err aborted) => .ok (.Err aborted)
  | .fail error => .fail error
  | .div => .div

private theorem public_replace (kernel : ConcreteRatchetKernel) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    publicResult (replace kernel result) = publicResult result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- Every actual public native completion field and all callback effects are independent of the generated seed at fixed first-message material. -/
theorem public_output {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    publicResult <$> RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      publicResult <$> thin source writer descriptor material := by
  rw [split, Functor.map_map]
  apply map_congr
  intro result
  exact public_replace _ result

/-- Any actual successful Beacon completion retains the entire generated post-sequence-one kernel, including both role counters and all receive-cache cells. -/
theorem completed_kernel {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) (completed : registration.CompletedBeacon)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((RegistrationBeaconBoundSource.fromOutput source writer descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material seed)).run before)) :
    completed.kernel = PqxdhRecordLiftWorld.kernel .beacon seed := by
  rw [split, StateT.run_map, support_map] at supported
  obtain ⟨⟨value, final⟩, _possible, equal⟩ := supported
  have replyEq := congrArg Prod.fst equal
  cases value with
  | fail error => cases replyEq
  | div => cases replyEq
  | ok result =>
    cases result with
    | Err aborted => cases replyEq
    | Ok original =>
      simp only [replace, RustM.ok.injEq, core.result.Result.Ok.injEq] at replyEq
      cases replyEq
      rfl

/-- An open native sequence-one continuation contains one actual opening capability and the already consumed whole kernel. The hidden variant below supplies only fixed placeholder chains. -/
noncomputable def program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RawCtxWholeOwner.PrimitiveSpec (RustM RegistrationBeaconRecordExecutor.Result) :=
  if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then
    (fun reply => RegistrationBeaconBoundSource.observe descriptor
      (PqxdhRecordLiftWorld.kernel .beacon (PqxdhOrderedChainHybrids.nextChain output.1, output.2)) reply) <$>
      PqxdhServerAuthBeaconFactor.primLabels (QueryImpl.ofLift RawCtxWholeOwner.PrimitiveSpec (OracleComp RawCtxWholeOwner.PrimitiveSpec))
        source (RawCtxKdfRequestTable.fullResponse output.1)
        (.inr (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
          (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
            RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))))
  else pure (.ok (.Err ⟨descriptor.candidate.server_binding.identity_key_id⟩))

private theorem program_call {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (response : RatchetKdfResponse)
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ prim (PqxdhServerAuthBeaconFactor.primLabels
      (QueryImpl.ofLift RawCtxWholeOwner.PrimitiveSpec (OracleComp RawCtxWholeOwner.PrimitiveSpec)) source response (.inr opening)) =
      PqxdhServerAuthBeaconFactor.primLabels prim source response (.inr opening) := by
  simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, simulateQ_ofLift_eq_self]

/-- The open program recovers the exact actual sequence-one source completion, including malformed frames, failed openings and all shared primitive state. -/
theorem labelled_program {m : Type → Type} [Monad m] [LawfulMonad m]
    (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    labelled prim source descriptor output =
      simulateQ (prim) (program source descriptor output) := by
  rw [labelled_one]
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
  · simp only [program, valid, ite_true, simulateQ_map]
    trans (fun reply => RegistrationBeaconBoundSource.observe descriptor
      (PqxdhRecordLiftWorld.kernel .beacon (PqxdhOrderedChainHybrids.nextChain output.1, output.2)) reply) <$>
        PqxdhServerAuthBeaconFactor.primLabels (prim) source
          (RawCtxKdfRequestTable.fullResponse output.1)
          (.inr (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
            (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
              RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1))))
    · apply map_congr
      intro reply
      cases reply with
      | none => simp only [normal_finish_none]; rfl
      | some plaintext => simp only [normal_finish_some, settled_world]
    · exact congrArg (fun work => (fun reply => RegistrationBeaconBoundSource.observe descriptor
        (PqxdhRecordLiftWorld.kernel .beacon (PqxdhOrderedChainHybrids.nextChain output.1, output.2)) reply) <$> work)
        (program_call (prim) source
          (RawCtxKdfRequestTable.fullResponse output.1)
          (selected output.2 (RegistrationBeaconBoundSource.context descriptor)
            (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output.1)),
              RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output.1)))).symm
  · simp only [program, valid, ite_false, simulateQ_pure]

/-- The open program recovers the exact actual sequence-one source completion, including malformed frames, failed openings and all shared primitive state. -/
theorem program_source {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    RegistrationBeaconBoundSource.fromOutput (Auxiliary := Auxiliary) source writer descriptor output =
      simulateQ (RegistrationBeaconBoundSource.primitive source writer) (program source descriptor output) :=
  labelled_program (RegistrationBeaconBoundSource.primitive source writer) source descriptor output

/-- At fixed message material, this arbitrary-interpreter equality changes only the entire successful native kernel. -/
theorem program_output_map (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output₁ output₂ : PqxdhServerAuthKeySchedule.Output)
    (sameMaterial : PqxdhOrderedChainHybrids.material output₂.1 = PqxdhOrderedChainHybrids.material output₁.1) :
    program source descriptor output₂ =
      replace (PqxdhRecordLiftWorld.kernel .beacon (PqxdhOrderedChainHybrids.nextChain output₂.1, output₂.2)) <$>
        program source descriptor output₁ := by
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
      (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
  · simp only [program, valid, ite_true, Functor.map_map]
    rw [sameMaterial]
    rw [selected_call _ source (RawCtxKdfRequestTable.fullResponse output₂.1)
      (RawCtxKdfRequestTable.fullResponse output₁.1) output₂.2 output₁.2
      (RegistrationBeaconBoundSource.context descriptor)
      (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output₂.1)))
      (.known (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output₁.1)))
      (RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output₁.1))]
    apply map_congr
    intro reply
    exact observe_replace descriptor _ _ reply
  · simp only [program, valid, ite_false, map_pure]
    rfl

noncomputable def publicProgram (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material) :=
  program source descriptor (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed)

theorem program_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    program source descriptor (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      replace (PqxdhRecordLiftWorld.kernel .beacon seed) <$> publicProgram source descriptor material := by
  have sameMaterial : PqxdhOrderedChainHybrids.material (PqxdhDeploymentHiddenLayout.joinOutput material seed).1 =
      PqxdhOrderedChainHybrids.material (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed).1 := by
    simp only [PqxdhDeploymentHiddenLayout.joinOutput, material_assemble]
  simpa only [PqxdhDeploymentHiddenLayout.joinOutput_next,
    show (PqxdhDeploymentHiddenLayout.joinOutput material seed).2 = seed.2 from rfl, Prod.mk.eta, publicProgram] using
      program_output_map source descriptor (PqxdhDeploymentHiddenLayout.joinOutput material fixedSeed)
        (PqxdhDeploymentHiddenLayout.joinOutput material seed) sameMaterial

end BeaconcryptCore.Computational.RegistrationBeaconSeed

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.output_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.output_map

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.split

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.public_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.public_output

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.completed_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.completed_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.program_output_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.program_output_map

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.program_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.program_split

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconSeed.labelled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconSeed.labelled_program
