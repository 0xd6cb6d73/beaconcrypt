-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconSeed
/-! Public KDF accounting is performed on the actual receive path. Its callback is independent of private chain operands, so it can be retained when the source KDF is represented by its private selected label. Every hash and AEAD effect remains in the common interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconChargedReceive
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthSendFactor (Kernel)
open RawCtxSelectedChain (Slot nativeKernel)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
noncomputable def labels (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (charge : m Unit) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) m
  | .inl slot => charge *> pure (RawCtxSelectedChain.step source challenge slot)
  | .inr pending => PqxdhServerAuthBeaconFactor.primLabels prim source challenge (.inr pending)

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
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (charge : m Unit) (response : RatchetKdfResponse)
    (right : RootOutput) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (labels prim source charge response)
      (RawCtxChainReceive.execute (initial right) 1#u64 context) =
      (do
        let _ ← charge
        let reply ← labels prim source charge response
          (.inr (selected right context (RawCtxSelectedChain.step source response .hidden)))
        pure (RawCtxChainReceive.normalFinish
          (selected right context (RawCtxSelectedChain.step source response .hidden)) reply)) := by
  simp only [RawCtxChainReceive.execute, normal_begin_one, RawCtxChainReceive.program.eq_3,
    simulateQ_bind, simulateQ_spec_query, labels, seqRight_eq_bind, bind_assoc,
    show (first right context).request = Slot.hidden from rfl, pure_bind,
    normal_resume_one, RawCtxChainReceive.program.eq_2, simulateQ_pure]


theorem pure_labels (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (response : RatchetKdfResponse) :
    labels prim source (pure ()) response = PqxdhServerAuthBeaconFactor.primLabels prim source response := by
  funext query
  cases query <;> simp only [labels, seqRight_eq_bind, pure_bind, PqxdhServerAuthBeaconFactor.primLabels]

theorem execute (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (charge : m Unit) (response : RatchetKdfResponse)
    (right : RootOutput) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (labels prim source charge response) (RawCtxChainReceive.execute (initial right) 1#u64 context) =
      charge *> simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source response)
        (RawCtxChainReceive.execute (initial right) 1#u64 context) := by
  rw [← pure_labels prim source response, one_program, one_program]
  simp only [seqRight_eq_bind, pure_bind, labels]

theorem primitive_receive (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource)
    (charge : m Unit)
    (kdf : ∀ request, prim (.inl request) = charge *> pure (RawCtxSourceHkdf.response source.crypto request))
    (target : RatchetChain) (entry : Kernel) (requested : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (prim ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (nativeKernel target entry) requested context) =
      (fun result => (nativeKernel target result.1, result.2)) <$>
        simulateQ (labels prim source charge
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
          (RawCtxChainReceive.execute entry requested context) := by
  rw [nativeKernel, RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxChainReceive.execute_native (RawCtxSelectedChain.interpret target)
    (RawCtxSelectedChain.interpret target)
    (labels prim source charge (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target)))
    ((prim ∘ₛ RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter)
    ?_ ?_ entry requested context
  · simpa only [Functor.map_map, nativeKernel] using congrArg
      (fun work => (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> work) mapped
  · intro request
    simp only [QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
      simulateQ_map, simulateQ_spec_query, RawCtxWholeOwner.adapter, kdf, labels, seqRight_eq_bind, map_bind, map_pure, RawCtxSelectedChain.step_source]
    rfl
  · intro opening
    simp only [QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
      simulateQ_spec_query, labels, PqxdhServerAuthBeaconFactor.primLabels]
    exact congrArg (simulateQ prim) (RawCtxChainOpeningArguments.adapter_chains
      (RawCtxSelectedChain.interpret target) (fun _ => RawCtxSelectedChain.unusedChain)
      (RawCtxSelectedChain.interpret target) (fun _ => RawCtxSelectedChain.unusedChain) opening)

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.pure_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.pure_labels

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.execute

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.primitive_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedReceive.primitive_receive

end BeaconcryptCore.Computational.RegistrationBeaconChargedReceive
