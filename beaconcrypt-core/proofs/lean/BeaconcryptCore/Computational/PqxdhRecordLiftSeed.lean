-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhInitialReplyErasure
import BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor
import BeaconcryptCore.Refinement.RatchetReceiveLoopExact

/-! Exact successful sequence-one source kernels. These constructors contain only the two post-registration chains and the fixed role counters. The source equalities below do not assert successful authentication or publication. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSeed
open PqxdhSecretInputKdf RawCtxFreshChainCut

abbrev Seed := RootOutput × RootOutput

abbrev serverKernel (seed : Seed) : RustM ConcreteRatchetKernel :=
  ConcreteRatchetKernel.from_counters 1#u64 0#u64
    (concreteChain seed.1) (concreteChain seed.2)

abbrev beaconKernel (seed : Seed) : RustM ConcreteRatchetKernel :=
  ConcreteRatchetKernel.from_counters 0#u64 1#u64
    (concreteChain seed.2) (concreteChain seed.1)

/-- Follow the extracted sequence-one receive phases, retaining a mismatch as an explicit absent result. This helper supplies one typed response and one successful opening result; it executes no cryptography. -/
def receiveOne {Context Plaintext : Type} (entry : ConcreteRatchetKernel)
    (response : RatchetKdfResponse) (context : Context) (plaintext : Plaintext) :
    RustM (Option (ConcreteRatchetKernel × core.option.Option Plaintext)) := do
  let effect ← begin_receive entry 1#u64 context
  match effect with
  | .ReceiveKdfRequested pending =>
      let effect ← pending.resume response
      match effect with
      | .ReceiveOpenRequested pending => some <$> pending.finish (.Some plaintext)
      | _ => ok none
  | _ => ok none

theorem receiveOne_from_counters {Context Plaintext : Type}
    (left right : RatchetChain) (response : RatchetKdfResponse)
    (step : RatchetStep RatchetChain RatchetMaterial)
    (decoded : ratchet_step_from_response response = ok step)
    (context : Context) (plaintext : Plaintext) :
    (do let entry ← ConcreteRatchetKernel.from_counters 0#u64 0#u64 right left
        receiveOne entry response context plaintext) =
      (fun kernel => some (kernel, core.option.Option.Some plaintext)) <$>
        ConcreteRatchetKernel.from_counters 0#u64 1#u64 right step.chain := by
  simp only [ConcreteRatchetKernel.from_counters, RefinedRatchet.from_counters,
    control.RatchetState.from_counters, control.SequenceCache.empty,
    empty_material_slots, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok, receiveOne, begin_receive,
    control.plan_receive_until]
  simp_scalar [control.RATCHET_MAX_GAP]
  simp only [ite_eq_right (by decide : ¬1#u64 ≤ 0#u64),
    show UScalar.cast .U64 0#u8 = 0#u64 from rfl,
    show UScalar.cast .U8 1#u64 = 1#u8 from rfl,
    show UScalar.cast .U8 0#u64 = 0#u8 from rfl,
    show (1#u64 - 0#u64 : RustM _) = ok 1#u64 from by rfl,
    show (1#u64 - 1#u64 : RustM _) = ok 0#u64 from by rfl,
    show (50#u64 - 0#u64 : RustM _) = ok 50#u64 from by rfl,
    lift, bind_tc_ok, ite_eq_right (by decide : ¬50#u64 < 0#u64),
    ite_eq_right (by decide : (1#u64) ≠ 0#u64)]
  simp only [control.RatchetState.receive_cache_len, bind_tc_ok,
    refined_receive_slots_are_empty, refined_receive_slots_are_empty_loop, loop.eq_def,
    refined_receive_slots_are_empty_loop.body,
    ite_eq_right (by decide : ¬0#u8 > 0#u8), ite_true,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, ReceiveKdf.resume,
    ite_eq_right (by decide : (1#u8) ≠ 0#u8), control.advance_receive_target]
  simp only [ite_eq_right (by decide : 0#u64 ≠ core.num.U64.MAX),
    show (0#u64 + 1#u64 : RustM _) = ok 1#u64 from rfl,
    bind_tc_ok, ite_true, decoded, pending_receive_is_valid,
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
  simp only [Array.make, show (0#usize).val = 0 from by scalar_tac,
    List.getElem_cons_zero, bind_tc_ok, Bool.false_eq_true, ite_false,
    pending_receive_slots_are_valid, pending_receive_slots_are_valid_loop,
    loop.eq_def, pending_receive_slots_are_valid_loop.body,
    ite_eq_right (by decide : ¬0#u8 > 0#u8), ite_true, ReceiveOpen.finish]
  simp only [publish_future_receive, lift, bind_tc_ok, control.capacity_eq_ok,
    show UScalar.cast .Usize 0#u8 = 0#usize from by scalar_tac,
    ite_eq_right (by scalar_tac : ¬0#usize > UScalar.cast .Usize 50#u64),
    show (UScalar.cast .Usize 50#u64 - 0#usize : RustM _) =
        ok (UScalar.cast .Usize 50#u64) from
      (control.uscalar_sub_eq_ok (UScalar.cast .Usize 50#u64) 0#usize (by scalar_tac)).elim
        (fun z hz => hz.1.trans (congrArg ok (by have := hz.2; scalar_tac))),
    publish_future_receive_slots, publish_future_receive_slots_loop, loop.eq_def,
    publish_future_receive_slots_loop.body,
    ite_eq_right (by decide : ¬0#u8 > 0#u8)]
  rfl

/-- The original initializer uses the two supplied halves in opposite role directions and zeroes both counters. -/
theorem initial_kernel (role : Bool) (left right : RootOutput) :
    PqxdhInitialReplyErasure.kernelOf role
      (RawCtxSelectedInitialConstructor.response64 (left ++ right)) =
      ConcreteRatchetKernel.from_counters 0#u64 0#u64
        (concreteChain (if role then right else left))
        (concreteChain (if role then left else right)) := by
  have result := RawCtxSelectedInitialConstructor.from64_initial
    (role, PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)) left right
  simp only [RawCtxSelectedInitialConstructor.initial,
    ← RawCtxSelectedInitialConstructor.new_map] at result
  cases role <;> simpa only [RawCtxSelectedInitialConstructor.from64,
    PqxdhInitialReplyErasure.kernelOf, PqxdhInitialResponseService.pending,
    RawCtxSelectedInitialConstructor.sendSlot, RawCtxSelectedInitialConstructor.receiveSlot,
    RawCtxSelectedChain.interpret, ConcreteRatchetKernel.new, Bool.false_eq_true,
    ite_false, ite_true] using result

/-- Follow the extracted first-send phases with one supplied typed KDF response and the actual optional seal result. -/
def sendOne {Context Output : Type} (entry : ConcreteRatchetKernel)
    (response : RatchetKdfResponse) (context : Context) (sealed : core.option.Option Output) :
    RustM (Option (ConcreteRatchetKernel × core.option.Option Output)) := do
  let start ← begin_send entry context
  match start with
  | .SendKdfRequested pending =>
      let ready ← pending.resume response
      some <$> ready.finish sealed
  | _ => ok none

theorem sendOne_from_counters {Context Output : Type}
    (left right : RatchetChain) (response : RatchetKdfResponse)
    (step : RatchetStep RatchetChain RatchetMaterial)
    (decoded : ratchet_step_from_response response = ok step)
    (context : Context) (sealed : core.option.Option Output) :
    (do let entry ← ConcreteRatchetKernel.from_counters 0#u64 0#u64 left right
        sendOne entry response context sealed) =
      (fun kernel => some (kernel, sealed)) <$>
        ConcreteRatchetKernel.from_counters 1#u64 0#u64 step.chain right := by
  simp only [ConcreteRatchetKernel.from_counters, RefinedRatchet.from_counters,
    control.RatchetState.from_counters, control.SequenceCache.empty,
    empty_material_slots, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok,
    sendOne, begin_send, control.advance_send]
  simp only [ite_eq_right (by decide : 0#u64 ≠ core.num.U64.MAX),
    show (0#u64 + 1#u64 : RustM _) = ok 1#u64 from rfl,
    bind_tc_ok, control.SendKey.impl.sequence, ite_true,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
    beq_self_eq_true, control.RatchetState.impl.send_sequence,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
    SendKdf.resume, decoded, SendSeal.finish_returns_interpreter_result,
    RawCtxMaterialInterpretation.rust_map_ok]

theorem response_step (output : PqxdhFullSecretInputKdf.FullOutput) :
    ratchet_step_from_response (RawCtxKdfRequestTable.fullResponse output) =
      ok ⟨concreteChain (PqxdhOrderedChainHybrids.nextChain output),
        concreteMaterial (PqxdhOrderedChainHybrids.material output)⟩ := by
  have exactStep : ratchet_step_from_response (RawCtxKdfRequestTable.fullResponse output) =
      ok ⟨(RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)).1,
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)).2⟩ :=
    (BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok
      (RawCtxKdfRequestTable.fullResponse output)).choose_spec
  simpa only [RawCtxFreshChainCut.decoded_parts] using exactStep

/-- Every seed gives a normal Server kernel; constructor refusal has probability zero under every seed distribution. -/
theorem serverKernel_total (seed : Seed) : ∃ kernel, serverKernel seed = ok kernel :=
  ⟨_, rfl⟩

/-- Every seed gives a normal Beacon kernel, independently of registration acceptance. -/
theorem beaconKernel_total (seed : Seed) : ∃ kernel, beaconKernel seed = ok kernel :=
  ⟨_, rfl⟩

/-- Successful extracted sequence-one opening installs precisely the seed kernel, including every counter and cache cell. The supplied plaintext is an opening outcome, not a claim that AEAD accepts. -/
theorem beacon_source {Context Plaintext : Type} (left right : RootOutput)
    (output : PqxdhFullSecretInputKdf.FullOutput) (context : Context) (plaintext : Plaintext) :
    (do let entry ← PqxdhInitialReplyErasure.kernelOf true
          (RawCtxSelectedInitialConstructor.response64 (left ++ right))
        receiveOne entry (RawCtxKdfRequestTable.fullResponse output) context plaintext) =
      (fun kernel => some (kernel, core.option.Option.Some plaintext)) <$>
        beaconKernel (PqxdhOrderedChainHybrids.nextChain output, right) := by
  simpa only [initial_kernel, ite_true] using receiveOne_from_counters
    (concreteChain left) (concreteChain right) (RawCtxKdfRequestTable.fullResponse output)
    _ (response_step output) context plaintext

/-- The extracted first send advances precisely to the Server seed kernel even when its supplied seal reply is absent; registration publication remains a separate later gate. -/
theorem server_source {Context Output : Type} (left right : RootOutput)
    (output : PqxdhFullSecretInputKdf.FullOutput) (context : Context) (sealed : core.option.Option Output) :
    (do let entry ← PqxdhInitialReplyErasure.kernelOf false
          (RawCtxSelectedInitialConstructor.response64 (left ++ right))
        sendOne entry (RawCtxKdfRequestTable.fullResponse output) context sealed) =
      (fun kernel => some (kernel, sealed)) <$>
        serverKernel (PqxdhOrderedChainHybrids.nextChain output, right) := by
  simpa only [initial_kernel, Bool.false_eq_true, ite_false] using sendOne_from_counters
    (concreteChain left) (concreteChain right) (RawCtxKdfRequestTable.fullResponse output)
    _ (response_step output) context sealed

/-- Assembly preserves the retained chain coordinate exactly; the other coordinates are independent arguments of this equation. -/
theorem assembled_next (key next : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) :
    PqxdhOrderedChainHybrids.nextChain (RawCtxKdfRequestTable.assemble (key, next, nonce)) = next := by
  exact congrArg (fun parts => parts.2.1)
    (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.apply_symm_apply (key, next, nonce))

/-- The successful Beacon kernel depends on `seed` alone; changing the first key, nonce, old left chain or opening context does not change this entire kernel result. -/
theorem beacon_source_parts {Context Plaintext : Type} (left key : RootOutput) (seed : Seed)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (context : Context) (plaintext : Plaintext) :
    (do let entry ← PqxdhInitialReplyErasure.kernelOf true
          (RawCtxSelectedInitialConstructor.response64 (left ++ seed.2))
        receiveOne entry (RawCtxKdfRequestTable.fullResponse
          (RawCtxKdfRequestTable.assemble (key, seed.1, nonce))) context plaintext) =
      (fun kernel => some (kernel, core.option.Option.Some plaintext)) <$> beaconKernel seed := by
  simpa only [assembled_next] using beacon_source left seed.2
    (RawCtxKdfRequestTable.assemble (key, seed.1, nonce)) context plaintext

/-- First-send advancement depends on `seed` alone and retains the supplied optional seal result unchanged. This equation does not publish a peer after a failed seal. -/
theorem server_source_parts {Context Output : Type} (left key : RootOutput) (seed : Seed)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (context : Context) (sealed : core.option.Option Output) :
    (do let entry ← PqxdhInitialReplyErasure.kernelOf false
          (RawCtxSelectedInitialConstructor.response64 (left ++ seed.2))
        sendOne entry (RawCtxKdfRequestTable.fullResponse
          (RawCtxKdfRequestTable.assemble (key, seed.1, nonce))) context sealed) =
      (fun kernel => some (kernel, sealed)) <$> serverKernel seed := by
  simpa only [assembled_next] using server_source left seed.2
    (RawCtxKdfRequestTable.assemble (key, seed.1, nonce)) context sealed

end BeaconcryptCore.Computational.PqxdhRecordLiftSeed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.receiveOne_from_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.receiveOne_from_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.initial_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.initial_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.sendOne_from_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.sendOne_from_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.response_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.response_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.serverKernel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.serverKernel_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beaconKernel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beaconKernel_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beacon_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.server_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.assembled_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.assembled_next

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beacon_source_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.beacon_source_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeed.server_source_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeed.server_source_parts
