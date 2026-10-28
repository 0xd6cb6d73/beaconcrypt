-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Effects

/-! Unconditional normal returns for the feature-gated receive-advance API. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- Defensive slot checks bound the counter increment even for arbitrary represented pending states. -/
theorem ReceiveAdvanceKdf.resume_total (pending : ReceiveAdvanceKdf)
    (response : RatchetKdfResponse) :
    ∃ result, pending.resume response = ok result := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [ReceiveAdvanceKdf.resume, hzero]
  · simp only [ReceiveAdvanceKdf.resume, hzero, ite_false]
    obtain ⟨advanced, hadvanced⟩ := control.advance_receive_ok pending.working_control
    cases hseq : advanced.sequence <;> cases hslot : advanced.slot <;>
      simp only [hadvanced, hseq, hslot, lift, bind_tc_ok, RustM.ok.injEq, exists_eq']
    rename_i sequence slot
    obtain ⟨logical, hlogical⟩ := control.RatchetState.receive_key_at_total advanced.state slot
    obtain ⟨nextSlot, hnextSlot, hnextSlotVal⟩ := control.uscalar_add_eq_ok
      (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.derived)
      (by scalar_tac)
    cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64, control.capacity_eq_ok, hnextSlot, bind_tc_ok,
      Bool.false_eq_true, ite_false, RustM.ok.injEq, exists_eq']
    repeat' first | exact ⟨_, rfl⟩ | split
    all_goals simp only [control.array_index_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
      (by scalar_tac), BeaconcryptCore.core_option_is_some_eq_ok, bind_tc_ok]
    all_goals (split <;> try exact ⟨_, rfl⟩)
    all_goals obtain ⟨derived, hderived, _⟩ :=
      control.uscalar_add_eq_ok pending.derived 1#u8 (by scalar_tac)
    all_goals obtain ⟨remaining, hremaining, _⟩ :=
      control.uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
    all_goals obtain ⟨stepped, hstepped⟩ :=
      BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
    all_goals simp only [hstepped, hderived, hremaining,
      control.array_index_mut_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
        (by scalar_tac), RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, bind_tc_ok]
    all_goals dsimp! only
    all_goals (split <;> try exact ⟨_, rfl⟩)
    obtain ⟨published, hpublished⟩ := refined.publish_future_receive_slots_ok pending.entry.refined
      (pending.staged_slots.set (UScalar.cast UScalarTy.Usize slot)
        (.Some ⟨sequence, stepped.material⟩)) pending.first_slot derived
    cases published
    simp only [hpublished, bind_tc_ok]
    exact ⟨_, rfl⟩

theorem ReceiveAdvanceKdf.request_total (pending : ReceiveAdvanceKdf) :
    ∃ result, ReceiveAdvanceKdf.impl.request pending = ok result := ⟨_, rfl⟩

theorem ReceiveAdvanceKdf.cancel_total (pending : ReceiveAdvanceKdf) :
    ∃ result, pending.cancel = ok result := ⟨_, rfl⟩

/-- Feature-gated admission validates arbitrary counters and material windows normally. -/
theorem begin_receive_advance_total (kernel : ConcreteRatchetKernel) (target : Std.U64) :
    ∃ result, begin_receive_advance kernel target = ok result := by
  obtain ⟨plan, hplan⟩ := control.plan_receive_until_total kernel.refined.control target
  cases hseq : plan.sequence <;> simp only [begin_receive_advance, hplan, hseq, bind_tc_ok,
    RustM.ok.injEq, exists_eq']
  obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel.refined
    kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 plan.derivations)
  cases empty <;> simp only [lift, control.RatchetState.receive_cache_len, hempty,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
    bind_tc_ok, Bool.false_eq_true, ite_false, ite_true]
  all_goals repeat' first | exact ⟨_, rfl⟩ | split

end beaconcrypt_core.ratchet.concrete

/-- info: 'beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.resume_total

/-- info: 'beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.request_total

/-- info: 'beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.cancel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.ReceiveAdvanceKdf.cancel_total

/-- info: 'beaconcrypt_core.ratchet.concrete.begin_receive_advance_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_core.ratchet.concrete.begin_receive_advance_total
