import BeaconcryptCore.PanicFreedom.Control

/-!
# Panic freedom of material restoration

Restoration rejects inconsistent counters, full caches, and occupied slots normally. Array access is protected by the extracted capacity guard, so no material or logical representation invariant is needed for these normal-return theorems.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace beaconcrypt_core.ratchet

/-- Material restoration returns normally, including inconsistent representations. -/
theorem refined.refined_restore_receive_key_total {SendChain ReceiveChain Material : Type}
    (restore : refined.RefinedRatchetRestore SendChain ReceiveChain Material)
    (sequence : Std.U64) (material : Material) :
    ∃ r, refined.refined_restore_receive_key restore sequence material = ok r := by
  obtain ⟨step, hstep⟩ := control.restore_receive_key_with_slot_total restore.logical sequence
  simp only [refined.refined_restore_receive_key, hstep, bind_tc_ok]
  cases step with
  | none => exact ⟨_, rfl⟩
  | some step =>
    simp only [lift, control.capacity_eq_ok, bind_tc_ok]
    by_cases hcap : UScalar.cast UScalarTy.Usize step.slot ≥ UScalar.cast UScalarTy.Usize 50#u64
    · simpa only [if_pos hcap, RustM.ok.injEq] using Exists.intro (false, restore) rfl
    · have hi : (UScalar.cast UScalarTy.Usize step.slot).val < restore.receive_slots.length := by scalar_tac
      have hlt : UScalar.cast UScalarTy.Usize step.slot < 50#usize := by scalar_tac
      simp only [if_neg hcap, control.array_index_eq_ok _ _ hi, bind_tc_ok,
        decide_eq_true hlt, Bool.or_true, massert, if_true, control.array_index_mut_eq_ok _ _ hi]
      dsimp! only
      rw [control.array_update_eq_ok _ _ _ (by simpa using hi)]
      cases restore.receive_slots.val[(UScalar.cast UScalarTy.Usize step.slot).val] <;>
        simp [core.option.Option.is_some, Std.core.option.Option.is_some]

/-- Concrete restoration inherits the material restoration guarantee. -/
theorem concrete.concrete_restore_receive_key_total (restore : concrete.ConcreteRatchetRestore)
    (sequence : Std.U64) (material : RatchetMaterial) :
    ∃ r, concrete.concrete_restore_receive_key restore sequence material = ok r := by
  obtain ⟨⟨accepted, next⟩, h⟩ := refined.refined_restore_receive_key_total restore.refined sequence material
  simp [concrete.concrete_restore_receive_key, h]

/-- Starting a logical restoration always returns normally. -/
theorem control.start_restore_total (send receive : Std.U64) :
    ∃ r, control.start_restore send receive = ok r := ⟨_, rfl⟩

/-- Finishing a logical restoration always returns normally. -/
theorem control.finish_restore_total (restore : control.RatchetRestore) :
    ∃ r, control.finish_restore restore = ok r := ⟨_, rfl⟩

/-- Starting material restoration always returns normally. -/
theorem refined.start_refined_restore_total {SendChain ReceiveChain : Type} (Material : Type)
    (send receive : Std.U64) (sendChain : SendChain) (receiveChain : ReceiveChain) :
    ∃ r, refined.start_refined_restore Material send receive sendChain receiveChain = ok r := ⟨_, rfl⟩

/-- Finishing material restoration always returns normally. -/
theorem refined.finish_refined_restore_total {SendChain ReceiveChain Material : Type}
    (restore : refined.RefinedRatchetRestore SendChain ReceiveChain Material) :
    ∃ r, refined.finish_refined_restore restore = ok r := ⟨_, rfl⟩

/-- Starting concrete restoration always returns normally. -/
theorem concrete.start_concrete_restore_total (send receive : Std.U64)
    (sendChain receiveChain : RatchetChain) :
    ∃ r, concrete.start_concrete_restore send receive sendChain receiveChain = ok r := ⟨_, rfl⟩

/-- Finishing concrete restoration always returns normally. -/
theorem concrete.finish_concrete_restore_total (restore : concrete.ConcreteRatchetRestore) :
    ∃ r, concrete.finish_concrete_restore restore = ok r := ⟨_, rfl⟩

end beaconcrypt_core.ratchet
