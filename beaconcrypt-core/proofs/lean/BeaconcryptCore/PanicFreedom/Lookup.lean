import BeaconcryptCore.PanicFreedom.Control

/-!
# Panic freedom of material lookups

Logical lookup and material lookup each guard their array index. The resulting operations return normally even when the logical and material arrays disagree.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace beaconcrypt_core.ratchet

/-- Material lookup is total without logical/material correspondence premises. -/
theorem refined.refined_receive_key_total {SendChain ReceiveChain Material : Type}
    (state : refined.RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64) :
    ∃ r, refined.refined_receive_key state sequence = ok r := by
  obtain ⟨slot, hslot⟩ := control.lookup_receive_key_total state.control sequence
  simp only [refined.refined_receive_key, hslot, bind_tc_ok]
  cases slot with
  | none => exact ⟨_, rfl⟩
  | some slot =>
    simp only [lift, control.capacity_eq_ok, bind_tc_ok]
    by_cases hcap : UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64
    · simpa only [if_pos hcap, RustM.ok.injEq] using Exists.intro core.option.Option.None rfl
    · have hi : (UScalar.cast UScalarTy.Usize slot).val < state.receive_slots.length := by scalar_tac
      simp only [if_neg hcap, control.array_index_eq_ok _ _ hi, core.option.Option.as_ref, bind_tc_ok]
      cases state.receive_slots.val[(UScalar.cast UScalarTy.Usize slot).val] <;>
        simp only [bind_tc_ok] <;> first | exact ⟨_, rfl⟩ | split_ifs <;> exact ⟨_, rfl⟩

/-- Indexed material lookup is total without logical/material correspondence premises. -/
theorem refined.RefinedRatchet.receive_entry_at_total {SendChain ReceiveChain Material : Type}
    (state : refined.RefinedRatchet SendChain ReceiveChain Material) (slot : Std.U8) :
    ∃ r, refined.RefinedRatchet.receive_entry_at state slot = ok r := by
  obtain ⟨sequence, hsequence⟩ := control.RatchetState.receive_key_at_total state.control slot
  simp only [refined.RefinedRatchet.receive_entry_at, hsequence, bind_tc_ok]
  cases sequence with
  | none => exact ⟨_, rfl⟩
  | some sequence =>
    simp only [lift, control.capacity_eq_ok, bind_tc_ok]
    by_cases hcap : UScalar.cast UScalarTy.Usize slot ≥ UScalar.cast UScalarTy.Usize 50#u64
    · simpa only [if_pos hcap, RustM.ok.injEq] using Exists.intro core.option.Option.None rfl
    · have hi : (UScalar.cast UScalarTy.Usize slot).val < state.receive_slots.length := by scalar_tac
      simp only [if_neg hcap, control.array_index_eq_ok _ _ hi, core.option.Option.as_ref, bind_tc_ok]
      cases state.receive_slots.val[(UScalar.cast UScalarTy.Usize slot).val] <;>
        simp only [bind_tc_ok] <;> first | exact ⟨_, rfl⟩ | split_ifs <;> exact ⟨_, rfl⟩

/-- Concrete indexed material lookup inherits the guarded lookup guarantee. -/
theorem concrete.ConcreteRatchetKernel.receive_entry_at_total
    (state : concrete.ConcreteRatchetKernel) (slot : Std.U8) :
    ∃ r, concrete.ConcreteRatchetKernel.receive_entry_at state slot = ok r :=
  refined.RefinedRatchet.receive_entry_at_total state.refined slot

end beaconcrypt_core.ratchet
