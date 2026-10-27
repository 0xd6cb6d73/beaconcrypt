import BeaconcryptCore.PanicFreedom.Control

/-! Exact planner shape and retained-key bounds after separating the uncached target derivation. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.control

/-- Every plan returns its requested target or an empty rejection, with at most fifty retained skips and one uncached target step. -/
theorem plan_receive_shape (state : RatchetState) (target : Std.U64) :
    ∃ plan, plan_receive_until state target = ok plan ∧ plan.derivations.val ≤ 51 ∧
      match plan.sequence with
      | .None => plan.derivations = 0#u64
      | .Some planned => planned = target ∧
          (target.val ≤ state.receive_sequence.val → plan.derivations = 0#u64) ∧
          (state.receive_sequence.val < target.val →
            plan.derivations.val = target.val - state.receive_sequence.val ∧
            0 < plan.derivations.val ∧
            state.receive_cache.len.val + (plan.derivations.val - 1) ≤ 50) := by
  by_cases hpast : target.val ≤ state.receive_sequence.val
  · refine ⟨_, plan_receive_until_replay state target hpast, by simp, rfl, fun _ => rfl, ?_⟩
    intro hf
    omega
  · by_cases hcapacity : state.receive_cache.len.val + (target.val - state.receive_sequence.val - 1) ≤ 50
    · obtain ⟨derivations, hplan, hcount⟩ := plan_receive_until_accept state target (by omega) hcapacity
      refine ⟨_, hplan, by simp only; omega, rfl, ?_, ?_⟩
      · intro hcontra
        omega
      · intro _
        exact ⟨hcount, by simp only; omega, by simp only; omega⟩
    · have hplan : plan_receive_until state target =
          ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
        by_cases hgap : state.receive_sequence.val + 51 < target.val
        · exact plan_receive_until_reject_of_gap_gt state target hgap
        · exact plan_receive_until_reject_of_cache_full state target (by omega) (by omega) (by omega)
      exact ⟨_, hplan, by simp, rfl⟩

/-- The current bound is genuinely fifty-one derivations: the target key is not stored in the skipped cache. -/
theorem plan_51_steps_is_admitted
    (state : RatchetState) (target : Std.U64)
    (hsequence : target.val = state.receive_sequence.val + 51)
    (hempty : state.receive_cache.len.val = 0) :
    plan_receive_until state target = ok { sequence := core.option.Option.Some target, derivations := 51#u64 } :=
  plan_receive_until_accept_51_of_empty state target hsequence hempty

end beaconcrypt_core.ratchet.control
