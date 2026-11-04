-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterNormal

/-! Safety-only certificates for the selected standard Result and Option plumbing. Callback normality is required only for the individual reached callback. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterStandard
open AdapterNormal

theorem pair_pure_total {A B C : Type} (pair : A × B) (next : A → B → C) :
    Normal (let (first, second) := pair; ok (next first second)) := by
  rcases pair with ⟨first, second⟩
  exact ⟨_, rfl⟩

theorem result_ok_total {A E : Type} (value : core.result.Result A E) :
    Normal (core.result.Result.ok value) := by
  cases value <;> exact ⟨_, rfl⟩

theorem option_branch_total {A : Type} (value : core.option.Option A) :
    Normal (core.option.Option.Insts.CoreOpsTry_traitTry.branch value) := by
  cases value <;> exact ⟨_, rfl⟩

theorem option_residual_total (A : Type) (value : core.option.Option core.convert.Infallible)
    (absent : value = .none) :
    Normal (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual A value) := by
  subst value
  exact ⟨_, rfl⟩

theorem option_residual_of_branch {A B : Type} (value : core.option.Option A)
    (residual : core.option.Option core.convert.Infallible)
    (branched : core.option.Option.Insts.CoreOpsTry_traitTry.branch value =
      ok (.Break residual)) :
    Normal (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual) := by
  cases value <;> cases branched
  exact ⟨_, rfl⟩

theorem option_ref_total {A : Type} (value : core.option.Option A) :
    Normal (core.option.Option.as_ref value) := by
  cases value <;> exact ⟨_, rfl⟩

theorem option_is_some_total {A : Type} (value : core.option.Option A) :
    Normal (core.option.Option.is_some value) := by
  cases value <;> exact ⟨_, rfl⟩

theorem option_map_total {A B C : Type} (callback : core.ops.function.FnOnce C A B)
    (value : core.option.Option A) (capture : C)
    (normal : ∀ input, Normal (callback.call_once capture input)) :
    Normal (core.option.Option.map callback value capture) := by
  cases value with
  | none => exact ⟨_, rfl⟩
  | some input =>
    obtain ⟨result, returned⟩ := normal input
    exact ⟨.some result, by simp only [core.option.Option.map, returned, bind_tc_ok]⟩

theorem option_and_then_total {A B C : Type}
    (callback : core.ops.function.FnOnce C A (core.option.Option B))
    (value : core.option.Option A) (capture : C)
    (normal : ∀ input, Normal (callback.call_once capture input)) :
    Normal (core.option.Option.and_then callback value capture) := by
  cases value with
  | none => exact ⟨_, rfl⟩
  | some input => exact normal input

end BeaconcryptCore.PanicFreedom.AdapterStandard
