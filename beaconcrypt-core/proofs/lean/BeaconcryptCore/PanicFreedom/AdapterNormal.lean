-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs

/-! Safety-only composition for direct extracted computations. A normal result may contain a protocol rejection or a dependency error. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterNormal

abbrev Normal {A : Type} (work : RustM A) : Prop := ∃ value, work = ok value

abbrev Ensures {A : Type} (work : RustM A) (invariant : A → Prop) : Prop :=
  ∃ value, work = ok value ∧ invariant value

theorem ensures_normal {A : Type} {work : RustM A} {invariant : A → Prop}
    (safe : Ensures work invariant) : Normal work :=
  safe.imp fun _ returned => returned.1

theorem ensures_ok {A : Type} (value : A) (invariant : A → Prop)
    (valid : invariant value) : Ensures (ok value) invariant := ⟨value, rfl, valid⟩

theorem normal_ok {A : Type} (value : A) : Normal (ok value) := ⟨value, rfl⟩

theorem normal_bind {A B : Type} (work : RustM A) (next : A → RustM B)
    (first : Normal work) (later : ∀ value, Normal (next value)) :
    Normal (work >>= next) := by
  obtain ⟨value, returned⟩ := first
  simpa only [returned, bind_tc_ok] using later value

theorem normal_bind_at {A B : Type} (work : RustM A) (next : A → RustM B)
    (first : Normal work) (later : ∀ value, work = ok value → Normal (next value)) :
    Normal (work >>= next) := by
  obtain ⟨value, returned⟩ := first
  simpa only [returned, bind_tc_ok] using later value returned

theorem ensures_bind_at {A B : Type} (work : RustM A) (next : A → RustM B)
    (invariant : B → Prop) (first : Normal work)
    (later : ∀ value, work = ok value → Ensures (next value) invariant) :
    Ensures (work >>= next) invariant := by
  obtain ⟨value, returned⟩ := first
  simpa only [returned, bind_tc_ok] using later value returned

theorem map_err_total {A E F C : Type} (callback : core.ops.function.FnOnce C E F)
    (result : core.result.Result A E) (capture : C)
    (total : ∀ error, Normal (callback.call_once capture error)) :
    Normal (core.result.Result.map_err callback result capture) := by
  cases result with
  | Ok value => exact ⟨_, rfl⟩
  | Err error =>
    obtain ⟨mapped, returned⟩ := total error
    exact ⟨.Err mapped, by simp only [core.result.Result.map_err, returned, bind_tc_ok]⟩

theorem normal_loop {S R : Type} (body : S → RustM (ControlFlow S R))
    (rank : S → Nat) (bodyTotal : ∀ state, Normal (body state))
    (progress : ∀ state next, body state = ok (.cont next) → rank next < rank state)
    (state : S) : Normal (loop body state) := by
  induction bound : rank state using Nat.strong_induction_on generalizing state with
  | h bound ih =>
    obtain ⟨decision, returned⟩ := bodyTotal state
    rw [loop.eq_def, returned]
    cases decision with
    | done result => exact normal_ok result
    | cont next => exact ih (rank next) (by simpa only [bound] using progress state next returned) next rfl

end BeaconcryptCore.PanicFreedom.AdapterNormal
