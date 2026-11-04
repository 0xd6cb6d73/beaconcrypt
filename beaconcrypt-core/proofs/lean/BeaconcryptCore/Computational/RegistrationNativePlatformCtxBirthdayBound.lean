-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCacheCompiler
/-! The literal count-bearing physical CTX backend has one shared birthday bound after an arbitrary actual empty/singleton warm cache, retaining all adaptive replies, input aliases, complete journals and public coins. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBound
open RegistrationNativePlatformCtxBackend (Spec State)
open RegistrationNativePlatformCtxBirthdayCompiler (compiler)
open RegistrationNativePlatformCtxBirthdayBudget (IsHash)
open PqxdhRecordFactsCollision (History interpreter)
open PqxdhRecordFactsCollisionCache (Collision)
variable {A : Type}

/-- One actual warm physical cache pays each unordered digest pair once; the named request cap counts all hash calls rather than owners or independent substitute games. -/
theorem physical_bound (work : OracleComp Spec A) (future : Nat)
    (bounded : work.IsQueryBoundP IsHash future) (before : State)
    (warm : RegistrationNativePlatformCtxBirthdayCache.Warm before.1) :
    𝒟[(fun result : A × State => @decide (Collision (fun _ => true) result.2.1) (Classical.propDecidable _)) <$>
      (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before] {true} ≤
      ((future + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  classical
  let _ : MeasurableSpace CtxRomAuth.CtxDigest := ⊤
  let _ : DiscreteMeasurableSpace CtxRomAuth.CtxDigest := ⟨fun _ => by simp⟩
  obtain ⟨history, good, clean, prior⟩ := RegistrationNativePlatformCtxBirthdayCacheCompiler.warm_good before warm
  have tight := RegistrationNativePlatformCtxBirthdayDraw.run_bound ((simulateQ compiler work).run before) future
    (RegistrationNativePlatformCtxBirthdayBudget.compiler_bound work future bounded before) history clean
  have potentialBound : RegistrationNativePlatformCtxBirthdayDraw.potential future (history.targets.length + history.ordinary.length) ≤
      (future + 1).choose 2 := by
    unfold RegistrationNativePlatformCtxBirthdayDraw.potential
    calc
      future * (history.targets.length + history.ordinary.length) + future.choose 2 ≤ future * 1 + future.choose 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left future prior) _
      _ = _ := by simp only [Nat.mul_one, Nat.choose_succ_succ, Nat.choose_one_right]
  have billed := tight.trans (mul_le_mul (Nat.cast_le.mpr potentialBound) le_rfl (by positivity) (by positivity))
  have covered :
      𝒟[(fun result : A × State => @decide (Collision (fun _ => true) result.2.1) (Classical.propDecidable _)) <$>
        (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before] {true} ≤
      𝒟[(fun result : (A × State) × History CtxRomAuth.CtxDigest => result.2.bad) <$>
        (simulateQ interpreter ((simulateQ compiler work).run before)).run history] {true} := by
    rw [← RegistrationNativePlatformCtxBirthdaySource.complete work before history, Functor.map_map]
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
    apply prEvent_mono_of_support
    intro result present collision
    exact RegistrationNativePlatformCtxBirthdayCacheCompiler.compiled_collision_detected work before history good result present
      (of_decide_eq_true collision)
  simpa only [CtxRomAuth.ctxDigest_card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using covered.trans billed
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBound.physical_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBound.physical_bound
