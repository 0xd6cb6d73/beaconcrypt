-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules

/-! Private ML count normalization retains the complete shared platform state. Both original-input stability and normalized continuation equality are checked over the exact packed native/platform state; no whole-profile count-independence law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformPackedState (pack)
variable {source : RegistrationNativeMldsa.Source} {Native Platform Value Next : Type}

def project (projection : Native → Native) : Native × Platform → Native × Platform := Prod.map projection id
abbrev Correct (projection : Native → Native) (work : StateT Native (M source Platform) Value) : Prop :=
  RegistrationNativeMldsaCountRules.Correct (project projection) (pack work)

private theorem idempotent (projection : Native → Native) (law : ∀ before, projection (projection before) = projection before)
    (before : Native × Platform) : project projection (project projection before) = project projection before := by
  rcases before with ⟨native, platform⟩
  simp only [project, Prod.map, id_eq, law]

theorem pure (projection : Native → Native) (law : ∀ before, projection (projection before) = projection before) (value : Value) :
    Correct (source := source) (Platform := Platform) projection (pure value : StateT Native (M source Platform) Value) := by
  unfold Correct
  rw [RegistrationNativePlatformPackedState.pure_pack]
  exact RegistrationNativeMldsaCountRules.pure _ (idempotent projection law) value

theorem bind (projection : Native → Native) (work : StateT Native (M source Platform) Value)
    (next : Value → StateT Native (M source Platform) Next) (first : Correct projection work)
    (rest : ∀ value, Correct projection (next value)) : Correct projection (work >>= next) := by
  unfold Correct
  rw [RegistrationNativePlatformPackedState.bind_pack]
  exact RegistrationNativeMldsaCountRules.bind _ _ _ first rest

theorem simulate {I : Type} {spec : OracleSpec I} (projection : Native → Native)
    (law : ∀ before, projection (projection before) = projection before)
    (handler : QueryImpl spec (StateT Native (M source Platform)))
    (allowed : ∀ query, Correct projection (handler query)) (work : OracleComp spec Value) :
    Correct projection (simulateQ handler work) := by
  unfold Correct
  rw [RegistrationNativePlatformPackedState.simulate_pack]
  exact RegistrationNativeMldsaCountRules.simulate _ (idempotent projection law) _ allowed work

private theorem pack_lift (work : StateT Native (StateT Platform ProbComp) Value) :
    pack (RegistrationNativePlatformMldsaProgram.lift (source := source) work) =
      RegistrationNativeMldsaProgram.liftState (pack work) := by
  funext before
  simp only [pack, RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run, simulateQ_map]

theorem closed (projection : Native → Native) (work : StateT Native (StateT Platform ProbComp) Value)
    (stable : RegistrationNativeKemCounterIndependence.Stable (project projection) (pack work)) :
    Correct projection (RegistrationNativePlatformMldsaProgram.lift (source := source) work) := by
  unfold Correct
  rw [pack_lift]
  exact RegistrationNativeMldsaCountRules.closed _ _ stable

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

theorem inject (projection : Native → Native)
    (work : StateT Native (OracleComp (RegistrationNativeMldsaProgram.Spec source)) Value)
    (good : RegistrationNativeMldsaCountRules.Correct projection work) :
    Correct (Platform := Platform) projection (RegistrationNativePlatformMldsaProgram.inject work) := by
  constructor
  · intro before
    have same := congrArg (fun action => (fun result => (result.1, (result.2, before.2))) <$> action) (good.1 before.1)
    simpa only [pack, RegistrationNativePlatformMldsaProgram.inject, StateT.run, lift_apply,
      Functor.map_map, project, Prod.map, id_eq] using same
  · intro before
    have same := congrArg (fun action => (fun result => (result.1, (result.2, before.2))) <$> action) (good.2 before.1)
    simpa only [pack, RegistrationNativePlatformMldsaProgram.inject, StateT.run, lift_apply,
      RegistrationNativeMldsaCountMap.transform, simulateQ_map, Functor.map_map, project, Prod.map, id_eq] using same
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

/-- Actual public platform work cannot inspect the native accounting coordinates and retains its literal complete external poststate. -/
theorem external (projection : Native → Native) (law : ∀ before, projection (projection before) = projection before)
    (work : StateT Platform ProbComp Value) :
    Correct (source := source) projection
      (RegistrationNativePlatformMldsaProgram.lift (StateT.lift work : StateT Native (StateT Platform ProbComp) Value)) := by
  apply closed
  intro before
  simp only [pack, StateT.run, lift_apply, map_apply, Functor.map_map, project, Prod.map, id_eq, law]

/-- Ordinary native source macros inherit their checked input independence while retaining the exact separate external state. -/
theorem native (projection : Native → Native) (work : StateT Native ProbComp Value)
    (stable : RegistrationNativeKemCounterIndependence.Stable projection work) :
    Correct (source := source) (Platform := Platform) projection
      (RegistrationNativePlatformMldsaProgram.lift
        (fun before => simulateQ RegistrationNativePlatformMldsaProgram.coins (work.run before))) := by
  have same : RegistrationNativePlatformMldsaProgram.lift (source := source)
      (fun before => simulateQ (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) (work.run before)) =
      RegistrationNativePlatformMldsaProgram.inject (RegistrationNativeMldsaProgram.liftState work) := by
    funext before previous
    change RegistrationNativeMldsaProgram.lift
      ((simulateQ RegistrationNativePlatformMldsaProgram.coins (work.run before)).run previous) = _
    rw [RegistrationNativePlatformMldsaProgram.lift_coins]
    simp only [StateT.run, lift_apply, RegistrationNativePlatformMldsaProgram.inject,
      RegistrationNativeMldsaProgram.liftState, RegistrationNativeMldsaProgram.lift, simulateQ_map]
  rw [same]
  exact inject projection _ (RegistrationNativeMldsaCountRules.closed projection work stable)

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.inject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.inject

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.external

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules.native
