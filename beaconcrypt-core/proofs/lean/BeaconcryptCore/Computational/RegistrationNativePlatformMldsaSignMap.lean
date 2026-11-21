-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap

/-! Complete named signing requests translate across source-key representations while both native and public platform states remain threaded. Ordinary source/platform computation is unchanged. Generation is handled separately by the actual dynamic key table. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap
open RegistrationNativeMldsaMap (Map)
open RegistrationNativePlatformMldsaProgram (M)
variable {left right : RegistrationNativeMldsa.Source} {Native Platform Value Next : Type}

def transform (mapping : Map left right) (work : StateT Native (M left Platform) Value) :
    StateT Native (M right Platform) Value := fun before previous =>
  RegistrationNativeMldsaSignMap.transform mapping ((work.run before).run previous)

theorem pure (mapping : Map left right) (value : Value) :
    transform mapping (Pure.pure value : StateT Native (M left Platform) Value) = Pure.pure value := by
  funext before previous
  rfl

theorem bind (mapping : Map left right) (work : StateT Native (M left Platform) Value)
    (next : Value → StateT Native (M left Platform) Next) :
    transform mapping (work >>= next) = (transform mapping work >>= fun value => transform mapping (next value)) := by
  funext before previous
  simp only [transform, StateT.run_bind, RegistrationNativeMldsaSignMap.transform, simulateQ_bind]
  rfl

theorem hom (mapping : Map left right) :
    Cslib.IsMonadHom (StateT Native (M left Platform)) (StateT Native (M right Platform)) (transform mapping) :=
  .mk' (pure mapping) (bind mapping)

/-- Actual closed ordinary platform operations retain the same full state under key-only translation. -/
theorem lift (mapping : Map left right) (work : StateT Native (StateT Platform ProbComp) Value) :
    transform mapping (RegistrationNativePlatformMldsaProgram.lift work) = RegistrationNativePlatformMldsaProgram.lift work := by
  funext before previous
  exact RegistrationNativeMldsaSignMap.transform_lift mapping ((work.run before).run previous)

/-- Existing reified native signing components translate before injection into the separate platform state. -/
theorem inject (mapping : Map left right)
    (work : StateT Native (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Value) :
    transform (Platform := Platform) mapping (RegistrationNativePlatformMldsaProgram.inject work) =
      RegistrationNativePlatformMldsaProgram.inject (RegistrationNativeMldsaSignMap.transformState mapping work) := by
  funext before previous
  change simulateQ (RegistrationNativeMldsaSignMap.translation mapping) (do
    let value ← work.run before
    Pure.pure (value, previous)) = (do
      let value ← RegistrationNativeMldsaSignMap.transform mapping (work.run before)
      Pure.pure (value, previous))
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.hom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.inject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSignMap.inject
