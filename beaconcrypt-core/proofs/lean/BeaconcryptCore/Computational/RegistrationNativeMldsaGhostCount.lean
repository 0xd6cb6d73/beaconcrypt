-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState

/-! Public generation metadata remains exact when existing native controller accounting views are lifted through tracking. Both original input independence and free count normalization are transported as checked source-program equalities. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGenerationGhost (run)
open RegistrationNativeMldsaGhostState (track arrange)
variable {S V : Type} (source : Source)

def view (projection : S → S) (before : S × RegistrationNativeMldsaGenerationGhost.State) :=
  (projection before.1, before.2)

private theorem run_map {A B : Type} (selected : Nat) (observer : A → B)
    (work : OracleComp (Spec (handleSource source)) A) (before : RegistrationNativeMldsaGenerationGhost.State) :
    run source selected (observer <$> work) before = Prod.map observer id <$> run source selected work before := by
  simp only [run, simulateQ_map, StateT.run_map]
  rfl

/-- Original source accounting independence preserves the exact learned public key and attempt ordinal. -/
theorem stable (projection : S → S) (selected : Nat)
    (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (law : RegistrationStateView.Stable projection work) :
    RegistrationStateView.Stable (view projection) (track source selected work) := by
  intro before
  have same := congrArg (fun program => arrange <$> run source selected program before.2) (law before.1)
  simp only [run_map, Functor.map_map] at same
  simpa only [track, StateT.run, Functor.map_map, Prod.map, id_eq, view, arrange] using same

/-- Free count normalization preserves actual tracked generation metadata jointly with the checked native state view. -/
theorem natural (projection : S → S) (selected : Nat)
    (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (law : RegistrationNativeMldsaCountMap.Natural projection work) :
    RegistrationNativeMldsaCountMap.Natural (view projection) (track source selected work) := by
  intro before
  have same := congrArg (fun program => arrange <$> run source selected program before.2) (law before.1)
  simp only [run_map, Functor.map_map] at same
  rw [RegistrationNativeMldsaGenerationGhost.normalized] at same
  simpa only [track, StateT.run, RegistrationNativeMldsaCountMap.transform,
    simulateQ_map, Functor.map_map, Prod.map, id_eq, view, arrange] using same

/-- Every previously checked actual native controller supplies both tracked count laws without an additional primitive or source contract. -/
theorem correct (projection : S → S) (selected : Nat)
    (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (law : RegistrationNativeMldsaCountRules.Correct projection work) :
    RegistrationNativeMldsaCountRules.Correct (view projection) (track source selected work) :=
  ⟨stable source projection selected work law.1, natural source projection selected work law.2⟩
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostCount.correct
