-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerationGhost

/-! Public generation tracking lifts through arbitrary stateful native controllers. The original controller sees the same primitive replies and native state. The extra state contains only the actual generation counter and selected public key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGenerationGhost (run)
variable {S V W : Type} (source : Source)

private theorem bind_apply {m : Type → Type} [Monad m] {State A B : Type}
    (work : StateT State m A) (next : A → StateT State m B) (before : State) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private theorem map_apply {State A B : Type} (observer : A → B)
    (work : StateT State (OracleComp (Spec (handleSource source))) A) (before : State) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

def arrange (result : (V × S) × RegistrationNativeMldsaGenerationGhost.State) :=
  (result.1.1, (result.1.2, result.2))

def track (selected : Nat) (work : StateT S (OracleComp (Spec (handleSource source))) V) :
    StateT (S × RegistrationNativeMldsaGenerationGhost.State) (OracleComp (Spec (handleSource source))) V :=
  fun before => arrange <$> run source selected (work.run before.1) before.2

/-- Pure source state updates add no tracked primitive call. -/
theorem pure (selected : Nat) (value : V) : track source selected (pure value : StateT S _ V) = pure value := by
  funext before
  simp only [track, StateT.run_pure, run, simulateQ_pure, map_pure, arrange]
  rfl

/-- Tracking retains every original stateful continuation and optional failure branch. -/
theorem bind (selected : Nat) (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (next : V → StateT S (OracleComp (Spec (handleSource source))) W) :
    track source selected (work >>= next) = (track source selected work >>= fun value => track source selected (next value)) := by
  funext before
  simp only [track, StateT.run, bind_apply, run, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr
  intro middle
  rfl

/-- Source-value mapping commutes with public generation tracking. -/
theorem map (selected : Nat) (observer : V → W) (work : StateT S (OracleComp (Spec (handleSource source))) V) :
    track source selected (observer <$> work) = observer <$> track source selected work := by
  funext before
  simp only [track, StateT.run_map, map_apply, run, simulateQ_map, Functor.map_map]
  rfl

/-- The complete original native controller is recovered by erasing only the public generation ghost. -/
theorem erase (selected : Nat) (work : StateT S (OracleComp (Spec (handleSource source))) V)
    (current : S) (ghost : RegistrationNativeMldsaGenerationGhost.State) :
    (fun result => (result.1, result.2.1)) <$> (track source selected work).run (current, ghost) = work.run current := by
  simpa only [track, StateT.run, Functor.map_map, arrange] using
    RegistrationNativeMldsaGenerationGhost.erase source selected (work.run current) ghost

/-- The count-free source transformation commutes with the complete tracked stateful controller. -/
theorem normalized (selected : Nat) (work : StateT S (OracleComp (Spec (handleSource source))) V) :
    RegistrationNativeMldsaCountMap.transformState (track source selected work) =
      track source selected (RegistrationNativeMldsaCountMap.transformState work) := by
  funext before
  simp only [RegistrationNativeMldsaCountMap.transformState, track, StateT.run,
    RegistrationNativeMldsaCountMap.transform, simulateQ_map]
  exact congrArg (fun program => arrange <$> program)
    (RegistrationNativeMldsaGenerationGhost.normalized source selected (work.run before.1) before.2).symm
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState.normalized
