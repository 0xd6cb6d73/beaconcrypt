-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenService

/-! The actual seed-free service uses at most44 byte draws per admitted material request and no World capability. These are structural AST bounds, independent of any distributional or source-state projection. Hidden seed draws occur only in the separate World installation handler. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds
open RegistrationNativeHiddenService (State coins material demand)
open RegistrationNativeRelatedFamily (Message)
open PqxdhDeploymentHiddenLayout (Material)
open PqxdhRecordLiftInterface (Slot EnvEffects)
variable {n : Nat}

def IsCapability : (EnvEffects n).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsCapability (n := n)) := fun query => by
  cases query <;> simp only [IsCapability] <;> infer_instance

private theorem coins_bound {Value : Type} (work : ProbComp Value) (count : Nat)
    (bounded : work.IsTotalQueryBound count) : (simulateQ (coins (n := n)) work).IsTotalQueryBound count := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) (fun _ => True) _ count
    ((isQueryBoundP_true_iff _ _).mpr bounded)
  intro query
  simp [coins, isQueryBoundP_query_iff]

private theorem coins_free {Value : Type} (work : ProbComp Value) :
    (simulateQ (coins (n := n)) work).IsQueryBoundP IsCapability 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [coins, IsCapability, isQueryBoundP_query_iff]

/-- Every material read performs at most44 actual byte draws; cached aliases perform none. -/
theorem material_bound (slot : Slot n) (before : State n) :
    ((material slot).run before).IsTotalQueryBound 44 := by
  cases cached : before.materials slot with
  | some value => rw [RegistrationNativeHiddenService.material_hit slot before value cached]; trivial
  | none =>
      rw [RegistrationNativeHiddenService.material_miss slot before cached]
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact coins_bound _ 44 PqxdhDeploymentHiddenLayout.material_bound

/-- The material sampler cannot invoke a hash, installation, presence test or any other World capability. -/
theorem material_free (slot : Slot n) (before : State n) :
    ((material slot).run before).IsQueryBoundP IsCapability 0 := by
  cases cached : before.materials slot with
  | some value => rw [RegistrationNativeHiddenService.material_hit slot before value cached]; trivial
  | none =>
      rw [RegistrationNativeHiddenService.material_miss slot before cached, isQueryBoundP_map_iff]
      exact coins_free _

attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot

/-- Every actual demand branch retains the44-draw bound, including unprepared, off-protected, alias-hit and capacity-refused requests. -/
theorem demand_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State n) :
    ((demand source input inside message).run before).IsTotalQueryBound 44 := by
  simp only [demand, StateT.run]
  split
  · cases realized : input message with
    | none => simp only []; trivial
    | some bytes =>
        simp only []
        split
        · cases allocated : RegistrationNativeHiddenService.reserve bytes { before with demands := before.demands + 1 } with
          | mk selected after => cases selected with
            | none => trivial
            | some slot =>
                simp only [IsTotalQueryBound, isQueryBound_map_iff]
                exact material_bound slot after
        · trivial
  · trivial

/-- The full service request performs no World capability read or installation; the native continuation owns the later hidden-reference installation. -/
theorem demand_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State n) :
    ((demand source input inside message).run before).IsQueryBoundP IsCapability 0 := by
  simp only [demand, StateT.run]
  split
  · cases realized : input message with
    | none => simp only []; trivial
    | some bytes =>
        simp only []
        split
        · cases allocated : RegistrationNativeHiddenService.reserve bytes { before with demands := before.demands + 1 } with
          | mk selected after => cases selected with
            | none => trivial
            | some slot =>
                rw [isQueryBoundP_map_iff]
                exact material_free slot after
        · trivial
  · trivial

end BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.material_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.material_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.material_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.material_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.demand_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.demand_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.demand_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds.demand_free
