-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativeKeyRelabel

/-! The actual phase compiler makes no protected key-table query at preparation, and at most one at an admitted material demand. These bounds count the original adaptive demand commands, including failures, rather than assuming a first-touch cap for an unrelated table client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyBounds
open RegistrationNativeKeyPhases (Meta State Value prepareMeta demandMeta erased)
open RegistrationNativeKeyCompiler (KeySpec liftProb compiler client sourceInterpreter interpret)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRegistrationJointKemSecondEntry (IsValue)
open PqxdhServerAuthKeySchedule (Output)

def IsDemand : RegistrationNativeKeyPhases.Spec.Domain → Prop
  | .inr (.demand _) => True
  | _ => False

instance demandDecidable : DecidablePred IsDemand := fun query => by
  cases query with
  | inl coin => exact isFalse id
  | inr request => cases request with
    | prepare message => exact isFalse id
    | demand message => exact isTrue trivial

theorem lift_free {Result : Type} (work : StateT Meta ProbComp Result) (before : Meta) :
    ((liftProb work).run before).IsQueryBoundP (IsValue (D := Pqxdh.Bytes) (R := Output)) 0 := by
  change (simulateQ RegistrationNativeKeyCompiler.coins (work.run before)).IsQueryBoundP _ 0
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeKeyCompiler.coins, isQueryBoundP_query_iff, IsValue]

theorem compiler_free (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : RegistrationNativeKeyPhases.Spec.Domain) (free : ¬ IsDemand query) (before : Meta) :
    ((compiler source input inside query).run before).IsQueryBoundP
      (IsValue (D := Pqxdh.Bytes) (R := Output)) 0 := by
  cases query with
  | inl coin => exact lift_free _ _
  | inr request => cases request with
    | prepare message => exact lift_free _ _
    | demand message => exact False.elim (free trivial)

theorem compiler_demand (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : Meta) :
    ((compiler source input inside (.inr (.demand message))).run before).IsQueryBoundP
      (IsValue (D := Pqxdh.Bytes) (R := Output)) 1 := by
  unfold compiler
  rw [StateT.run_bind]
  rw [← Nat.zero_add 1]
  apply isQueryBoundP_bind (lift_free _ _)
  intro result _possible
  cases result.1 with
  | none => trivial
  | some selected =>
    rcases selected with ⟨bytes, protectedInput⟩
    cases protectedInput
    · trivial
    · simp only [ite_true, StateT.run_map, StateT.run_lift, isQueryBoundP_map_iff]
      simp [isQueryBoundP_query_iff, IsValue]

/-- Every actual source demand accounts for at most one protected material read; preparation and ordinary coins account for none. -/
theorem client_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp RegistrationNativeKeyPhases.Spec Result) (count : Nat)
    (bounded : work.IsQueryBoundP IsDemand count) (before : Meta) :
    (client source input inside work before).IsQueryBoundP (IsValue (D := Pqxdh.Bytes) (R := Output)) count := by
  unfold client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted state
    cases query with
    | inl coin => exact False.elim counted
    | inr request => cases request with
      | prepare message => exact False.elim counted
      | demand message => exact compiler_demand source input inside message state
  · intro query free state
    exact compiler_free source input inside query free state

/-- The PRK-free client preserves the ordinary final source bit after forgetting only private PRK state and scheduling metadata. -/
theorem client_source {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp RegistrationNativeKeyPhases.Spec Result) (before : State) :
    (simulateQ (sourceInterpreter source hmac) (client source input inside work before.1)).run' before.2 =
      (simulateQ (erased source hmac input inside) work).run' before := by
  have raw := congrFun (RegistrationNativeKeyCompiler.program_source source hmac input inside work) before
  have final := congrArg (fun experiment => Prod.fst <$> experiment) raw
  simp only [client, StateT.run'_eq, simulateQ_map]
  rw [StateT.run_map]
  simpa only [interpret, Functor.map_map, StateT.run] using final

end BeaconcryptCore.Computational.RegistrationNativeKeyBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBounds.lift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBounds.lift_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBounds.compiler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBounds.compiler_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBounds.compiler_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBounds.compiler_demand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBounds.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBounds.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBounds.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBounds.client_source
