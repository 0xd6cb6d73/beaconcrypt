-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck

/-! The ordinary suffix-key tester retains the actual oracle state and its fresh prefix draw. These source equations apply to the real fixed family and the ideal persistent table without substituting an independent earlier answer. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource
open RegistrationNativeSuffixKeyPrf (Prefix Secret Oracle Spec value realImpl idealImpl)
open RegistrationNativeSuffixKeyCheck (Output coins Matches testAt test)
variable {Value : Type}
attribute [local irreducible] RegistrationNativeSuffixKeyPrf.value PqxdhServerAuthKeySchedule.fromRoot

/-- All real tester coins are the same literal probability computation. -/
theorem real_coins (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (key : Secret) (work : ProbComp Value) :
    simulateQ (realImpl source key) (simulateQ coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : realImpl source key ∘ₛ coins = QueryImpl.ofLift unifSpec ProbComp := by funext query; rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- Every ideal tester coin preserves the whole persistent prefix table. -/
theorem ideal_coins (work : ProbComp Value) (cache : Oracle.QueryCache) :
    (simulateQ idealImpl (simulateQ coins work)).run cache = (fun result => (result, cache)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : idealImpl ∘ₛ coins = (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Oracle.QueryCache ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

/-- The real terminal checker always recognizes a true guessed key, while keeping its fresh prefix draw. -/
theorem real_test (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (key : Secret) (guesses : List Secret) (member : key ∈ guesses) :
    simulateQ (realImpl source key) (test source guesses) = (fun _ : Prefix => true) <$> ($ᵗ Prefix) := by
  simp only [test, simulateQ_bind, real_coins, RegistrationNativeSuffixKeyCheck.real_at source key guesses member,
    bind_pure_comp]

/-- A fresh ideal query samples its complete108-byte answer and records exactly that answer in the same persistent table. -/
theorem ideal_at (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (head : Prefix) (cache : Oracle.QueryCache) (fresh : cache head = none) :
    (simulateQ idealImpl (testAt source guesses head)).run cache =
      (fun answer : Output => (decide (Matches source guesses head answer), cache.cacheQuery head answer)) <$> ($ᵗ Output) := by
  change (do let answer ← Oracle.randomOracle head; pure (decide (Matches source guesses head answer))).run cache = _
  rw [StateT.run_bind, QueryImpl.withCaching_run_none _ fresh]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  rfl

/-- The actual randomized ideal checker draws its fresh prefix before its one table request. -/
theorem ideal_test (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (cache : Oracle.QueryCache) :
    (simulateQ idealImpl (test source guesses)).run' cache =
      ($ᵗ Prefix >>= fun head => (simulateQ idealImpl (testAt source guesses head)).run' cache) := by
  simp only [test, simulateQ_bind, StateT.run'_eq, StateT.run_bind, ideal_coins, bind_map_left, map_bind]

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.real_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.real_coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.real_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.real_test
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_at
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource.ideal_test
