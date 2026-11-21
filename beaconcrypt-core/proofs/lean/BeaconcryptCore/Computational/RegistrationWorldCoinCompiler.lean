-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement

/-! Native primitive sampling and EnvEffects coin programs share their exact draws and complete non-coin World state. EnvEffects additionally charges one coin effect per draw; its difference from the native sampled counter is derived rather than silently equated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldCoinCompiler
open PqxdhRecordLiftInterface (EnvEffects effectKind)
variable {n : Nat} {Value : Type}

def eraseCoin (state : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { state with primitive := ({ state.primitive.1 with
    effects := Function.update state.primitive.1.effects .coin 0 }, state.primitive.2) }

def nativeTick (state : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { state with primitive := ({ state.primitive.1 with uniform := state.primitive.1.uniform + 1 }, state.primitive.2) }

def tick (state : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { state with primitive := ({ state.primitive.1 with
    uniform := state.primitive.1.uniform + 1
    effects := Function.update state.primitive.1.effects .coin (state.primitive.1.effects .coin + 1) }, state.primitive.2) }

def envCoin : QueryImpl unifSpec (OracleComp (EnvEffects n)) :=
  fun coin => (EnvEffects n).query (.inl coin)

noncomputable def coin : QueryImpl unifSpec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query => PqxdhRecordLiftWorld.effects (.inl query)

def nativeCoin : QueryImpl unifSpec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query => PqxdhRecordLiftWorld.sampled (unifSpec.query query)

/-- Each EnvEffects coin preserves its literal uniform query and advances precisely its two analysis counters. -/
theorem coin_run (query : Nat) (state : PqxdhRecordLiftWorld.State n) :
    (coin query).run state = (fun reply => (reply, tick state)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [coin, PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, PqxdhRecordLiftWorld.chargeEffect,
    effectKind, StateT.run, simulateQ_spec_query, PqxdhRecordLiftWorld.countCoin, bind_pure_comp,
    Functor.map_map]
  rfl

/-- Native sampling advances only the actual uniform counter. -/
theorem nativeCoin_run (query : Nat) (state : PqxdhRecordLiftWorld.State n) :
    (nativeCoin query).run state = (fun reply => (reply, nativeTick state)) <$> (unifSpec.query query : ProbComp _) := by
  simp only [nativeCoin, PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_spec_query,
    PqxdhRecordLiftWorld.countCoin, bind_pure_comp, Functor.map_map]
  rfl

private theorem countCoin_run (query count : Nat) :
    (PqxdhRecordLiftWorld.countCoin query).run count =
      (fun reply => (reply, count + 1)) <$> (unifSpec.query query : ProbComp _) := rfl

private theorem sampled_run (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.sampled draw).run state =
      (fun result => (result.1, { state with primitive :=
        ({ state.primitive.1 with uniform := result.2 }, state.primitive.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.countCoin draw).run state.primitive.1.uniform := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp]

/-- Replacing the native sampler by its one-query interpreter keeps the full source computation and World. -/
theorem native_program (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    (simulateQ nativeCoin draw).run state = (PqxdhRecordLiftWorld.sampled draw).run state := by
  induction draw using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, nativeCoin_run, bind_map_left, sampled_run]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, countCoin_run,
        bind_map_left, map_bind]
      apply bind_congr
      intro reply
      rw [ih, sampled_run]
      rfl

/-- Erasing only the additional coin-effect ledger commutes with the native sampler. -/
theorem sampled_erase (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$> (PqxdhRecordLiftWorld.sampled draw).run state =
      (PqxdhRecordLiftWorld.sampled draw).run (eraseCoin state) := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq, eraseCoin]

/-- The actual environment and native draws have the same complete World after forgetting only their differing coin-effect counter. -/
theorem coins_erase (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$>
      (simulateQ PqxdhRecordLiftWorld.effects (simulateQ envCoin draw)).run state =
    Prod.map id eraseCoin <$> (PqxdhRecordLiftWorld.sampled draw).run state := by
  have step : ∀ query state, Prod.map id eraseCoin <$> (coin (n := n) query).run state =
      (nativeCoin query).run (eraseCoin state) := by
    intro query state
    rw [coin_run, nativeCoin_run, Functor.map_map]
    congr 1
    funext reply
    simp only [Prod.map, id_eq, eraseCoin, tick, nativeTick, Function.update_idem]
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq coin nativeCoin eraseCoin step draw state
  have composed : PqxdhRecordLiftWorld.effects (n := n) ∘ₛ envCoin = coin := by
    funext query
    simp only [QueryImpl.apply_compose, envCoin, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, composed, projected, native_program, sampled_erase]

/-- The extra EnvEffects coin charge equals the number of actual underlying uniform draws on every reached branch. -/
theorem coin_accounting (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n)
    (result : Value × PqxdhRecordLiftWorld.State n)
    (reached : result ∈ support ((simulateQ coin draw).run state)) :
    result.2.primitive.1.effects .coin + state.primitive.1.uniform =
      state.primitive.1.effects .coin + result.2.primitive.1.uniform := by
  induction draw using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, coin_run, bind_map_left, mem_support_bind_iff] at reached
      obtain ⟨reply, _, tail⟩ := reached
      have counted := ih reply (tick state) result tail
      simp only [tick, Function.update_self] at counted
      omega

/-- The environment coin lift executes the literal coin interpreter on every source reply branch. -/
theorem env_program (draw : ProbComp Value) (state : PqxdhRecordLiftWorld.State n) :
    (simulateQ PqxdhRecordLiftWorld.effects (simulateQ envCoin draw)).run state =
      (simulateQ coin draw).run state := by
  have composed : PqxdhRecordLiftWorld.effects (n := n) ∘ₛ envCoin = coin := by
    funext query
    simp only [QueryImpl.apply_compose, envCoin, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, composed]

/-- Primitive sampling transports its actual total draw cap to EnvEffects coin calls and makes no hash or administrative query. -/
theorem env_bound (draw : ProbComp Value) (cap : Nat) (bounded : draw.IsTotalQueryBound cap)
    (kind : PqxdhRecordLiftInterface.EffectKind) :
    (simulateQ (envCoin (n := n)) draw).IsQueryBoundP (fun query => effectKind query = kind)
      (if kind = .coin then cap else 0) := by
  by_cases selected : kind = .coin
  · subst kind
    simp only [ite_true]
    exact RawCtxSourceOpen.simulate_bound envCoin (fun _ => True) _ draw cap
      ((isQueryBoundP_true_iff _ _).mpr bounded)
      (fun query => by simp [envCoin, isQueryBoundP_query_iff, effectKind])
  · rw [ite_eq_right selected]
    exact RawCtxSourceOpen.simulate_bound envCoin (fun _ => False) _ draw 0 (isQueryBoundP_false _ 0)
      (fun query => by simp [envCoin, isQueryBoundP_query_iff, effectKind, Ne.symm selected])

end BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coin_run
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.nativeCoin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.nativeCoin_run
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.native_program
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.sampled_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.sampled_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coins_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coins_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coin_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.coin_accounting

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.env_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.env_program
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.env_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldCoinCompiler.env_bound
