-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsa
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-! Additive private ML generate/sign capabilities. Leaf replies carry only their result and a private count of the actual source uniform draws. The actual evaluator restores the original native or Env coin accounting exactly; later primitive-oracle substitutions must erase this accounting receipt from their public view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCapability
open RegistrationSigningShared (SignReply)
variable {n : Nat} {Value : Type}

inductive Accounting where
  | native
  | environment

inductive Request (source : RegistrationNativeMldsa.Source) where
  | generate
  | sign (credential : RegistrationNativeMldsa.Credential source) (request : registration.MldsaSigningRequest)

def Reply {source : RegistrationNativeMldsa.Source} : Request source → Type
  | .generate => Option (RegistrationNativeMldsa.Credential source)
  | .sign _ _ => SignReply

noncomputable def draw {source : RegistrationNativeMldsa.Source} (query : Request source) : ProbComp (Reply query) :=
  match query with
  | .generate => RegistrationNativeMldsa.generate source
  | .sign credential request => RegistrationNativeMldsa.owned source credential request

abbrev Spec (source : RegistrationNativeMldsa.Source) : OracleSpec (Request source) :=
  fun query => Reply query × Nat

/-- The actual leaf interpreter retains the complete source random behavior and its exact draw count. -/
noncomputable def actual (source : RegistrationNativeMldsa.Source) : QueryImpl (Spec source) ProbComp :=
  fun query => (simulateQ PqxdhRecordLiftWorld.countCoin (draw query)).run 0

/-- Private coin-count erasure gives exactly the original generate or complete owned-sign operation. -/
theorem actual_forget (source : RegistrationNativeMldsa.Source) (query : Request source) :
    Prod.fst <$> actual source query = draw query :=
  PqxdhRecordLiftWorld.countCoin_forget (draw query) 0

private theorem count_query (query count : Nat) :
    (PqxdhRecordLiftWorld.countCoin query).run count =
      (fun reply => (reply, count + 1)) <$> (unifSpec.query query : ProbComp _) := rfl

/-- Counting a leaf from an arbitrary reached counter differs only by its initial offset. -/
theorem count_offset (work : ProbComp Value) (offset initial : Nat) :
    Prod.map id (fun count => offset + count) <$>
        (simulateQ PqxdhRecordLiftWorld.countCoin work).run initial =
      (simulateQ PqxdhRecordLiftWorld.countCoin work).run (offset + initial) := by
  have step (query current : Nat) :
      Prod.map id (fun count => offset + count) <$>
          (PqxdhRecordLiftWorld.countCoin query).run current =
        (PqxdhRecordLiftWorld.countCoin query).run (offset + current) := by
    simp only [count_query, Functor.map_map, Prod.map, id_eq, Nat.add_assoc]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (fun count => offset + count) step work initial

def advance (accounting : Accounting) (before : PqxdhRecordLiftWorld.State n) (count : Nat) :
    PqxdhRecordLiftWorld.State n :=
  { before with primitive := ({ before.primitive.1 with
      uniform := before.primitive.1.uniform + count
      effects := match accounting with
        | .native => before.primitive.1.effects
        | .environment => Function.update before.primitive.1.effects .coin (before.primitive.1.effects .coin + count) },
      before.primitive.2) }

private theorem advance_zero (accounting : Accounting) (before : PqxdhRecordLiftWorld.State n) :
    advance accounting before 0 = before := by
  cases accounting <;> simp only [advance, Nat.add_zero, Function.update_eq_self]

/-- A native-only leaf keeps its exact original uniform counter and every other World field. -/
theorem native_count (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1, advance .native before result.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0 =
      (PqxdhRecordLiftWorld.sampled work).run before := by
  have shifted := congrArg (fun distribution =>
    (fun result : Value × Nat => (result.1, { before with primitive :=
      ({ before.primitive.1 with uniform := result.2 }, before.primitive.2) })) <$> distribution)
    (count_offset work before.primitive.1.uniform 0)
  simpa only [Nat.add_zero, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, advance] using shifted

/-- An Env leaf counts the same actual underlying draws in both original private counters. -/
theorem environment_count (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1, advance .environment before result.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0 =
      (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin work)).run before := by
  have step (query current : Nat) :
      Prod.map id (advance .environment before) <$>
          (PqxdhRecordLiftWorld.countCoin query).run current =
        (RegistrationWorldCoinCompiler.coin query).run (advance .environment before current) := by
    simp only [count_query, RegistrationWorldCoinCompiler.coin_run, Functor.map_map, Prod.map,
      id_eq, advance, RegistrationWorldCoinCompiler.tick, Function.update_self,
      Function.update_idem, Nat.add_assoc]
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (advance .environment before) step work 0
  rw [advance_zero] at law
  rw [RegistrationWorldCoinCompiler.env_program]
  exact law

/-- Reified private leaf calls update only the original accounting coordinates. -/
noncomputable def call {source : RegistrationNativeMldsa.Source} (accounting : Accounting) (query : Request source) :
    StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) (Reply query) := fun before => do
  let reply ← (Spec source).query query
  pure (reply.1, advance accounting before reply.2)

/-- Actual evaluation of a reified leaf is exactly the original source sampling at the same reached World. -/
theorem call_actual (source : RegistrationNativeMldsa.Source) (accounting : Accounting)
    (query : Request source) (before : PqxdhRecordLiftWorld.State n) :
    simulateQ (actual source) ((call accounting query).run before) =
      match accounting with
      | .native => (PqxdhRecordLiftWorld.sampled (draw query)).run before
      | .environment => (simulateQ PqxdhRecordLiftWorld.effects
          (simulateQ RegistrationWorldCoinCompiler.envCoin (draw query))).run before := by
  cases accounting with
  | native =>
      simp only [call, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query, actual]
      exact native_count (draw query) before
  | environment =>
      simp only [call, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query, actual]
      exact environment_count (draw query) before

end BeaconcryptCore.Computational.RegistrationNativeMldsaCapability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.actual_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.actual_forget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.count_offset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.count_offset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.native_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.native_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.environment_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.environment_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.call_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCapability.call_actual
