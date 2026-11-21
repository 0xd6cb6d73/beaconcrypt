-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource

/-! The public censor stopping client threads one complete private source interpreter through its actual callbacks. Reassociation retains the shared physical cache, private pool, exact Native/P state and the same public stopping snapshot, including every failed prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource
open RegistrationNativeMldsaStop (Observer freeze)
variable {Index State Candidate Value Private : Type} {queries : OracleSpec Index}
variable (backend : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))

noncomputable def runState (work : StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec) Value)
    (current : State) (privateState : Private) : ProbComp ((Value × State) × Private) :=
  (simulateQ backend (work.run current)).run privateState

private theorem run_pure (value : Value) (current : State) (privateState : Private) :
    runState backend (pure value) current privateState = pure ((value, current), privateState) := by
  simp only [runState, StateT.run_pure, simulateQ_pure, StateT.run_pure]

private theorem run_bind {Next : Type}
    (work : StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec) Value)
    (next : Value → StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec) Next)
    (current : State) (privateState : Private) :
    runState backend (work >>= next) current privateState = (do
      let result ← runState backend work current privateState
      runState backend (next result.1.1) result.1.2 result.2) := by
  simp only [runState, StateT.run_bind, simulateQ_bind, StateT.run_bind]

/-- Reassociate the actual table state; no field is erased. -/
def arrange (result : (Value × (State × Option Candidate)) × Private) :
    Value × ((State × Private) × Option Candidate) :=
  (result.1.1, ((result.1.2.1, result.2), result.1.2.2))

noncomputable def callback (handler : QueryImpl queries (StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec))) :
    QueryImpl queries (StateT (State × Private) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> runState backend (handler query) before.1 before.2

def observer (observe : Observer (spec := queries) (State := State) (Candidate := Candidate)) :
    Observer (spec := queries) (State := State × Private) (Candidate := Candidate) :=
  fun query before reply after => observe query before.1 reply after.1

private theorem map_apply {S A B : Type} (function : A → B) (work : StateT S ProbComp A) (before : S) :
    (function <$> work) before = (fun pair => (function pair.1, pair.2)) <$> work before :=
  StateT.run_map function work before

/-- One actual stopped capability callback is exactly its stopped table interpretation, including the no-query branch after selection. -/
theorem query (handler : QueryImpl queries (StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec)))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (query : queries.Domain) (current : State) (previous : Option Candidate) (pool : Private) :
    arrange <$> runState backend (freeze handler observe defaultReply query) (current, previous) pool =
      (freeze (callback backend handler) (observer observe) defaultReply query).run ((current, pool), previous) := by
  cases previous with
  | none =>
    simp only [freeze, RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp,
      runState,
      simulateQ_map, Functor.map_map, callback, observer]
    rw [map_apply, Functor.map_map]
    rfl
  | some candidate =>
    change arrange <$> runState backend (pure (defaultReply query)) (current, some candidate) pool =
      pure (defaultReply query, ((current, pool), some candidate))
    rw [run_pure, map_pure]
    rfl

/-- Every adaptive publicly stopped program equals its actual same-cut private-source callback execution, jointly in native state, pool and candidate. -/
theorem program (handler : QueryImpl queries (StateT State (OracleComp RegistrationNativeIdentityCensorOperational.Spec)))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries Value)
    (current : State) (previous : Option Candidate) (pool : Private) :
    arrange <$> runState backend (simulateQ (freeze handler observe defaultReply) work) (current, previous) pool =
      (simulateQ (freeze (callback backend handler) (observer observe) defaultReply) work).run ((current, pool), previous) := by
  induction work using OracleComp.inductionOn generalizing current previous pool with
  | pure value => simp only [simulateQ_pure, run_pure, map_pure, StateT.run_pure]; rfl
  | query_bind asked next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, run_bind, map_bind,
      StateT.run_bind]
    rw [← query backend handler observe defaultReply asked current previous pool, bind_map_left]
    apply bind_congr
    intro middle
    exact ih middle.1.1 middle.1.2.1 middle.1.2.2 middle.2

section Main
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- Closing the literal public marked callback is the actual current Main computation after its public entry marker, with the full private source coordinate retained. -/
theorem current (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (censored : Bool)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (callback (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend) request).run before =
      (interpret joint selected placeholder censored (frontend request)).run
        ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position request before.1.2), before.2) := by
  have literal : (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before.1 =
      (fun returned => (returned.1.1, (returned.1.2, returned.2))) <$>
        (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
          ((frontend request).run before.1.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.1.2) := by
    change (do
      let returned ← (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        ((frontend request).run before.1.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.1.2)
      pure (returned.1.1, (returned.1.2, returned.2))) = _
    rw [bind_pure_comp]
  change (fun returned => (returned.1.1, (returned.1.2, returned.2))) <$>
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before.1)).run before.2 = _
  rw [literal, simulateQ_map, StateT.run_map, Functor.map_map]
  simp only [interpret, StateT.run, bind_pure_comp]

end Main
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource.current
