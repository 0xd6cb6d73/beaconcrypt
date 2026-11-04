-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop

/-! The free named-capability stopping program has the exact actual private-table execution used by the same-cut candidate theorem. State reassociation retains the complete native source state, table, first candidate and true primitive accounting. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaTableProgram (runState)
open RegistrationNativeMldsaStop (Observer freeze)
variable {Index State Candidate Value : Type} {queries : OracleSpec Index}
variable (source : RegistrationNativeMldsa.Source)

/-- Reassociate the actual table state; no field is erased. -/
def arrange (result : (Value × (State × Option Candidate)) × Pool source) :
    Value × ((State × Pool source) × Option Candidate) :=
  (result.1.1, ((result.1.2.1, result.2), result.1.2.2))

noncomputable def callback (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))))) :
    QueryImpl queries (StateT (State × Pool source) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> runState source (handler query) before.1 before.2

def observer (observe : Observer (spec := queries) (State := State) (Candidate := Candidate)) :
    Observer (spec := queries) (State := State × Pool source) (Candidate := Candidate) :=
  fun query before reply after => observe query before.1 reply after.1

private theorem map_apply {S A B : Type} (function : A → B) (work : StateT S ProbComp A) (before : S) :
    (function <$> work) before = (fun pair => (function pair.1, pair.2)) <$> work before :=
  StateT.run_map function work before

/-- One actual stopped capability callback is exactly its stopped table interpretation, including the no-query branch after selection. -/
theorem query (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)))))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (query : queries.Domain) (current : State) (previous : Option Candidate) (pool : Pool source) :
    arrange source <$> runState source (freeze handler observe defaultReply query) (current, previous) pool =
      (freeze (callback source handler) (observer source observe) defaultReply query).run ((current, pool), previous) := by
  cases previous with
  | none =>
    simp only [freeze, RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp,
      RegistrationNativeMldsaTableProgram.runState, RegistrationNativeMldsaTableProgram.evaluate,
      simulateQ_map, Functor.map_map, callback, observer]
    rw [map_apply, Functor.map_map]
    rfl
  | some candidate =>
    change arrange source <$> runState source (pure (defaultReply query)) (current, some candidate) pool =
      pure (defaultReply query, ((current, pool), some candidate))
    rw [RegistrationNativeMldsaTableProgram.run_pure, map_pure]
    rfl

/-- Every adaptive free stopped program equals its actual same-cut table callback execution, jointly in native state, pool and candidate. -/
theorem program (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)))))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries Value)
    (current : State) (previous : Option Candidate) (pool : Pool source) :
    arrange source <$> runState source (simulateQ (freeze handler observe defaultReply) work) (current, previous) pool =
      (simulateQ (freeze (callback source handler) (observer source observe) defaultReply) work).run ((current, pool), previous) := by
  induction work using OracleComp.inductionOn generalizing current previous pool with
  | pure value => simp only [simulateQ_pure, RegistrationNativeMldsaTableProgram.run_pure, map_pure, StateT.run_pure]; rfl
  | query_bind asked next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.run_bind, map_bind,
      StateT.run_bind]
    rw [← query source handler observe defaultReply asked current previous pool, bind_map_left]
    apply bind_congr
    intro middle
    exact ih middle.1.1 middle.1.2.1 middle.1.2.2 middle.2

section Native
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (handleSource source))

/-- The concrete original typed free source program executes exactly the checked TableStop frozen run. -/
theorem native (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (current : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (previous : Option RegistrationNativeMldsaEuf.Forgery) (pool : Pool source) :
    arrange source <$> runState source
      (simulateQ (freeze (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential)
        (RegistrationNativeMldsaTrialObserver.observe source.verify publicKey) defaultReply) work) (current, previous) pool =
      (simulateQ (freeze (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential)
        (RegistrationNativeMldsaTableStop.observe source publicKey) defaultReply) work).run ((current, pool), previous) :=
  program source _ _ defaultReply work current previous pool

/-- Actual startup and free stopped-source support suffice for ordinary validity and freshness at the literal final signing prefix. -/
theorem initialized_good (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : (Value × (RegistrationNativeExperiment.State n KemSK (handleSource source) × Option RegistrationNativeMldsaEuf.Forgery)) × Pool source)
    (supported : result ∈ support (runState source
      (simulateQ (freeze (RegistrationNativeMldsaProfile.handler setup checks wire route representation initial.created initial.credential)
        (RegistrationNativeMldsaTrialObserver.observe source.verify publicKey) RegistrationNativeMldsaTableStop.defaultReply) work)
      (initial.state, none) started.2)) :
    ∀ forgery, result.1.2.2 = some forgery →
      RegistrationNativeMldsaTableStop.Good source publicKey (result.1.2.1, result.2) forgery := by
  have mapped : arrange source result ∈ support ((simulateQ (freeze
      (RegistrationNativeMldsaTableStop.callback source setup checks wire route representation initial.created initial.credential)
      (RegistrationNativeMldsaTableStop.observe source publicKey) RegistrationNativeMldsaTableStop.defaultReply) work).run
        ((initial.state, started.2), none)) := by
    rw [← native source setup checks wire route representation initial.created initial.credential publicKey
      RegistrationNativeMldsaTableStop.defaultReply work initial.state none started.2, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativeMldsaTableStop.initialized_good source setup checks wire route representation publicKey ensureInit
    identityIndex serverKeyId started startup initial member work (arrange source result) mapped

end Native
end BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.initialized_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStoppedSource.initialized_good
