-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting

/-! Compile the actual initialized registration client into the ordinary generated-identity game. KEM generation/decapsulation and runtime initialization retain their complete local state and actual randomness. Generated identity seeds remain confined to the ordinary joint-game interpreter; imported seeds remain caller-known. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhServerAuthExperiment
open PqxdhRegistrationJointIdentityRouting (Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Next Reader Response : Type}
abbrev Local (KemSK A : Type) := PqxdhLiveKemBirth.Pool KemSK × A
abbrev Client (KemSK A Result : Type) := StateT (Local KemSK A) (OracleComp Spec) Result
abbrev State (KemSK A : Type) := PqxdhRegistrationJointServerPrefix.State KemSK A

def coins (work : ProbComp Result) : OracleComp Spec Result :=
  simulateQ (fun query => Spec.query (.inr (.inl query))) work

def native (work : StateT (Local KemSK A) ProbComp Result) : Client KemSK A Result := fun state => coins (work state)

def forward : QueryImpl Spec (Client KemSK A) := fun query state => (fun answer => (answer, state)) <$> Spec.query query

def onKem (work : StateT (PqxdhLiveKemBirth.Pool KemSK) ProbComp Result) : StateT (Local KemSK A) ProbComp Result :=
  fun state => (fun result => (result.1, (result.2, state.2))) <$> work state.1

def onRuntime (work : StateT A ProbComp Result) : StateT (Local KemSK A) ProbComp Result :=
  fun state => (fun result => (result.1, (state.1, result.2))) <$> work state.2

/-- The actual constructor/backend service compiler uses only standard generated identity services, explicit known imports and local evaluated source code. -/
def impl (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool) :
    QueryImpl (PqxdhRegistrationJointServerBirth.Spec KemSK) (Client KemSK A)
  | .inl (.inl query) => forward (.inl query)
  | .inl (.inr (.inl coin)) => forward (.inr (.inl coin))
  | .inl (.inr (.inr query)) => native (onKem (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query))
  | .inr .initialize => native (onRuntime ensureInit)
  | .inr (.importSeed seed) => forward (.inr (.inr seed))

/-- Reassociate the entire identity/KEM/runtime state after interpreting the routing source interface. -/
def run (joint : Primitives) (work : Client KemSK A Result) (state : State KemSK A) :
    ProbComp (Result × State KemSK A) :=
  (fun result => (result.1.1, ((result.2, result.1.2.1), result.1.2.2))) <$>
    (simulateQ (PqxdhRegistrationJointIdentityRouting.source joint) (work (state.1.2, state.2))).run state.1.1

set_option backward.isDefEq.respectTransparency false in
/-- Every local random query is real and preserves the full source identity pool and native-index audit. -/
theorem coins_complete (joint : Primitives) (work : ProbComp Result) (state : SourceState) :
    (simulateQ (PqxdhRegistrationJointIdentityRouting.source joint) (coins work)).run state =
      (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      change ((unifSpec.query query : ProbComp _) >>= fun answer =>
        (simulateQ (PqxdhRegistrationJointIdentityRouting.source joint) (coins (next answer))).run state) = _
      simp only [ih, map_bind]

/-- The complete local KEM/runtime execution remains in place and leaves only identity ownership unchanged. -/
theorem native_run (joint : Primitives) (work : StateT (Local KemSK A) ProbComp Result) (state : State KemSK A) :
    run joint (native work) state =
      (fun result => (result.1, ((state.1.1, result.2.1), result.2.2))) <$> work (state.1.2, state.2) := by
  simp only [run, native, coins_complete, Functor.map_map]

/-- A forwarded request retains every local KEM/runtime field and uses the exact indexed source identity interface. -/
theorem forward_run (joint : Primitives) (query : Spec.Domain) (state : State KemSK A) :
    run joint (forward query) state =
      (fun result => (result.1, ((result.2, state.1.2), state.2))) <$>
        (PqxdhRegistrationJointIdentityRouting.source joint query).run state.1.1 := by
  simp only [run, forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]

/-- All adaptive continuations retain both complete private services and the runtime state. -/
theorem run_bind (joint : Primitives) (work : Client KemSK A Result)
    (next : Result → Client KemSK A Next) (state : State KemSK A) :
    run joint (work >>= next) state =
      (run joint work state >>= fun result => run joint (next result.1) result.2) := by
  change (fun result : (Next × Local KemSK A) × SourceState => (result.1.1, ((result.2, result.1.2.1), result.1.2.2))) <$>
    (simulateQ (PqxdhRegistrationJointIdentityRouting.source joint)
      (work (state.1.2, state.2) >>= fun result => next result.1 result.2)).run state.1.1 = _
  simp only [simulateQ_bind, StateT.run_bind, map_bind, run, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual private-service or constructor callback matches its complete original interpreter, including local KEM secrets, histories and initialization effects. -/
theorem query_source (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain) (state : State KemSK A) :
    run setup.joint (impl setup ensureInit query) state =
      (PqxdhRegistrationJointServerBirth.impl setup ensureInit query).run state := by
  rcases query with (query | (coin | query)) | request
  case inl.inl =>
    change run setup.joint (forward (.inl query)) state = _
    rw [forward_run]
    simp only [PqxdhRegistrationJointIdentityRouting.source,
      PqxdhRegistrationJointServerBirth.impl, PqxdhRegistrationJointServerPrefix.onPool,
      PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
    rfl
  case inl.inr.inl =>
    change run setup.joint (forward (.inr (.inl coin))) state = _
    rw [forward_run]
    simp only [PqxdhRegistrationJointIdentityRouting.source,
      PqxdhRegistrationJointServerBirth.impl, PqxdhRegistrationJointServerPrefix.onPool,
      PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
    rfl
  case inl.inr.inr =>
    simp only [impl, native_run, onKem, PqxdhRegistrationJointServerBirth.impl,
      PqxdhRegistrationJointServerPrefix.onPool, PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
    rfl
  case inr =>
    cases request with
    | «initialize» =>
        simp only [impl, native_run, onRuntime, PqxdhRegistrationJointServerBirth.impl,
          PqxdhRegistrationJointServerPrefix.onAux, StateT.run, Functor.map_map]
    | importSeed seed =>
        simpa only [impl, PqxdhRegistrationJointIdentityRouting.source,
          PqxdhRegistrationJointServerBirth.impl, PqxdhRegistrationJointServerBirth.importKnown, StateT.run, map_pure] using
            forward_run setup.joint (.inr (.inr seed)) state

/-- The ordinary-identity source compiler preserves the entire actual initialized program, all continuations and both source private histories. -/
theorem program_source (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) Result) (state : State KemSK A) :
    run setup.joint (simulateQ (impl setup ensureInit) program) state =
      (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, run_bind, query_source, StateT.run_bind, ih]

/-- The executable identity reduction owns only the KEM/runtime state and a source-index registry. Generated identity secrets stay exclusively in the standard external challenger. -/
def reduction (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) Result)
    (localState : Local KemSK A) (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    OracleComp DynamicSpec ((Result × Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry) :=
  (simulateQ (PqxdhRegistrationJointIdentityRouting.route setup.joint)
    ((simulateQ (impl setup ensureInit) program).run localState)).run registry

/-- This full source-state reconstruction is applied only after interpreting the ordinary challenger, never inside the executable reduction. -/
def projectResult (result : ((Result × Local KemSK A) × PqxdhRegistrationJointIdentityRouting.Registry) × SourceState) :
    Result × State KemSK A :=
  (result.1.1.1, ((PqxdhRegistrationJointIdentityRouting.project (result.1.2, result.2), result.1.1.2.1), result.1.1.2.2))

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual source program is simulated in the ordinary dynamically generated joint game, with imports locally known, exact creation indices and all private/native/runtime state retained in the interpreted projection. -/
theorem reduction_source (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointServerBirth.Spec KemSK) Result)
    (localState : Local KemSK A) (state : PqxdhRegistrationJointIdentityRouting.State)
    (valid : PqxdhRegistrationJointIdentityRouting.Valid state) :
    projectResult <$> (simulateQ (lazyImpl setup.joint) (reduction setup ensureInit program localState state.1)).run state.2 =
      (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit) program).run
        ((PqxdhRegistrationJointIdentityRouting.project state, localState.1), localState.2) := by
  rw [← program_source]
  have correspondence := PqxdhRegistrationJointIdentityRouting.program_source setup.joint
    ((simulateQ (impl setup ensureInit) program).run localState) state valid
  have mapped := congrArg (fun work => (fun result : (Result × Local KemSK A) × SourceState =>
    (result.1.1, ((result.2, result.1.2.1), result.1.2.2))) <$> work) correspondence
  simp only [reduction, run, PqxdhRegistrationJointIdentityRouting.run, Functor.map_map, StateT.run] at mapped ⊢
  convert mapped using 1
  rfl

/-- The concrete ordinary-joint-game client starts from empty private KEM and source handle registries, then executes actual Server initialization and every adaptive command. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :=
  reduction setup ensureInit (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program)
    (PqxdhLiveKemBirth.empty, runtime) ⟨[], []⟩

/-- Reattach every interpreted private owner and current native field to the actual initialized outcome, without adding any adversary observation. -/
def initializedResult
    (result : (((Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Result)) × Local KemSK A) ×
      PqxdhRegistrationJointIdentityRouting.Registry) × SourceState) :
    Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Result) × State KemSK A :=
  let decoded := projectResult result
  (decoded.1.map (PqxdhRegistrationJointOpenInitialization.attach decoded.2.1), decoded.2)

set_option backward.isDefEq.respectTransparency false in
/-- The actual initialized registration scheduler is an executable client of the ordinary joint-game endpoint. The checked equality retains every final native/private/runtime field, imported/generated origin, rejection and source-order sampler. -/
theorem initialized_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    initializedResult <$>
      (simulateQ (lazyImpl setup.joint) (initialized setup codec checks ensureInit supplied program runtime)).run initialState =
        (fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
          (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run
            ((initialState, PqxdhLiveKemBirth.empty), runtime) := by
  rw [← PqxdhRegistrationJointOpenInitialization.initialized_source]
  have correspondence := reduction_source setup ensureInit
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program)
    (PqxdhLiveKemBirth.empty, runtime) (⟨[], []⟩, initialState) PqxdhRegistrationJointIdentityRouting.initial_valid
  have mapped := congrArg (fun work => (fun result : Option (PqxdhRegistrationJointOpenInitialization.Outcome KemSK Result) × State KemSK A =>
    (result.1.map (PqxdhRegistrationJointOpenInitialization.attach result.2.1), result.2)) <$> work) correspondence
  simp only [initialized, PqxdhRegistrationJointOpenInitialization.run, Functor.map_map] at mapped ⊢
  convert mapped using 1
  all_goals rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.coins_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.forward_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.forward_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.reduction_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.reduction_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCompiler.initialized_source
