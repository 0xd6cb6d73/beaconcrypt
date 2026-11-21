-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts

/-! Route actual source allocation indices to the ordinary dynamically generated joint-identity game. Caller-known imports are represented by their known seed; generated identities are represented only by the challenger creation index. No public-key lookup or key-injectivity assumption selects a private owner. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting
open PqxdhJointIdentity PqxdhDynamicIdentityPool
variable {Result Next : Type}

inductive Ref where
  | known (seed : IdentitySeed)
  | generated (index : Nat)

structure Registry where
  refs : List Ref
  transcript : List Observation

abbrev State := Registry × SourceState
abbrev KnownSpec : OracleSpec IdentitySeed := fun _ => Nat × PublicIdentity
abbrev Spec := DynamicSpec + (unifSpec + KnownSpec)

def Valid (state : State) : Prop :=
  ∀ index, Ref.generated index ∈ state.1.refs → index < state.2.seeds.length

/-- Analysis-only interpretation of a handle. The default branch is excluded by the maintained validity invariant; this function is never passed to a client or reduction. -/
def resolve (seeds : List IdentitySeed) : Ref → IdentitySeed
  | .known seed => seed
  | .generated index => seeds[index]?.getD (List.Vector.replicate 32 0)

/-- Complete source private state and native-index audit, recovered only inside the ordinary game interpreter. -/
def project (state : State) : SourceState :=
  ⟨state.1.refs.map (resolve state.2.seeds), state.1.transcript⟩

def record (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query) (registry : Registry) : Registry :=
  { registry with transcript := registry.transcript ++ [⟨query, answer⟩] }

/-- Known imports append to the source registry without generating or relabelling an ordinary target identity. -/
def imported (joint : Primitives) (seed : IdentitySeed) (registry : Registry) :
    (Nat × PublicIdentity) × Registry :=
  ((registry.refs.length, joint.publicKeys seed), { registry with refs := registry.refs ++ [.known seed] })

/-- Publicly executable routing: generated private seeds occur only in the external standard joint-game interpreter. -/
def route (joint : Primitives) : QueryImpl Spec (StateT Registry (OracleComp DynamicSpec)) := fun query registry =>
  match query with
  | .inl (.inl coin) =>
      (fun answer => (answer, record (.inl coin) answer registry)) <$> DynamicSpec.query (.inl coin)
  | .inl (.inr .create) => do
      let answer ← DynamicSpec.query (.inr .create)
      match answer with
      | none => pure (none, record (.inr .create) none registry)
      | some generated =>
          let answer := some (registry.refs.length, generated.2)
          pure (answer, record (.inr .create) answer { registry with refs := registry.refs ++ [.generated generated.1] })
  | .inl (.inr (.service index request)) => do
      let answer ← match registry.refs[index]? with
        | none => pure none
        | some (.known seed) => pure (some (primitiveReply joint seed request))
        | some (.generated target) => DynamicSpec.query (.inr (.service target request))
      pure (answer, record (.inr (.service index request)) answer registry)
  | .inl (.inr (.reveal index)) => do
      let answer ← match registry.refs[index]? with
        | none => pure none
        | some (.known seed) => pure (some seed)
        | some (.generated target) => DynamicSpec.query (.inr (.reveal target))
      pure (answer, record (.inr (.reveal index)) answer registry)
  | .inr (.inl coin) => (fun answer => (answer, registry)) <$> DynamicSpec.query (.inl coin)
  | .inr (.inr seed) => pure (imported joint seed registry)

/-- Source interpretation retains its exact imported/generated allocation sequence and omits ambient coins from the private-service audit. -/
def source (joint : Primitives) : QueryImpl Spec (StateT SourceState ProbComp)
  | .inl query => lazyImpl joint query
  | .inr (.inl coin) => fun state => (fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _)
  | .inr (.inr seed) => fun state => pure ((state.seeds.length, joint.publicKeys seed),
      { state with seeds := state.seeds ++ [seed] })

def run (joint : Primitives) (work : StateT Registry (OracleComp DynamicSpec) Result) (state : State) :
    ProbComp (Result × State) :=
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl joint) (work state.1)).run state.2

/-- Existing generated handles retain their exact seed after another generation; this statement uses creation indices, never public-key uniqueness. -/
theorem resolve_append (seeds : List IdentitySeed) (seed : IdentitySeed) (reference : Ref)
    (valid : ∀ index, reference = .generated index → index < seeds.length) :
    resolve (seeds ++ [seed]) reference = resolve seeds reference := by
  cases reference <;> simp_all [resolve, List.getElem?_append_left]

/-- Appending the actual next generated handle preserves the entire decoded source seed prefix and appends exactly the sampled seed. -/
theorem project_created (joint : Primitives) (state : State) (seed : IdentitySeed) (valid : Valid state) :
    project ((record (.inr .create) (some (state.1.refs.length, joint.publicKeys seed))
      { state.1 with refs := state.1.refs ++ [.generated state.2.seeds.length] }),
      (createdReply joint state.2 seed).2) = (createdReply joint (project state) seed).2 := by
  simp only [project, record, createdReply, PqxdhDynamicIdentityPool.record, List.map_append,
    List.map_cons, List.map_nil, List.length_map, resolve, List.getElem?_concat_length, Option.getD_some]
  congr 2
  apply List.map_congr_left
  exact fun reference present => resolve_append _ seed reference (fun index same => valid index (same ▸ present))

set_option backward.isDefEq.respectTransparency false in
/-- The complete coupled creation retains the challenger state as well as the source-index registry; no generated seed is available until interpretation. -/
theorem create_run (joint : Primitives) (state : State) :
    run joint (route joint (.inl (.inr .create))) state =
      (fun seed => (some (state.1.refs.length, joint.publicKeys seed),
        (record (.inr .create) (some (state.1.refs.length, joint.publicKeys seed))
          { state.1 with refs := state.1.refs ++ [.generated state.2.seeds.length] },
          (createdReply joint state.2 seed).2))) <$> sampleSeed := by
  simp only [run]
  change (fun result : (Option (Nat × PublicIdentity) × Registry) × SourceState => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl joint) (_ >>= _)).run state.2 = _
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lazyImpl_create,
    bind_map_left, createdReply, simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Actual generated creation uses the standard lazy challenger draw in source order and preserves the complete decoded private state and native audit. -/
theorem create_source (joint : Primitives) (state : State) (valid : Valid state) :
    (fun result => (result.1, project result.2)) <$>
      run joint (route joint (.inl (.inr .create))) state =
        (source joint (.inl (.inr .create))).run (project state) := by
  rw [create_run]
  change _ = (lazyImpl joint (.inr .create)).run (project state)
  rw [lazyImpl_create]
  simp only [Functor.map_map, project_created joint state _ valid]
  congr 1
  funext seed
  simp only [createdReply, project, List.length_map]

set_option backward.isDefEq.respectTransparency false in
/-- Forwarded service answers retain their complete challenger state together with the exact local registry update. -/
theorem forwarded_run (joint : Primitives) (query : DynamicSpec.Domain)
    (next : Registry → DynamicSpec.Range query → Result × Registry) (state : State) :
    run joint (fun registry => next registry <$> DynamicSpec.query query) state =
      (fun result => ((next state.1 result.1).1, ((next state.1 result.1).2, result.2))) <$>
        (lazyImpl joint query).run state.2 := by
  change (fun result : (Result × Registry) × SourceState => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl joint) (next state.1 <$> DynamicSpec.query query)).run state.2 = _
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query]
  simp only [Functor.map_map]

/-- Local pure routing preserves the complete external challenger state. -/
theorem pure_run (joint : Primitives) (next : Registry → Result × Registry) (state : State) :
    run joint (fun registry => pure (next registry)) state = pure ((next state.1).1, ((next state.1).2, state.2)) := rfl
set_option backward.isDefEq.respectTransparency false in
/-- Native-audited and ambient uniform requests share the ordinary random channel but preserve their distinct source audit behavior. -/
theorem uniform_source (joint : Primitives) (coin : Nat) (state : State) :
    (fun result => (result.1, project result.2)) <$> run joint (route joint (.inl (.inl coin))) state =
      (source joint (.inl (.inl coin))).run (project state) := by
  change (fun result => (result.1, project result.2)) <$>
    run joint (fun registry => (fun answer => (answer, record (.inl coin) answer registry)) <$>
      DynamicSpec.query (.inl coin)) state = _
  rw [forwarded_run]
  simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record, Functor.map_map]
set_option backward.isDefEq.respectTransparency false in
/-- Every source service, known import and ambient random request has exactly the original reply and complete projected source state under the ordinary generated-identity game. -/
theorem query_source (joint : Primitives) (query : Spec.Domain) (state : State) (valid : Valid state) :
    (fun result => (result.1, project result.2)) <$> run joint (route joint query) state =
      (source joint query).run (project state) := by
  rcases query with (coin | request) | (coin | seed)
  case inl.inl => exact uniform_source joint coin state
  case inr.inl =>
    simp only [run, route, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    simp [source, lazyImpl, poolImpl, StateT.run, project, PqxdhDynamicIdentityPool.record, Functor.map_map]
  case inr.inr =>
    simp only [run, route, simulateQ_pure, StateT.run_pure, map_pure]
    simp [source, StateT.run, imported, project, resolve]
  case inl.inr =>
    cases request with
    | create => exact create_source joint state valid
    | service index request =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
            simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record, List.getElem?_map, found]
        | some reference =>
            cases reference with
            | known seed =>
                simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
                simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record,
                  List.getElem?_map, found, resolve]
            | generated target =>
                have targetValid := valid target (List.mem_of_getElem? found)
                simp only [run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]
                simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record,
                  List.getElem?_map, found, resolve, List.getElem?_eq_getElem targetValid]
    | reveal index =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
            simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record, List.getElem?_map, found]
        | some reference =>
            cases reference with
            | known seed =>
                simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
                simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record,
                  List.getElem?_map, found, resolve]
            | generated target =>
                have targetValid := valid target (List.mem_of_getElem? found)
                simp only [run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]
                simp [source, lazyImpl, poolImpl, StateT.run, project, record, PqxdhDynamicIdentityPool.record,
                  List.getElem?_map, found, resolve, List.getElem?_eq_getElem targetValid]

/-- The empty source and ordinary challenger registries satisfy the handle invariant without a premise about honest protocol candidates. -/
theorem initial_valid : Valid (⟨[], []⟩, initialState) := by simp [Valid]

/-- A generated source handle always denotes the newly appended challenger seed, while all prior generated handles remain valid. -/
theorem created_valid (joint : Primitives) (state : State) (seed : IdentitySeed) (valid : Valid state) :
    Valid (record (.inr .create) (some (state.1.refs.length, joint.publicKeys seed))
      { state.1 with refs := state.1.refs ++ [.generated state.2.seeds.length] },
      (createdReply joint state.2 seed).2) := by
  simp only [Valid, record, createdReply, PqxdhDynamicIdentityPool.record, List.mem_append,
    List.mem_singleton, Ref.generated.injEq, List.length_append, List.length_singleton]
  exact fun index present => present.elim (fun member => Nat.lt_succ_of_lt (valid index member)) (fun same => same ▸ Nat.lt_succ_self _)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual routed reply preserves validity, including imported material, missing handles, rejected services and explicit reveals. -/
theorem query_valid (joint : Primitives) (query : Spec.Domain) (state : State) (valid : Valid state)
    (result : Spec.Range query × State) (supported : result ∈ support (run joint (route joint query) state)) :
    Valid result.2 := by
  rcases query with (coin | request) | (coin | seed)
  case inl.inl =>
    simp only [run, route, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact valid
  case inr.inl =>
    simp only [run, route, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
    simp only [lazyImpl, poolImpl, StateT.run, bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨answer, _, rfl⟩ := supported
    exact valid
  case inr.inr =>
    simp only [run, route, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
    subst result
    simpa [Valid, imported] using valid
  case inl.inr =>
    cases request with
    | create =>
        rw [create_run] at supported
        obtain ⟨seed, _, rfl⟩ := (show ∃ seed ∈ support sampleSeed, _ from by simpa only [support_map, Set.mem_image] using supported)
        exact created_valid joint state seed valid
    | service index request =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact valid
        | some reference =>
            cases reference with
            | known seed =>
                simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact valid
            | generated target =>
                simp only [run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact valid
    | reveal index =>
        cases found : state.1.refs[index]? with
        | none =>
            simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
            subst result
            exact valid
        | some reference =>
            cases reference with
            | known seed =>
                simp only [run, route, found, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
                subst result
                exact valid
            | generated target =>
                simp only [run, route, found, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map] at supported
                simp only [lazyImpl, poolImpl, StateT.run, map_pure, mem_support_pure_iff] at supported
                subst result
                exact valid

set_option backward.isDefEq.respectTransparency false in
/-- Coupled interpretation retains the complete registry/challenger state between every adaptive continuation. -/
theorem run_bind (joint : Primitives) (work : StateT Registry (OracleComp DynamicSpec) Result)
    (next : Result → StateT Registry (OracleComp DynamicSpec) Next) (state : State) :
    run joint (work >>= next) state =
      (run joint work state >>= fun result => run joint (next result.1) result.2) := by
  change (fun result : (Next × Registry) × SourceState => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl joint) (work state.1 >>= fun result => next result.1 result.2)).run state.2 = _
  simp only [simulateQ_bind, StateT.run_bind, map_bind, run, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary adaptive source programs, including every supplied import and reveal, have the same complete source-private output under the ordinary generated-identity endpoint. No generator interchange, marginal-only equality or unavailable seed oracle is used. -/
theorem program_source (joint : Primitives) (program : OracleComp Spec Result) (state : State) (valid : Valid state) :
    (fun result => (result.1, project result.2)) <$> run joint (simulateQ (route joint) program) state =
      (simulateQ (source joint) program).run (project state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, run_bind, map_bind, StateT.run_bind]
      rw [← query_source joint query state valid]
      simp only [bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result supported
      exact ih result.1 result.2 (query_valid joint query state valid result supported)

end BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.resolve_append' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.resolve_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.project_created' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.project_created

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.create_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.forwarded_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.forwarded_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.pure_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.uniform_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.initial_valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.initial_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.created_valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.created_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.query_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.query_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityRouting.program_source
