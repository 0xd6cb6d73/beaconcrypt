-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutMonotone

/-! Published-tuple provenance and published-tuple replay in the common deployment experiment (CE-7 CE-A2pub, CE-6 CE-R1'). -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- A stateful simulation keeps a state invariant along a client that never issues a query of class `bad`, when every other step keeps it. -/
theorem run_inv_of_free {ι' κ σ : Type} {spec : OracleSpec ι'} {target : OracleSpec κ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (bad : spec.Domain → Prop) [DecidablePred bad]
    (invariant : σ → Prop)
    (step : ∀ query, ¬bad query → ∀ state, invariant state → ∀ result ∈ support ((impl query).run state),
      invariant result.2)
    (client : OracleComp spec Result) (free : client.IsQueryBoundP bad 0) (state : σ) (held : invariant state)
    (result : Result × σ) (supported : result ∈ support ((simulateQ impl client).run state)) : invariant result.2 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact held
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      obtain ⟨allowed, rest⟩ := free
      have good : ¬bad query := by
        rcases allowed with fine | impossible
        · exact fine
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have restFree := rest reply
      simp only [good, ite_false] at restFree
      exact ih reply restFree middle (step query good state held _ first) second

/-- A stateful simulation of a client that never issues a query of class `bad` issues no query of class `target'` when no other step does. -/
theorem simulate_free {ι' κ σ : Type} {spec : OracleSpec ι'} {target : OracleSpec κ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (bad : spec.Domain → Prop) [DecidablePred bad]
    (forbidden : target.Domain → Prop) [DecidablePred forbidden]
    (step : ∀ query, ¬bad query → ∀ state, ((impl query).run state).IsQueryBoundP forbidden 0)
    (client : OracleComp spec Result) (free : client.IsQueryBoundP bad 0) (state : σ) :
    ((simulateQ impl client).run state).IsQueryBoundP forbidden 0 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      obtain ⟨allowed, rest⟩ := free
      have good : ¬bad query := by
        rcases allowed with fine | impossible
        · exact fine
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine isQueryBoundP_bind (n := 0) (m := 0) (step query good state) fun value _ => ?_
      have restFree := rest value.1
      simp only [good, ite_false] at restFree
      exact ih value.1 restFree value.2

/-- A plain simulation issues no query of class `forbidden` when no step does. -/
theorem simulateQ_free {ι' κ : Type} {spec : OracleSpec ι'} {target : OracleSpec κ}
    (impl : QueryImpl spec (OracleComp target)) (forbidden : target.Domain → Prop) [DecidablePred forbidden]
    (step : ∀ query, (impl query).IsQueryBoundP forbidden 0) (client : OracleComp spec Result) :
    (simulateQ impl client).IsQueryBoundP forbidden 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact isQueryBoundP_bind (n := 0) (m := 0) (step query) fun value _ => ih value

/-- A known-seed import request of the Server constructor interface, with public reports beside it. -/
def birthImport : (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)).Domain → Bool
  | .inl (.inr (.importSeed _)) => true
  | _ => false

/-- A known-seed import request of the identity routing interface, with public reports beside it. -/
def routeImport : (PqxdhRegistrationJointReportLift.Spec PqxdhRegistrationJointIdentityRouting.Spec).Domain → Bool
  | .inl (.inr (.inr _)) => true
  | _ => false

/-- With a generated Server seed, the report-instrumented initialized commands never import a known seed: the constructor creates the Server identity, and every later command reaches the private pools only through ordinary pool requests. -/
theorem initialized_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (count : Nat)
    (program : OracleComp (Spec KemSK) Result) :
    (PqxdhRegistrationJointReportCommands.initialized setup codec checks none count program).IsQueryBoundP
      (fun query => birthImport (KemSK := KemSK) query = true) 0 := by
  have liftFree : ∀ {Value : Type} (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Value),
      (PqxdhRegistrationJointReportLift.lift (simulateQ PqxdhRegistrationJointOpenInitialization.poolLift work) :
        OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Value).IsQueryBoundP
        (fun query => birthImport (KemSK := KemSK) query = true) 0 := by
    intro Value work
    induction work using OracleComp.inductionOn with
    | pure value => trivial
    | query_bind query next ih =>
        have notImport : birthImport (KemSK := KemSK) (.inl (.inl query)) = false := rfl
        simp only [PqxdhRegistrationJointReportLift.lift, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, PqxdhRegistrationJointOpenInitialization.poolLift]
        rw [isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp [notImport]), fun reply => ?_⟩
        simp only [notImport, Bool.false_eq_true, ite_false]
        exact ih reply
  have reportedFree : ∀ (identityIndex : Nat) (publicIdentity : PublicIdentity)
      (state : PqxdhRegistrationJointReportCommands.State KemSK),
      ((PqxdhRegistrationJointReportCommands.reported setup codec checks identityIndex publicIdentity count program).run
        state).IsQueryBoundP (fun query => birthImport (KemSK := KemSK) query = true) 0 := by
    intro identityIndex publicIdentity state
    apply PqxdhDeploymentCompileSecrecy.simulate_zero
    intro query current
    rcases query with query | report
    · change (PqxdhRegistrationJointReportLift.lift (PqxdhRegistrationJointReportCommands.commands setup codec checks
        identityIndex publicIdentity ((Spec KemSK).query query) current)).IsQueryBoundP _ 0
      simp only [PqxdhRegistrationJointReportCommands.commands]
      unfold PqxdhRegistrationJointReportLift.lift
      rw [simulateQ_map, isQueryBoundP_map_iff]
      exact liftFree _
    · change OracleComp.IsQueryBoundP ((fun _ => ((), current)) <$> ((PqxdhRegistrationJointReportLift.Spec
        (PqxdhRegistrationJointServerBirth.Spec KemSK)).query (.inr report) :
          OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) _)) _ 0
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      simp [birthImport]
  unfold PqxdhRegistrationJointReportCommands.initialized
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun born _ => ?_
  · simp only [PqxdhRegistrationJointReportLift.lift, PqxdhRegistrationJointServerBirth.client, simulateQ_bind,
      simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [birthImport]), fun ready => ?_⟩
    simp only [birthImport, Bool.false_eq_true, ite_false]
    split
    · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => by simp⟩
    · trivial
  · rcases born with _ | created
    · trivial
    · exact (isQueryBoundP_map_iff _ _ _).mpr (reportedFree _ _ _)

/-- Lifting a program beside public reports keeps a query-class bound of zero. -/
theorem lift_free {ι' : Type} {source : OracleSpec ι'}
    (forbidden : (PqxdhRegistrationJointReportLift.Spec source).Domain → Prop) [DecidablePred forbidden]
    (work : OracleComp source Result) (free : work.IsQueryBoundP (fun query => forbidden (.inl query)) 0) :
    (PqxdhRegistrationJointReportLift.lift work).IsQueryBoundP forbidden 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      obtain ⟨allowed, rest⟩ := free
      have good : ¬forbidden (.inl query) := by
        rcases allowed with fine | impossible
        · exact fine
        · omega
      simp only [PqxdhRegistrationJointReportLift.lift, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl good, fun reply => ?_⟩
      have restFree := rest reply
      simp only [good, ite_false] at restFree ⊢
      exact ih reply restFree

/-- The identity compiler forwards no known-seed import to the identity routing when the compiled commands make none. -/
theorem compiled_free (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointServerBirth.Spec KemSK)) Result)
    (free : program.IsQueryBoundP (fun query => birthImport (KemSK := KemSK) query = true) 0)
    (localState : PqxdhRegistrationJointIdentityCompiler.Local KemSK A) :
    ((simulateQ (PqxdhRegistrationJointReportLift.extend (PqxdhRegistrationJointIdentityCompiler.impl setup ensureInit))
      program).run localState).IsQueryBoundP (fun query => routeImport query = true) 0 := by
  apply simulate_free _ (fun query => birthImport (KemSK := KemSK) query = true) _ _ program free localState
  intro query notImport state
  have coinsFree : ∀ {Value : Type} (work : ProbComp Value),
      (PqxdhRegistrationJointIdentityCompiler.coins work).IsQueryBoundP
        (fun query => routeImport (.inl query) = true) 0 := by
    intro Value work
    apply simulateQ_free
    intro coin
    rw [isQueryBoundP_query_iff]
    simp [routeImport]
  rcases query with ((poolQuery | (coin | kemQuery)) | (_ | seed)) | report
  · apply lift_free
    simp only [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward]
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [routeImport]
  · apply lift_free
    simp only [PqxdhRegistrationJointIdentityCompiler.impl, PqxdhRegistrationJointIdentityCompiler.forward]
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [routeImport]
  · apply lift_free
    exact coinsFree _
  · apply lift_free
    exact coinsFree _
  · simp [birthImport] at notImport
  · change OracleComp.IsQueryBoundP ((fun _ => ((), state)) <$> ((PqxdhRegistrationJointReportLift.Spec
      PqxdhRegistrationJointIdentityRouting.Spec).query (.inr report) :
        OracleComp (PqxdhRegistrationJointReportLift.Spec PqxdhRegistrationJointIdentityRouting.Spec) _)) _ 0
    rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    simp [routeImport]

/-- Every identity handle is generated: the identity routing appends only generated handles when no known seed is imported. -/
def AllGenerated (registry : PqxdhRegistrationJointIdentityRouting.Registry) : Prop :=
  ∀ ref ∈ registry.refs, ∃ target, ref = .generated target

/-- Without known-seed imports, the identity routing keeps every handle generated. -/
theorem route_generated (joint : Primitives)
    (work : OracleComp (PqxdhRegistrationJointReportLift.Spec PqxdhRegistrationJointIdentityRouting.Spec) Result)
    (free : work.IsQueryBoundP (fun query => routeImport query = true) 0)
    (result : Result × PqxdhRegistrationJointIdentityRouting.Registry)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointReportLift.extend
      (PqxdhRegistrationJointIdentityRouting.route joint)) work).run ⟨[], []⟩)) :
    AllGenerated result.2 := by
  refine run_inv_of_free _ (fun query => routeImport query = true) AllGenerated ?_ work free _
    (by intro ref member; simp at member) result supported
  intro query notImport registry held next member
  rcases query with ((coin | (_ | ⟨selected, request⟩ | selected)) | (coin | seed)) | report
  · have inner := PqxdhRegistrationJointAcceptCutMonotone.simulate_result _ _ next member
    simp only [PqxdhRegistrationJointIdentityRouting.route, support_map, Set.mem_image] at inner
    obtain ⟨_, _, rfl⟩ := inner
    exact held
  · have inner := PqxdhRegistrationJointAcceptCutMonotone.simulate_result _ _ next member
    simp only [PqxdhRegistrationJointIdentityRouting.route, mem_support_bind_iff] at inner
    obtain ⟨answer, _, inner⟩ := inner
    cases answer with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at inner
        subst inner
        exact held
    | some generated =>
        simp only [support_pure, Set.mem_singleton_iff] at inner
        subst inner
        intro ref member
        simp only [PqxdhRegistrationJointIdentityRouting.record, List.mem_append, List.mem_singleton] at member
        rcases member with old | new
        · exact held ref old
        · exact ⟨_, new⟩
  · have inner := PqxdhRegistrationJointAcceptCutMonotone.simulate_result _ _ next member
    simp only [PqxdhRegistrationJointIdentityRouting.route] at inner
    split at inner
    · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
    · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
    · obtain ⟨_, _, inner⟩ := OracleComp.mem_support_bind_peel _ _ inner
      simp only [support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
  · have inner := PqxdhRegistrationJointAcceptCutMonotone.simulate_result _ _ next member
    simp only [PqxdhRegistrationJointIdentityRouting.route] at inner
    split at inner
    · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
    · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
    · obtain ⟨_, _, inner⟩ := OracleComp.mem_support_bind_peel _ _ inner
      simp only [support_pure, Set.mem_singleton_iff] at inner
      subst inner
      exact held
  · have inner := PqxdhRegistrationJointAcceptCutMonotone.simulate_result _ _ next member
    simp only [PqxdhRegistrationJointIdentityRouting.route, support_map, Set.mem_image] at inner
    obtain ⟨_, _, rfl⟩ := inner
    exact held
  · simp [routeImport] at notImport
  · change next ∈ support ((fun _ => ((), registry)) <$> ((PqxdhRegistrationJointReportLift.Spec
      PqxdhDynamicIdentityPool.DynamicSpec).query (.inr report) :
        OracleComp (PqxdhRegistrationJointReportLift.Spec PqxdhDynamicIdentityPool.DynamicSpec) _)) at member
    rw [support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact held

/-- With a generated Server seed, every identity handle of every report-run outcome of every source14 program is a generated report position. -/
theorem report_generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (program : OracleComp (Spec KemSK) Result) (runtime : A)
    (reached : PqxdhRegistrationJointInitializedReports.ReportResult KemSK A Result count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count program runtime)))
    (index : Nat) (ref : PqxdhRegistrationJointIdentityRouting.Ref) (found : reached.1.2.refs[index]? = some ref) :
    ∃ target, ref = .generated target := by
  have client : reached.1 ∈ support (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none
      count program runtime) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhJointPhase1Reports.sourceImpl setup.joint count) _
      (PqxdhJointPhase1Reports.initialMonitor count, ⟨PqxdhDynamicIdentityReports.initialSource count,
        PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, supported, rfl⟩
  have generated := route_generated setup.joint _ (compiled_free setup ensureInit _
    (initialized_free setup codec checks count program) _) reached.1 client
  exact generated ref (List.mem_of_getElem? found)

/-- One lazy pool step creates at most one seed, and only on a create request. -/
theorem pool_seeds (joint : Primitives) (request : PqxdhDynamicIdentityPool.DynamicSpec.Domain)
    (state : PqxdhDynamicIdentityPool.SourceState)
    (result : PqxdhDynamicIdentityPool.DynamicSpec.Range request × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint request).run state)) :
    result.2.seeds.length ≤ state.seeds.length + if PqxdhDynamicIdentityPool.IsCreate request then 1 else 0 := by
  rcases request with coin | (_ | ⟨selected, service⟩ | selected)
  · simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    simp [PqxdhDynamicIdentityPool.record]
  · rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at supported
    obtain ⟨seed, _, rfl⟩ := supported
    simp [PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, PqxdhDynamicIdentityPool.IsCreate]
  · simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    simp [PqxdhDynamicIdentityPool.record]
  · simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    simp [PqxdhDynamicIdentityPool.record]

/-- One step of the private report interpreter creates at most one seed, and only on a create request. -/
theorem reporting_seeds (joint : Primitives) (count : Nat) (query : PqxdhDynamicIdentityReports.ReportingSpec.Domain)
    (state : PqxdhDynamicIdentityReports.ReportingState count)
    (result : PqxdhDynamicIdentityReports.ReportingSpec.Range query × PqxdhDynamicIdentityReports.ReportingState count)
    (supported : result ∈ support ((PqxdhDynamicIdentityReports.reportingImpl joint count query).run state)) :
    result.2.source.2.seeds.length ≤ state.source.2.seeds.length +
      if PqxdhDynamicIdentityReports.reportingClass PqxdhDynamicIdentityPool.IsCreate query then 1 else 0 := by
  rcases query with request | candidate
  · simp only [PqxdhDynamicIdentityReports.reportingImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, source⟩, member, supported⟩ := supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    change (answer, source) ∈ support ((PqxdhDynamicIdentityRouting.sourceWithHistory count
      (PqxdhDynamicIdentityPool.lazyImpl joint) request).run (state.source.1, state.source.2)) at member
    rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run, mem_support_bind_iff] at member
    obtain ⟨reply, replyMember, member⟩ := member
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    have bound := pool_seeds joint request state.source.2 reply replyMember
    convert bound using 3
    exact Iff.rfl
  · rw [PqxdhDynamicIdentityReports.reportingImpl_report, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp [PqxdhDynamicIdentityReports.reportedReply]

/-- One step of the complete report interpreter creates at most one private seed, and only on a create request. -/
theorem source_seeds (joint : Primitives) (count : Nat) (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (state : PqxdhJointPhase1Reports.Monitor count × PqxdhDynamicIdentityReports.ReportingState count)
    (result : PqxdhJointPhase1Reports.ProtocolSpec.Range query ×
      (PqxdhJointPhase1Reports.Monitor count × PqxdhDynamicIdentityReports.ReportingState count))
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count query).run state)) :
    result.2.2.source.2.seeds.length ≤ state.2.source.2.seeds.length +
      if PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsCreate query then 1 else 0 := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact PqxdhServerAuthExperiment.run_count (PqxdhDynamicIdentityReports.reportingImpl joint count)
    (PqxdhDynamicIdentityReports.reportingClass PqxdhDynamicIdentityPool.IsCreate)
    (fun current => current.source.2.seeds.length) (reporting_seeds joint count)
    ((PqxdhJointPhase1Reports.wrapper joint count query).run state.1) _
    (PqxdhJointPhase1Reports.wrapper_query_step joint count PqxdhDynamicIdentityPool.IsCreate query state.1) state.2
    inner actual

/-- A report-run client with at most `count` identity creations creates at most `count` private seeds, so every generated report position of its routing is below `count`. -/
theorem generated_lt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (program : OracleComp (Spec KemSK) Result) (runtime : A)
    (creates : (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count program
      runtime).IsQueryBoundP (PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsCreate) count)
    (reached : PqxdhRegistrationJointInitializedReports.ReportResult KemSK A Result count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count program runtime)))
    (index target : Nat) (found : reached.1.2.refs[index]? = some (.generated target)) : target < count := by
  have tracked := PqxdhRegistrationJointRoutedReportSource.tracked setup.joint count _ reached supported
  have valid := tracked.valid target (List.mem_of_getElem? found)
  have bounded := PqxdhServerAuthExperiment.run_count (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
    (PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsCreate)
    (fun current => current.2.source.2.seeds.length) (source_seeds setup.joint count) _ count creates _ reached supported
  simp only [PqxdhDynamicIdentityReports.initialSource, PqxdhDynamicIdentityPool.initialState, List.length_nil,
    Nat.zero_add] at bounded
  exact lt_of_lt_of_le valid bounded

/-- The key tuple a published Phase 1 candidate carries: the messages of its three attached fields, parsed without a signature check. -/
def candidateTuple (candidate : PqxdhEd25519EufCma.Phase1Candidate) : Option PqxdhEd25519EufCma.Phase1KeyTuple := do
  let pre ← PqxdhEd25519EufCma.splitAttachedSignature candidate.preKey
  let one ← PqxdhEd25519EufCma.splitAttachedSignature candidate.oneTimeKey
  let pq ← PqxdhEd25519EufCma.splitAttachedSignature candidate.pqKey
  let prekey ← PqxdhEd25519EufCma.parsePrekeyMessage pre.2
  let oneTime ← PqxdhEd25519EufCma.parseOneTimeMessage one.2
  let pqKey ← PqxdhEd25519EufCma.parsePqMessage pq.2
  pure ⟨prekey, oneTime, pqKey⟩

/-- An honestly signed candidate carries exactly the key tuple it signed. -/
theorem candidateTuple_signed (primitives : Primitives) (seed : IdentitySeed)
    (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple) :
    candidateTuple (PqxdhJointPhase1SourceWriter.signedCandidate primitives seed identity keys) = some keys := by
  simp [candidateTuple, PqxdhJointPhase1SourceWriter.signedCandidate, PqxdhJointPhase1SourceWriter.candidate]

/-- The key tuple of an owner's first published bundle, read from public bytes without a signature check. -/
def publishedTuple (codec : Codec Reader Response) (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) :
    Option PqxdhEd25519EufCma.Phase1KeyTuple :=
  ((PqxdhDeploymentTranscript.bundleOf transcript owner).bind (PqxdhDeploymentTranscript.candidateOf codec)).bind
    candidateTuple

/-- The Ed25519 identity public key of every owner of a native state, in creation order. -/
def ownerIdentities (setup : Setup baseSpec KemSK) (native : PqxdhRegistrationSchedule.State KemSK) :
    List PqxdhEd25519EufCma.Ed25519PublicKey :=
  native.owners.map fun owner => (setup.joint.publicKeys owner.beacon.identity).ed25519

/-- The identity public key of every encoded owner, in creation order. -/
def encodedIdentities (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    List PqxdhEd25519EufCma.Ed25519PublicKey :=
  owners.map fun entry => entry.2.2.beacon.identity.2

/-- CE-A2pub event: some successful accept of the transcript carries a raw candidate that the source attached verification of `crypto` accepts with the identity key of some created owner and a key tuple that is not the tuple of that owner's published bundle (or that owner published no bundle). -/
def PublishedForgery (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) : Prop :=
  ∃ (raw : Pqxdh.Bytes) (session : Nat),
    (⟨.inl (.inr (.accept raw)), some session⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript ∧
    ∃ candidate identity decoded owner, PqxdhDeploymentTranscript.candidateOf codec raw = some candidate ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some (identity, decoded) ∧
      identities[owner]? = some identity ∧ publishedTuple codec transcript owner ≠ some decoded

/-- The terminal batches raise the report flag for a reported candidate that is an original-field failure in the snapshot they start from. -/
theorem announceAll_detects (joint : Primitives) (count target : Nat) (candidates : List PqxdhEd25519EufCma.Phase1Candidate)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (member : candidate ∈ candidates)
    (state : PqxdhJointPhase1Reports.Monitor count × PqxdhDynamicIdentityReports.ReportingState count)
    (failure : PqxdhJointPhase1Reports.FieldOriginFailure joint ⟨target, candidate⟩ state.1.snapshot)
    (after : Unit × (PqxdhJointPhase1Reports.Monitor count × PqxdhDynamicIdentityReports.ReportingState count))
    (supported : after ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (PqxdhDeploymentProvenance.announceAll count candidates)).run state)) :
    after.2.1.occurred = true := by
  induction candidates generalizing state with
  | nil => simp at member
  | cons head rest ih =>
      simp only [PqxdhDeploymentProvenance.announceAll, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, second⟩ := supported
      obtain ⟨snapshot, occurred⟩ := PqxdhRegistrationJointTerminalReports.source_batch joint count (List.range count)
        head state middle first
      rcases List.mem_cons.mp member with same | later
      · subst same
        have raised : middle.2.1.occurred = true := by
          rw [occurred, Bool.or_eq_true]
          exact Or.inr (List.any_eq_true.mpr ⟨target, List.mem_range.mpr failure.1,
            (PqxdhJointPhase1Reports.candidateAccepted_iff joint ⟨target, candidate⟩ state.1.snapshot).mpr failure⟩)
        exact PqxdhDeploymentAcceptDetection.run_sticky joint count _ middle.2 raised after second
      · exact ih later middle.2 (by rw [snapshot]; exact failure) second

/-- At the end of the report-instrumented initialized execution of the compiled program, on a run without a rejected bundle call in Fresh, a published-tuple forgery of the final transcript is an original-field failure, in the final report snapshot, of the raw candidate of one of the transcript's successful accepts at a generated report position below the creation cap. -/
theorem published_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (reached : PqxdhRegistrationJointInitializedReports.ReportResult KemSK A
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) (budget.create + 1))
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint (budget.create + 1)
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none (budget.create + 1)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local))
    (finished : (PqxdhRegistrationJointInitializedReports.sourceResult reached).1 = some encoded)
    (forgery : PublishedForgery setup.source.crypto codec encoded.2.1.1.2.transcript
      (encodedIdentities encoded.2.2.owners))
    (clean : PqxdhDeploymentTranscript.NoBundleFailure encoded.2.1.1.2.transcript) :
    ∃ target candidate, target < budget.create + 1 ∧
      candidate ∈ PqxdhDeploymentProvenance.acceptedCandidates codec (PqxdhDeploymentProvenance.finalTranscript reached.1) ∧
      PqxdhJointPhase1Reports.FieldOriginFailure setup.joint ⟨target, candidate⟩ reached.2.1.snapshot := by
  obtain ⟨raw, session, entryMember, candidate, identity, decoded, owner, parsed, accepted, identityFound,
    notPublished⟩ := forgery
  obtain ⟨original, _, actual, encodedSame, _⟩ := PqxdhRegistrationJointInitializedReports.successful_witness setup
    codec checks ensureInit none (budget.create + 1) _ runtime reached supported encoded finished
  subst encodedSame
  change publishedTuple codec original.2.1.1.2.transcript owner ≠ some decoded at notPublished
  change (⟨.inl (.inr (.accept raw)), some session⟩ : PqxdhDeploymentInterface.Entry) ∈ original.2.1.1.2.transcript
    at entryMember
  change PqxdhDeploymentTranscript.NoBundleFailure original.2.1.1.2.transcript at clean
  have pool : original.2.2.pool = (PqxdhRegistrationJointInitializedReports.sourceResult reached).2.1 :=
    PqxdhRegistrationJointInitializedReports.outcome_pool reached _ finished
  have identityLookup : ∃ entry, original.2.2.owners[owner]? = some entry ∧
      identity = (setup.joint.publicKeys entry.owner.beacon.identity).ed25519 := by
    simp only [encodedIdentities, PqxdhRegistrationJointInitializedSchedule.encodeOutcome,
      PqxdhRegistrationJointGeneratedFinish.encodeState, List.map_map, List.getElem?_map,
      Option.map_eq_some_iff] at identityFound
    obtain ⟨entry, entryFound, same⟩ := identityFound
    exact ⟨entry, entryFound, same.symm⟩
  obtain ⟨entry, entryFound, rfl⟩ := identityLookup
  have signed := PqxdhDeploymentSigningHistory.signed_source setup codec checks route ensureInit bounds mode adversary
    runtime _ actual original rfl
  have seedFound : original.2.2.pool.1.seeds[entry.identityIndex]? = some entry.owner.beacon.identity :=
    (signed.owned entry (List.mem_of_getElem? entryFound)).1
  have detached : PqxdhEd25519EufCma.acceptPhase1Candidate setup.joint.verify candidate =
      some ((setup.joint.publicKeys entry.owner.beacon.identity).ed25519, decoded) := by
    rw [← PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
      (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        shortRejects)]
    exact accepted
  have unissued : ∃ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
      field.message ∉ PqxdhRegistrationJointSigningTranscript.messagesAt entry.identityIndex
        original.2.2.pool.1.transcript := by
    rcases PqxdhDeploymentSigningHistory.signing_history setup codec checks route ensureInit bounds mode adversary
        runtime _ actual original rfl owner entry entryFound (clean owner) with
      ⟨_, empty⟩ | ⟨bytes, keys, published, written, messages⟩
    · obtain ⟨_, pqSignature, _, _, pqAttached, _⟩ := PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness
        setup.joint.verify candidate _ decoded detached
      refine ⟨⟨PqxdhEd25519EufCma.pqMessage decoded.pqKey, pqSignature⟩, ?_, by rw [empty]; simp⟩
      simp [PqxdhJointPhase1Reports.candidateFields, pqAttached]
    · have tuple : publishedTuple codec original.2.1.1.2.transcript owner = some keys := by
        simp only [publishedTuple, published, Option.bind_some,
          PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, candidateTuple_signed]
      have different : decoded ≠ keys := fun same => notPublished (by rw [tuple, same])
      by_contra issued
      push Not at issued
      have fixed : PqxdhRegistrationJointIssuedAttempts.Fixed keys.prekey keys.pqKey [keys] := by
        intro other member
        rw [List.mem_singleton] at member
        subst member
        exact ⟨rfl, rfl⟩
      have all : ∀ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
          field.message ∈ PqxdhRegistrationJointIssuedAttempts.history [keys] := by
        intro field member
        have present := issued field member
        rw [messages] at present
        simpa [PqxdhRegistrationJointIssuedAttempts.history] using present
      have origin := PqxdhRegistrationJointIssuedAttempts.accepted_origin setup.joint _ candidate decoded [keys]
        keys.prekey keys.pqKey fixed detached all
      exact different (List.mem_singleton.mp origin)
  have refFound : ∃ ref, reached.1.2.refs[entry.identityIndex]? = some ref := by
    have seeds := seedFound
    rw [pool] at seeds
    change (reached.1.2.refs.map (PqxdhRegistrationJointIdentityRouting.resolve reached.2.2.source.2.seeds))[
      entry.identityIndex]? = some _ at seeds
    rw [List.getElem?_map, Option.map_eq_some_iff] at seeds
    obtain ⟨ref, refFound, _⟩ := seeds
    exact ⟨ref, refFound⟩
  obtain ⟨ref, refFound⟩ := refFound
  obtain ⟨target, rfl⟩ := report_generated setup codec checks ensureInit (budget.create + 1) _ runtime reached supported
    entry.identityIndex ref refFound
  have creates := PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit none
    (budget.create + 1) (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime
    (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
  have bound := generated_lt setup codec checks ensureInit (budget.create + 1) _ runtime
    (creates.mono (by simp [PqxdhDeploymentCompileCaps.transported]; omega)) reached supported entry.identityIndex target
    refFound
  have quiet := PqxdhDeploymentQuiet.quiet_initialized setup codec checks ensureInit none
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
    (PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary 0 (by decide))
    (PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary 1 (by decide))
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) PqxdhDeploymentQuiet.quiet_empty _ actual
  refine ⟨target, candidate, bound, ?_, ?_⟩
  · change (reached.1.1.1.map _) = some _ at finished
    obtain ⟨outcome, outcomeFound, same⟩ := Option.map_eq_some_iff.mp finished
    simp only [PqxdhDeploymentProvenance.finalTranscript, outcomeFound, Option.map_some, Option.getD_some]
    have transcript : outcome.2.1.1.2.transcript = original.2.1.1.2.transcript := by
      have projected := congrArg (fun value => value.2.1.1.2.transcript) same
      simpa [PqxdhRegistrationJointOpenInitialization.attach,
        PqxdhRegistrationJointInitializedSchedule.encodeOutcome] using projected
    rw [transcript]
    exact List.mem_filterMap.mpr ⟨_, entryMember, parsed⟩
  · apply PqxdhRegistrationJointInitializedReports.field_origin setup codec checks ensureInit none (budget.create + 1)
      _ runtime reached supported entry.identityIndex ⟨target, bound⟩ refFound
      (setup.joint.publicKeys entry.owner.beacon.identity) candidate decoded
    · rw [← pool]
      simp [PqxdhDynamicIdentityReports.sourceKeys, seedFound]
    · exact detached
    · exact PqxdhDeploymentQuiet.unrevealed_of_quiet _ quiet _
    · rw [← pool]
      exact unissued

/-- Merging the compiled program's local record copies changes no owner identity. -/
theorem identities_merge (setup : Setup baseSpec KemSK) (copies : PqxdhDeploymentCompile.Local)
    (native : PqxdhRegistrationSchedule.State KemSK) :
    ownerIdentities setup (PqxdhDeploymentCompile.merge copies native).native = ownerIdentities setup native := by
  apply List.ext_getElem?
  intro index
  simp only [ownerIdentities, PqxdhDeploymentCompile.merge, List.getElem?_map, List.getElem?_mapIdx]
  cases found : native.owners[index]? with
  | none => rfl
  | some owner =>
      simp only [Option.map_some, Option.some.injEq]
      unfold PqxdhDeploymentCompile.mergeOwner
      split <;> rfl

/-- Encoding an owner keeps its identity public key. -/
theorem identities_encode (setup : Setup baseSpec KemSK) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    encodedIdentities (PqxdhRegistrationJointGeneratedFinish.encodeState setup state).owners =
      ownerIdentities setup (PqxdhRegistrationJointSchedule.source state) := by
  simp only [encodedIdentities, ownerIdentities, PqxdhRegistrationJointGeneratedFinish.encodeState,
    PqxdhRegistrationJointSchedule.source, List.map_map]
  rfl

/-- The A2pub event on a report-run outcome of the compiled program: a published-tuple forgery of the final transcript under the encoded owners' identity keys, on a run without a rejected bundle call in Fresh. -/
def ReportEvent (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) {count : Nat}
    (reached : PqxdhRegistrationJointInitializedReports.ReportResult KemSK A
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) count) : Prop :=
  ∃ encoded, (PqxdhRegistrationJointInitializedReports.sourceResult reached).1 = some encoded ∧
    PublishedForgery crypto codec encoded.2.1.1.2.transcript (encodedIdentities encoded.2.2.owners) ∧
    PqxdhDeploymentTranscript.NoBundleFailure encoded.2.1.1.2.transcript

/-- The A2pub event on an outcome of the deployment experiment: a published-tuple forgery of the final transcript under the owners' identity keys, on a run without a rejected bundle call in Fresh. -/
def GameEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PublishedForgery setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) ∧
    PqxdhDeploymentTranscript.NoBundleFailure final.1.transcript

/-- The A2pub event on a decoded report-run outcome. -/
def DecodedEvent (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (result : Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local)) ×
        PqxdhRegistrationJointServerPrefix.State KemSK A) : Prop :=
  ∃ encoded, result.1 = some encoded ∧
    PublishedForgery crypto codec encoded.2.1.1.2.transcript (encodedIdentities encoded.2.2.owners) ∧
    PqxdhDeploymentTranscript.NoBundleFailure encoded.2.1.1.2.transcript

set_option linter.deprecated false in
/-- The A2pub event of the deployment experiment has exactly the probability of the A2pub event of the report-instrumented initialized execution of the compiled program. -/
theorem game_report (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (count : Nat) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun outcome => decide (GameEvent setup codec outcome)) <$> (PqxdhDeploymentSecrecy.game setup codec checks
        route ensureInit 0 bounds mode adversary).run runtime] {true} =
      𝒟[(fun reached => decide (ReportEvent setup.source.crypto codec reached)) <$>
        PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec
          checks ensureInit none count (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
            adversary) runtime)] {true} := by
  classical
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]
  have compiled := PqxdhDeploymentCompileSecrecy.compile_full_source setup codec checks route ensureInit phase1 phase2
    bounds mode adversary ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  simp only [PqxdhDynamicIdentityPool.initialState, List.length_nil] at compiled
  have reported := PqxdhRegistrationJointReportSource.initialized_source setup codec checks ensureInit none count
    (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime
  have decoded : Pr[ReportEvent (A := A) setup.source.crypto codec (count := count) | PqxdhJointPhase1Reports.run
      setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit none count
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime)] =
      Pr[DecodedEvent setup.source.crypto codec | (fun result =>
        PqxdhRegistrationJointIdentityCompiler.initializedResult (result.1, result.2.2.source.2)) <$>
          PqxdhJointPhase1Reports.run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec
            checks ensureInit none count (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
              adversary) runtime)] := by
    rw [probEvent_map]
    rfl
  rw [decoded, reported, probEvent_map, ← compiled, probEvent_map]
  congr 1
  funext result
  rcases result with ⟨_ | outcome, after⟩
  · simp [GameEvent, DecodedEvent, PqxdhDeploymentCompileSecrecy.mergeFull]
  · simp only [Function.comp_apply, GameEvent, DecodedEvent, PqxdhDeploymentCompileSecrecy.mergeFull, Option.map_some,
      Option.some.injEq, PqxdhRegistrationJointInitializedSchedule.eraseOutcome,
      PqxdhRegistrationJointInitializedSchedule.encodeOutcome]
    apply propext
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl⟩, forged, clean⟩
      refine ⟨_, rfl, ?_, clean⟩
      rw [identities_encode]
      rwa [identities_merge] at forged
    · rintro ⟨_, rfl, forged, clean⟩
      refine ⟨_, _, _, rfl, ?_, clean⟩
      rw [identities_merge]
      rwa [identities_encode] at forged

set_option linter.deprecated false in
/-- Theorem CE-A2pub (published-tuple provenance, on `NoBundleFailure` runs, no selection factor). For a deployment adversary in either mode that respects its budget, with a generated Server seed, the probability that the run has no rejected bundle call made in Fresh and yet some successful accept carries a raw candidate that the source attached verification accepts with the identity key of some created owner and a key tuple other than the tuple of that owner's published bundle (or that owner published none) is at most the same sum over the `qCreate + 1` generated identity positions of the ordinary joint-use weak-EUF advantages of the A2 client's reductions as CE-A2. The premises are `shortRejects` with `setup.wiring`, the approved codec laws `Phase1ReadBack` and `Phase2ReadBack`, and the adversary's budget. -/
theorem a2pub_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun outcome => decide (GameEvent setup codec outcome)) <$> (PqxdhDeploymentSecrecy.game setup codec checks
        route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  classical
  rw [game_report setup codec checks route ensureInit phase1 phase2 bounds mode adversary (budget.create + 1) runtime,
    evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  have transfer := PqxdhDeploymentProvenance.client_transfer setup codec checks route ensureInit bounds mode adversary
    (budget.create + 1) runtime (ReportEvent setup.source.crypto codec) (by
      intro reached member happened after afterMember
      obtain ⟨encoded, finished, forged, clean⟩ := happened
      obtain ⟨target, candidate, _, candidateMember, failure⟩ := published_failure setup codec checks shortRejects
        phase1 route ensureInit bounds mode adversary budget respects runtime reached member encoded finished forged clean
      exact announceAll_detects setup.joint (budget.create + 1) target _ candidate candidateMember reached.2 failure
        after afterMember)
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map] at transfer
  have creates := PqxdhDeploymentProvenance.client_creates setup codec checks route ensureInit bounds mode adversary
    budget respects (budget.create + 1) runtime
  have field := PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint budget.create
    (PqxdhDeploymentProvenance.client setup codec checks route ensureInit bounds mode adversary (budget.create + 1)
      runtime) fallback ordinaryFallback (creates.mono (by omega))
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map] at transfer
  exact le_trans transfer field

/-- A partial map whose image list has no duplicate sends no two positions of the list to the same value. -/
theorem filterMap_nodup_ne {α β : Type} (f : α → Option β) (list : List α) (unique : (list.filterMap f).Nodup)
    (first second : Nat) (different : first ≠ second) (left right : α) (leftFound : list[first]? = some left)
    (rightFound : list[second]? = some right) (value : β) (leftMapped : f left = some value)
    (rightMapped : f right = some value) : False := by
  induction list generalizing first second with
  | nil => simp at leftFound
  | cons head tail ih =>
      have tailUnique : (tail.filterMap f).Nodup := by
        rw [List.filterMap_cons] at unique
        split at unique
        · exact unique
        · exact (List.nodup_cons.mp unique).2
      cases first with
      | zero =>
          cases second with
          | zero => exact different rfl
          | succ second =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at leftFound
              subst leftFound
              rw [List.filterMap_cons, leftMapped, List.nodup_cons] at unique
              exact unique.1 (List.mem_filterMap.mpr ⟨right, List.mem_of_getElem? rightFound, rightMapped⟩)
      | succ first =>
          cases second with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at rightFound
              subst rightFound
              rw [List.filterMap_cons, rightMapped, List.nodup_cons] at unique
              exact unique.1 (List.mem_filterMap.mpr ⟨left, List.mem_of_getElem? leftFound, leftMapped⟩)
          | succ second =>
              exact ih tailUnique first second (fun same => different (by rw [same])) leftFound rightFound

/-- CE-R1' event: two successful accepts at distinct transcript positions carry raw candidates that the source attached verification accepts with the identity key of one created owner. -/
def DoubleAccept (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) : Prop :=
  ∃ (first second : Nat), first ≠ second ∧
    ∃ (raw raw' : Pqxdh.Bytes) (session session' : Nat) (candidate candidate' : PqxdhEd25519EufCma.Phase1Candidate)
      (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys keys' : PqxdhEd25519EufCma.Phase1KeyTuple) (owner : Nat),
      transcript[first]? = some ⟨.inl (.inr (.accept raw)), some session⟩ ∧
      transcript[second]? = some ⟨.inl (.inr (.accept raw')), some session'⟩ ∧
      PqxdhDeploymentTranscript.candidateOf codec raw = some candidate ∧
      PqxdhDeploymentTranscript.candidateOf codec raw' = some candidate' ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some (identity, keys) ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto candidate' = some (identity, keys') ∧
      identities[owner]? = some identity

/-- The CE-R1' event on an outcome of the deployment experiment, on a run without a rejected bundle call in Fresh. -/
def ReplayEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    DoubleAccept setup.source.crypto codec final.1.transcript (ownerIdentities setup final.2.native) ∧
    PqxdhDeploymentTranscript.NoBundleFailure final.1.transcript

/-- On every outcome of the experiment, two successful accepts under one owner's identity on a `NoBundleFailure` run make one of them a published-tuple forgery: if both carried the owner's published tuple they would carry one registration ID, which the live Server object consumes once (CE-R1). -/
theorem replay_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (replayed : ReplayEvent setup codec outcome) : GameEvent setup codec outcome := by
  obtain ⟨created, output, final, reached, ⟨first, second, different, raw, raw', session, session', candidate, candidate',
    identity, keys, keys', owner, firstFound, secondFound, parsed, parsed', accepted, accepted', identityFound⟩,
    clean⟩ := replayed
  refine ⟨created, output, final, reached, ?_, clean⟩
  by_contra notForged
  have firstTuple : publishedTuple codec final.1.transcript owner = some keys := by
    by_contra other
    exact notForged ⟨raw, session, List.mem_of_getElem? firstFound, candidate, identity, keys, owner, parsed, accepted,
      identityFound, other⟩
  have secondTuple : publishedTuple codec final.1.transcript owner = some keys' := by
    by_contra other
    exact notForged ⟨raw', session', List.mem_of_getElem? secondFound, candidate', identity, keys', owner, parsed',
      accepted', identityFound, other⟩
  have same : keys' = keys := Option.some.inj (secondTuple.symm.trans firstTuple)
  subst same
  have registered := PqxdhDeploymentReplay.registered_game setup codec checks route ensureInit identityIndex bounds mode
    adversary runtime outcome supported created output final reached
  exact filterMap_nodup_ne (PqxdhDeploymentReplay.entryRegistration setup.source.crypto codec) final.1.transcript
    registered.unique first second different _ _ firstFound secondFound
    (identity.toList ++ keys'.oneTime.toList)
    (by simp [PqxdhDeploymentReplay.entryRegistration, PqxdhDeploymentReplay.registrationOf, parsed, accepted])
    (by simp [PqxdhDeploymentReplay.entryRegistration, PqxdhDeploymentReplay.registrationOf, parsed', accepted'])

set_option linter.deprecated false in
/-- Theorem CE-R1' (published-tuple replay, on `NoBundleFailure` runs). For a deployment adversary in either mode that respects its budget, with a generated Server seed, the probability that the run has no rejected bundle call made in Fresh and yet two successful accepts at distinct positions carry raw candidates accepted under one created owner's identity key is at most the CE-A2pub bound: the same sum over the `qCreate + 1` generated identity positions of the A2 client's joint-use weak-EUF advantages. -/
theorem r1prime_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun outcome => decide (ReplayEvent setup codec outcome)) <$> (PqxdhDeploymentSecrecy.game setup codec checks
        route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup codec checks route ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  classical
  refine le_trans ?_ (a2pub_bound setup codec checks shortRejects phase1 phase2 route ensureInit bounds mode adversary
    budget respects runtime fallback ordinaryFallback)
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro outcome member replayed
  simp only [Function.comp_apply, decide_eq_true_eq] at replayed ⊢
  exact replay_published setup codec checks route ensureInit 0 bounds mode adversary runtime outcome member replayed

end BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.run_inv_of_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.run_inv_of_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.simulate_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.simulate_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.simulateQ_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.simulateQ_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.initialized_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.initialized_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.lift_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.lift_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.compiled_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.compiled_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.route_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.route_generated

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.report_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.report_generated

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.pool_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.pool_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.reporting_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.reporting_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.source_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.source_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.generated_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.generated_lt

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.candidateTuple_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.candidateTuple_signed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.announceAll_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.announceAll_detects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.published_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.published_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.identities_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.identities_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.identities_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.identities_encode

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.game_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.game_report

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.a2pub_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.a2pub_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.filterMap_nodup_ne' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.filterMap_nodup_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.replay_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.replay_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.r1prime_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple.r1prime_bound
