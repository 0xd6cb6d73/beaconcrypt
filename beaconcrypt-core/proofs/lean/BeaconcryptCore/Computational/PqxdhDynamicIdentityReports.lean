import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting

/-!
# Dynamic signature reports with later identity compromise

Public creation replies and actual service/reveal replies determine the monitor state. The source permits arbitrary reports and subsequent compromises; a public stopping client selects its first fresh valid reported signature. Native report points, byte-based lookup and root/record reveal policies remain separate interfaces.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicIdentityReports

open PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool (DynamicSpec PoolQuery)
open PqxdhDynamicIdentityRouting (DynamicForgery dynamicClass)

/-- Only public creation replies and actual public service/reveal history are retained by the stopping client. -/
structure PublicSnapshot (count : ℕ) where
  keys : ℕ → Option PublicIdentity
  history : GlobalState count

/-- The source's generated-index map, used only to prove equality to observed public creation replies. -/
def sourceKeys (primitives : Primitives) (seeds : List IdentitySeed) : ℕ → Option PublicIdentity :=
  fun index => seeds[index]?.map primitives.publicKeys

/-- The complete source state determines the same public snapshot; this projection is never a seed service. -/
def sourceSnapshot (primitives : Primitives) {count : ℕ}
    (state : GlobalState count × PqxdhDynamicIdentityPool.SourceState) : PublicSnapshot count :=
  ⟨sourceKeys primitives state.2.seeds, state.1⟩

/-- An actual creation publishes one new public key at the next generated index. -/
def observeKeys (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (keys : ℕ → Option PublicIdentity) : ℕ → Option PublicIdentity :=
  match query with
  | .inr .create => match answer with
    | none => keys
    | some (index, publicKey) => Function.update keys index (some publicKey)
  | _ => keys

/-- Service and compromise histories are derived from actual replies. In particular a rejected reveal does not compromise the future identity at that index. -/
def observe {count : ℕ} (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (state : PublicSnapshot count) : PublicSnapshot count :=
  ⟨observeKeys query answer state.keys,
    PqxdhDynamicIdentityRouting.historyUpdate count query answer state.history⟩

/-- Appending a generated private seed changes exactly the newly published public index, even when key bytes collide with an earlier identity. -/
theorem sourceKeys_append (primitives : Primitives) (seeds : List IdentitySeed) (seed : IdentitySeed) :
    sourceKeys primitives (seeds ++ [seed]) =
      Function.update (sourceKeys primitives seeds) seeds.length (some (primitives.publicKeys seed)) := by
  funext index
  by_cases earlier : index < seeds.length
  · simp [sourceKeys, List.getElem?_append_left earlier, Nat.ne_of_lt earlier]
  · by_cases next : index = seeds.length
    · subst index
      simp [sourceKeys]
    · have later : seeds.length < index := by omega
      have after : (seeds ++ [seed]).length ≤ index := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [sourceKeys, Function.update_of_ne next, List.getElem?_eq_none after,
        List.getElem?_eq_none (Nat.le_of_lt later), Option.map_none]

/-- Non-creation source requests leave the public key map unchanged and expose no reserved future identity. -/
theorem observeKeys_noncreate (query : DynamicSpec.Domain)
    (notCreate : ¬PqxdhDynamicIdentityPool.IsCreate query) (answer : DynamicSpec.Range query)
    (keys : ℕ → Option PublicIdentity) : observeKeys query answer keys = keys := by
  cases query with
  | inl coin => rfl
  | inr request => cases request <;> simp_all [PqxdhDynamicIdentityPool.IsCreate, observeKeys]

/-- Every actual source step yields the same public snapshot that the stopping client computes from the returned value. -/
theorem source_snapshot_step (primitives : Primitives) (count : ℕ) (query : DynamicSpec.Domain)
    (state : GlobalState count × PqxdhDynamicIdentityPool.SourceState)
    (result : DynamicSpec.Range query × (GlobalState count × PqxdhDynamicIdentityPool.SourceState))
    (supported : result ∈ support ((PqxdhDynamicIdentityRouting.sourceWithHistory count
      (PqxdhDynamicIdentityPool.lazyImpl primitives) query).run state)) :
    sourceSnapshot primitives result.2 = observe query result.1 (sourceSnapshot primitives state) := by
  rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run] at supported
  obtain ⟨reply, actual, finished⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
  by_cases creates : PqxdhDynamicIdentityPool.IsCreate query
  · have queryEq : query = .inr .create := by
      cases query with
      | inl coin => exact False.elim creates
      | inr request => cases request <;> simp_all [PqxdhDynamicIdentityPool.IsCreate]
    subst query
    rw [PqxdhDynamicIdentityPool.lazyImpl_create] at actual
    obtain ⟨seed, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ actual
    simp only [sourceSnapshot, observe, observeKeys,
      PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, sourceKeys_append]
  · have kept := PqxdhDynamicIdentityPool.noncreate_seeds_preserved primitives query creates state.2 reply actual
    simp only [sourceSnapshot, observe, kept, observeKeys_noncreate query creates]

/-- A report is checked against a publicly observed generated key and its then-current actual signing/reveal history. -/
def reportAccepted (primitives : Primitives) {count : ℕ} (candidate : DynamicForgery)
    (state : PublicSnapshot count) : Bool :=
  if valid : candidate.identity < count then
    match state.keys candidate.identity with
    | none => false
    | some publicKey => decide (⟨candidate.identity, valid⟩ ∉ state.history.reveals) &&
        wins primitives publicKey candidate.forgery (state.history.histories ⟨candidate.identity, valid⟩)
  else false

/-- On the actual source snapshot, public report recognition is exactly the explicit generated-target signature event. -/
theorem reportAccepted_iff_source (primitives : Primitives) {count : ℕ} (candidate : DynamicForgery)
    (state : GlobalState count × PqxdhDynamicIdentityPool.SourceState) :
    reportAccepted primitives candidate (sourceSnapshot primitives state) = true ↔
      PqxdhDynamicIdentityRouting.DynamicEvent primitives (candidate, state) := by
  change reportAccepted primitives candidate
    (⟨sourceKeys primitives state.2.seeds, state.1⟩ : PublicSnapshot count) = true ↔ _
  by_cases valid : candidate.identity < count
  · cases lookup : state.2.seeds[candidate.identity]? with
    | none => simp [reportAccepted, sourceKeys, lookup, valid,
        PqxdhDynamicIdentityRouting.DynamicEvent, Fresh]
    | some seed => simp [reportAccepted, sourceKeys, lookup, valid,
        PqxdhDynamicIdentityRouting.DynamicEvent, Fresh]
  · simp [reportAccepted, valid, PqxdhDynamicIdentityRouting.DynamicEvent, Fresh]

abbrev ReportSpec : OracleSpec DynamicForgery := fun _ => Unit
abbrev ReportingSpec := DynamicSpec + ReportSpec

/-- Each report retains its unchanged candidate, publicly recognized result and exact position among source query/reply observations. -/
structure ReportObservation where
  sourceQueries : ℕ
  candidate : DynamicForgery
  accepted : Bool

/-- The real source retains every private state and public observation, all unchanged reported candidates, and a sticky event bit. -/
structure ReportingState (count : ℕ) where
  source : GlobalState count × PqxdhDynamicIdentityPool.SourceState
  publicSnapshot : PublicSnapshot count
  occurred : Bool
  reported : List ReportObservation

/-- Reports use only observed public keys and history. Later real service requests, creation and seed reveals remain unrestricted. -/
def reportingImpl (primitives : Primitives) (count : ℕ) :
    QueryImpl ReportingSpec (StateT (ReportingState count) ProbComp) := fun query state =>
  match query with
  | .inl request => do
    let (answer, source) ← (PqxdhDynamicIdentityRouting.sourceWithHistory count
      (PqxdhDynamicIdentityPool.lazyImpl primitives) request).run state.source
    pure (answer, { state with source, publicSnapshot := observe request answer state.publicSnapshot })
  | .inr candidate => pure ((), { state with
      occurred := state.occurred || reportAccepted primitives candidate state.publicSnapshot,
      reported := state.reported ++ [⟨state.source.2.transcript.length, candidate,
        reportAccepted primitives candidate state.publicSnapshot⟩] })

/-- The exact dependent reply type keeps report-interface state transitions explicit. -/
def reportedReply (primitives : Primitives) (count : ℕ) (candidate : DynamicForgery)
    (state : ReportingState count) : ReportingSpec.Range (.inr candidate) × ReportingState count :=
  ((), { state with
    occurred := state.occurred || reportAccepted primitives candidate state.publicSnapshot,
    reported := state.reported ++ [⟨state.source.2.transcript.length, candidate,
      reportAccepted primitives candidate state.publicSnapshot⟩] })

/-- The exact report poststate retains public recognition and its position in the source transcript. -/
theorem reportingImpl_report (primitives : Primitives) (count : ℕ) (candidate : DynamicForgery)
    (state : ReportingState count) :
    (reportingImpl primitives count (.inr candidate)).run state =
      pure (reportedReply primitives count candidate state) := rfl

/-- Public report recognition stops before later compromise; earlier source replies remain exact, and no private seed is supplied to this stopping client. -/
def stopAtFreshReport (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ReportingSpec Result) (state : PublicSnapshot count) :
    OracleComp DynamicSpec (Option DynamicForgery) :=
  OracleComp.recOn client (fun _ _ => pure none)
    (fun query _ recurse state => match query with
      | .inl request => do
        let answer ← DynamicSpec.query request
        recurse answer (observe request answer state)
      | .inr candidate =>
        if reportAccepted primitives candidate state then pure (some candidate)
        else recurse () state) state

@[simp] theorem stop_pure (primitives : Primitives) (count : ℕ) {Result : Type}
    (value : Result) (state : PublicSnapshot count) :
    stopAtFreshReport primitives count (pure value) state = pure none := rfl

@[simp] theorem stop_service (primitives : Primitives) (count : ℕ) {Result : Type}
    (request : DynamicSpec.Domain) (next : DynamicSpec.Range request → OracleComp ReportingSpec Result)
    (state : PublicSnapshot count) :
    stopAtFreshReport primitives count (ReportingSpec.query (.inl request) >>= next) state =
      (do let answer ← DynamicSpec.query request
          stopAtFreshReport primitives count (next answer) (observe request answer state)) := rfl

@[simp] theorem stop_report (primitives : Primitives) (count : ℕ) {Result : Type}
    (candidate : DynamicForgery) (next : Unit → OracleComp ReportingSpec Result)
    (state : PublicSnapshot count) :
    stopAtFreshReport primitives count (ReportingSpec.query (.inr candidate) >>= next) state =
      if reportAccepted primitives candidate state then pure (some candidate)
      else stopAtFreshReport primitives count (next ()) state := rfl

/-- A stopped output is the exact candidate and actual source state at the publicly recognized report. -/
def StoppedEvent (primitives : Primitives) {count : ℕ}
    (result : Option DynamicForgery × (GlobalState count × PqxdhDynamicIdentityPool.SourceState)) : Prop :=
  match result.1 with
  | none => False
  | some candidate => PqxdhDynamicIdentityRouting.DynamicEvent primitives (candidate, result.2)

/-- An earlier fresh signature event remains captured even when the full source continues to create identities and reveal the reported target afterward. -/
theorem occurred_probability_le_stopped (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ReportingSpec Result)
    (source : GlobalState count × PqxdhDynamicIdentityPool.SourceState) (reported : List ReportObservation) :
    Pr{let result ← (simulateQ (reportingImpl primitives count) client).run
        ⟨source, sourceSnapshot primitives source, false, reported⟩}[result.2.occurred = true] ≤
      Pr{let result ← (simulateQ
          (PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives))
          (stopAtFreshReport primitives count client (sourceSnapshot primitives source))).run source}[
        StoppedEvent primitives result] := by
  classical
  induction client using OracleComp.inductionOn generalizing source reported with
  | pure value =>
      rw [simulateQ_pure, StateT.run_pure, prEvent_pure, ite_eq_right (by simp)]
      exact zero_le
  | query_bind query next ih =>
    cases query with
    | inl request =>
      rw [stop_service]
      simp only [simulateQ_query_bind, StateT.run_bind]
      change Pr{let result ←
          (((PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)
            request).run source >>= fun reply => pure (reply.1,
              ReportingState.mk reply.2 (observe request reply.1 (sourceSnapshot primitives source)) false
                reported)) >>=
            fun reply => (simulateQ (reportingImpl primitives count) (next reply.1)).run reply.2)}[
          result.2.occurred = true] ≤
        Pr{let result ←
          ((PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)
            request).run source >>= fun reply => (simulateQ
              (PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives))
              (stopAtFreshReport primitives count (next reply.1)
                (observe request reply.1 (sourceSnapshot primitives source)))).run reply.2)}[
          StoppedEvent primitives result]
      have shape :
          (((PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)
            request).run source >>= fun reply => pure (reply.1,
              ReportingState.mk reply.2 (observe request reply.1 (sourceSnapshot primitives source)) false
                reported)) >>=
            fun reply => (simulateQ (reportingImpl primitives count) (next reply.1)).run reply.2) =
          ((PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives)
            request).run source >>= fun reply => (simulateQ (reportingImpl primitives count) (next reply.1)).run
              (ReportingState.mk reply.2 (observe request reply.1 (sourceSnapshot primitives source)) false
                reported)) := by
        simp only [bind_assoc, pure_bind]
      rw [shape]
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun reply supported => ?_
      have actual := source_snapshot_step primitives count request source reply supported
      rw [← actual]
      exact ih reply.1 reply.2 reported
    | inr candidate =>
      rw [stop_report]
      by_cases accepted : reportAccepted primitives candidate (sourceSnapshot primitives source) = true
      · have event := (reportAccepted_iff_source primitives candidate source).mp accepted
        rw [ite_eq_left accepted, simulateQ_pure, StateT.run_pure, prEvent_pure,
          ite_eq_left (show StoppedEvent primitives (some candidate, source) from event)]
        exact prEvent_le_one _
      · have rejected : reportAccepted primitives candidate (sourceSnapshot primitives source) = false :=
          Bool.eq_false_iff.mpr accepted
        rw [ite_eq_right accepted]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, reportingImpl_report, pure_bind, reportedReply, rejected,
          Bool.or_self]
        apply ih () source

/-- The source starts without created identities, signing history or compromise history. -/
def initialSource (count : ℕ) : GlobalState count × PqxdhDynamicIdentityPool.SourceState :=
  ⟨PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState⟩

def initialSnapshot (count : ℕ) : PublicSnapshot count :=
  ⟨fun _ => none, PqxdhJointIdentityFreshness.initialState count⟩

theorem initial_snapshot (primitives : Primitives) (count : ℕ) :
    sourceSnapshot primitives (initialSource count) = initialSnapshot count := rfl

/-- The full source retains every report and permits arbitrary later compromise. -/
def reportingRun (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ReportingSpec Result) : ProbComp (Result × ReportingState count) :=
  (simulateQ (reportingImpl primitives count) client).run
    ⟨initialSource count, initialSnapshot count, false, []⟩

/-- The executable extractor starts with no public identities and returns the first recognized candidate unchanged. Its fallback can only enlarge the final-event probability. -/
def reportExtractor (primitives : Primitives) (count : ℕ) {Result : Type}
    (fallback : DynamicForgery) (client : OracleComp ReportingSpec Result) : OracleComp DynamicSpec DynamicForgery :=
  (fun result => result.getD fallback) <$> stopAtFreshReport primitives count client (initialSnapshot count)

/-- Earlier source report-time freshness is reduced to final freshness of the stopped source, without imposing final freshness on the original continued execution. -/
theorem reportingRun_le_extractor (primitives : Primitives) (count : ℕ) {Result : Type}
    (fallback : DynamicForgery) (client : OracleComp ReportingSpec Result) :
    Pr{let result ← reportingRun primitives count client}[result.2.occurred = true] ≤
      Pr{let result ← PqxdhDynamicIdentityRouting.dynamicRun primitives count
          (reportExtractor primitives count fallback client)}[
        PqxdhDynamicIdentityRouting.DynamicEvent primitives result] := by
  have captured := occurred_probability_le_stopped primitives count client (initialSource count) []
  rw [initial_snapshot] at captured
  apply captured.trans
  simp only [PqxdhDynamicIdentityRouting.dynamicRun, reportExtractor, simulateQ_map, StateT.run_map]
  rw [prEvent_map]
  apply prEvent_mono
  intro result accepted
  cases candidate : result.1 with
  | none => simp [StoppedEvent, candidate] at accepted
  | some forgery =>
    simpa only [StoppedEvent, candidate, Option.getD_some] using accepted

/-- Ordinary source service classes are unaffected by the additional report interface. -/
def reportingClass (predicate : DynamicSpec.Domain → Prop) : ReportingSpec.Domain → Prop
  | .inl request => predicate request
  | .inr _ => False

instance (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (reportingClass predicate) := fun query => by
  cases query with
  | inl request => exact inferInstanceAs (Decidable (predicate request))
  | inr candidate => exact inferInstanceAs (Decidable False)

/-- Stopping at the first recognized report preserves every declared source query class and forwards every earlier request exactly once. -/
theorem stop_query_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ReportingSpec Result) (predicate : DynamicSpec.Domain → Prop)
    [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (reportingClass predicate) bound) (state : PublicSnapshot count) :
    (stopAtFreshReport primitives count client state).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing bound state with
  | pure value => simp
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl request =>
      rw [stop_service, OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨bounded.1, ?_⟩
      intro answer
      exact ih answer _ (bounded.2 answer) (observe request answer state)
    | inr candidate =>
      rw [stop_report]
      split
      · trivial
      · have nextBound := bounded.2 ()
        rw [ite_eq_right (by simp only [reportingClass, not_false_eq_true])] at nextBound
        exact ih () bound nextBound state

/-- The concrete stopped extractor inherits creation, randomness, signing, DH and reveal request caps. -/
theorem extractor_query_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (fallback : DynamicForgery) (client : OracleComp ReportingSpec Result)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (reportingClass predicate) bound) :
    (reportExtractor primitives count fallback client).IsQueryBoundP predicate bound := by
  simpa only [reportExtractor, OracleComp.isQueryBoundP_map_iff] using
    stop_query_bound primitives count client predicate bound bounded (initialSnapshot count)

/-- Dynamic creation, arbitrary report timing and later compromise incur only the existing generated-identity sum of explicit joint-use weak-EUF reductions. There is no report-position guessing factor. -/
theorem reporting_advantage_le_identity_sum (primitives : Primitives) (count : ℕ) {Result : Type}
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (client : OracleComp ReportingSpec Result)
    (creates : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsCreate) (count + 1)) :
    Pr{let result ← reportingRun primitives (count + 1) client}[result.2.occurred = true] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback client))) := by
  exact (reportingRun_le_extractor primitives (count + 1) fallback client).trans
    (PqxdhDynamicIdentityRouting.dynamic_advantage_le_sum primitives count ordinaryFallback _
      (extractor_query_bound primitives (count + 1) fallback client
        PqxdhDynamicIdentityPool.IsCreate (count + 1) creates))

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_sum_vcvioLegacy :
    ∀ (primitives : BeaconcryptCore.Computational.PqxdhJointIdentity.Primitives) (count : ℕ) {Result : Type} (fallback : BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : BeaconcryptCore.Computational.PqxdhJointIdentity.Forgery) (client : OracleComp BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.ReportingSpec Result) (creates : client.IsQueryBoundP (BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingClass BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.IsCreate) (count + 1)), (probEvent (BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingRun primitives (count + 1) client) fun (result : Result × BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.ReportingState (count + 1)) => result.2.occurred = Bool.true) ≤ ∑ target : Fin (count + 1), BeaconcryptCore.Computational.PqxdhJointIdentity.advantage primitives (BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReduction primitives target ordinaryFallback (BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback (BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback client))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_sum

/-- Each constructed reduction keeps the original source primitive caps and generates only the other reserved seeds. Public report tests make no challenger query. -/
theorem reportingReduction_query_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp ReportingSpec Result) (kind : Kind) (bound : ℕ)
    (bounded : client.IsQueryBoundP (reportingClass (dynamicClass (IsClass kind))) bound)
    (jointPublic : PublicIdentity) :
    (globalReduction primitives target ordinaryFallback
      (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback client)) jointPublic).IsQueryBoundP
          (IsClass kind) ((if kind = .uniform then 32 * count else 0) + bound) :=
  PqxdhDynamicIdentityRouting.dynamicReduction_query_bound primitives count target ordinaryFallback
    (reportExtractor primitives (count + 1) fallback client) kind bound
    (extractor_query_bound primitives (count + 1) fallback client (dynamicClass (IsClass kind)) bound bounded)
    jointPublic

/-- The complete interpreted reduction additionally pays the target challenger's 32 seed draws; unused reservations and every source uniform request remain charged. -/
theorem reportingReductionGame_uniform_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp ReportingSpec Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP (reportingClass (dynamicClass (IsClass .uniform))) bound) :
    (game primitives (globalReduction primitives target ordinaryFallback
      (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback client)))).IsTotalQueryBound
          (32 * (count + 1) + bound) :=
  PqxdhDynamicIdentityRouting.dynamicReductionGame_uniform_bound primitives count target ordinaryFallback
    (reportExtractor primitives (count + 1) fallback client) bound
    (extractor_query_bound primitives (count + 1) fallback client (dynamicClass (IsClass .uniform)) bound bounded)

/-- Report attempts have a separate source class even when invalid, repeated, or after compromise. -/
def IsReport : ReportingSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsReport := fun query => by cases query <;> simp [IsReport] <;> infer_instance

/-- Exactly one report observation is appended per attempt, retaining the actual source position and public verification result. -/
theorem reportingImpl_report_count (primitives : Primitives) (count : ℕ)
    (query : ReportingSpec.Domain) (state : ReportingState count)
    (result : ReportingSpec.Range query × ReportingState count)
    (supported : result ∈ support ((reportingImpl primitives count query).run state)) :
    result.2.reported.length = state.reported.length + if IsReport query then 1 else 0 := by
  cases query with
  | inl request =>
    simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    simp [IsReport]
  | inr candidate =>
    simp only [reportingImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [IsReport]

/-- Every adaptive report attempt is charged, while source identities, histories and later compromise remain unrestricted. -/
theorem reportingExecution_report_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp ReportingSpec Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP IsReport bound) (state : ReportingState count)
    (result : Result × ReportingState count)
    (supported : result ∈ support ((simulateQ (reportingImpl primitives count) client).run state)) :
    result.2.reported.length ≤ state.reported.length + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, restSupport⟩ := supported
    have stepCount := reportingImpl_report_count primitives count query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : IsReport query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- A report makes no uniform request; actual creation and every explicit source coin retain their exact independent costs. -/
theorem reportingImpl_uniform_step (primitives : Primitives) (count : ℕ)
    (query : ReportingSpec.Domain) (state : ReportingState count) :
    ((reportingImpl primitives count query).run state).IsTotalQueryBound
      ((if reportingClass PqxdhDynamicIdentityPool.IsCreate query then 32 else 0) +
        (if reportingClass PqxdhDynamicIdentityPool.IsUniform query then 1 else 0)) := by
  cases query with
  | inl request =>
    rw [show (reportingImpl primitives count (.inl request)).run state =
      (fun result => (result.1, ReportingState.mk result.2
        (observe request result.1 state.publicSnapshot) state.occurred state.reported)) <$>
        (PqxdhDynamicIdentityRouting.sourceWithHistory count
          (PqxdhDynamicIdentityPool.lazyImpl primitives) request).run state.source from by
      simp only [reportingImpl, StateT.run, bind_pure_comp]]
    simp only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
    rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run]
    simp only [bind_pure_comp, OracleComp.isQueryBound_map_iff, reportingClass]
    convert PqxdhDynamicIdentityPool.lazyImpl_uniform_step primitives request state.source.2 using 1
    rfl
  | inr candidate => trivial

/-- Complete source randomness charges 32 byte-valued draws for each permitted creation and every explicit uniform request, from every retained source state. -/
theorem reportingExecution_uniform_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp ReportingSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsCreate) qCreate)
    (coins : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsUniform) qUniform)
    (state : ReportingState count) :
    ((simulateQ (reportingImpl primitives count) client).run state).IsTotalQueryBound
      (32 * qCreate + qUniform) := by
  induction client using OracleComp.inductionOn generalizing qCreate qUniform state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at creates coins
    change ((reportingImpl primitives count query).run state >>= fun result =>
      (simulateQ (reportingImpl primitives count) (next result.1)).run result.2).IsTotalQueryBound _
    have accounted := OracleComp.isTotalQueryBound_bind (reportingImpl_uniform_step primitives count query state)
      (fun result => ih result.1 _ _ (creates.2 result.1) (coins.2 result.1) result.2)
    apply accounted.mono
    have createPositive : reportingClass PqxdhDynamicIdentityPool.IsCreate query → 0 < qCreate :=
      fun h => creates.1.resolve_left (not_not.mpr h)
    have uniformPositive : reportingClass PqxdhDynamicIdentityPool.IsUniform query → 0 < qUniform :=
      fun h => coins.1.resolve_left (not_not.mpr h)
    by_cases hc : reportingClass PqxdhDynamicIdentityPool.IsCreate query <;>
      by_cases hu : reportingClass PqxdhDynamicIdentityPool.IsUniform query <;>
      simp [hc, hu] at createPositive uniformPositive ⊢ <;> omega

/-- The actual complete reporting experiment uses on-demand source seeds, distinct from the reduction's entire privately reserved family. -/
theorem reportingRun_uniform_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp ReportingSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsCreate) qCreate)
    (coins : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsUniform) qUniform) :
    (reportingRun primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) :=
  reportingExecution_uniform_bound primitives count client qCreate qUniform creates coins _

/-- Monitoring preserves exactly one source trace entry per original request, including rejected indices, rejected DH and repeated reveals. Reports have their separate retained observations. -/
theorem reportingImpl_trace_count (primitives : Primitives) (count : ℕ)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (query : ReportingSpec.Domain) (state : ReportingState count)
    (result : ReportingSpec.Range query × ReportingState count)
    (supported : result ∈ support ((reportingImpl primitives count query).run state)) :
    PqxdhDynamicIdentityPool.traceCount predicate result.2.source.2 =
      PqxdhDynamicIdentityPool.traceCount predicate state.source.2 +
        if reportingClass predicate query then 1 else 0 := by
  cases query with
  | inl request =>
    simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    change (answer, next) ∈ support ((PqxdhDynamicIdentityRouting.sourceWithHistory count
      (PqxdhDynamicIdentityPool.lazyImpl primitives) request).run state.source) at step
    rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run] at step
    obtain ⟨reply, actual, finished⟩ := (mem_support_bind_iff _ _ _).mp step
    obtain exactReply := OracleComp.eq_of_mem_support_pure _ finished
    cases exactReply
    exact PqxdhDynamicIdentityPool.lazyImpl_trace_count primitives predicate request state.source.2 reply actual
  | inr candidate =>
    simp only [reportingImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [reportingClass]

/-- Every actual source query class has its declared retained-trace cap through arbitrary report and compromise scheduling. -/
theorem reportingExecution_trace_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp ReportingSpec Result)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (reportingClass predicate) bound) (state : ReportingState count)
    (result : Result × ReportingState count)
    (supported : result ∈ support ((simulateQ (reportingImpl primitives count) client).run state)) :
    PqxdhDynamicIdentityPool.traceCount predicate result.2.source.2 ≤
      PqxdhDynamicIdentityPool.traceCount predicate state.source.2 + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, restSupport⟩ := supported
    have stepCount := reportingImpl_trace_count primitives count predicate query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : reportingClass predicate query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- No later compromise, creation, service request or report can erase an already recorded event. -/
theorem reportingImpl_occurred (primitives : Primitives) (count : ℕ) :
    QueryImpl.PreservesInv (reportingImpl primitives count) (fun state => state.occurred = true) := by
  intro query state occurred result supported
  cases query with
  | inl request =>
    simp only [reportingImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact occurred
  | inr candidate =>
    simp only [reportingImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp [occurred]

/-- The complete source continuation retains the sticky event even after any number of subsequent private-seed reveals. -/
theorem reportingRun_occurred (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp ReportingSpec Result)
    (state : ReportingState count) (occurred : state.occurred = true) :
    ∀ result ∈ support ((simulateQ (reportingImpl primitives count) client).run state),
      result.2.occurred = true :=
  OracleComp.simulateQ_run_preserves_inv_of_query (reportingImpl primitives count)
    (fun state => state.occurred = true) (reportingImpl_occurred primitives count) client state occurred

/-- A uniform bound on each constructed endpoint yields one generated-identity factor, independent of the number of adaptive reports. -/
theorem reporting_advantage_le_identity_count (primitives : Primitives) (count : ℕ)
    {Result : Type} (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (client : OracleComp ReportingSpec Result)
    (creates : client.IsQueryBoundP (reportingClass PqxdhDynamicIdentityPool.IsCreate) (count + 1))
    (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives
      (globalReduction primitives target ordinaryFallback
        (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
          (reportExtractor primitives (count + 1) fallback client))) ≤ epsilon) :
    Pr{let result ← reportingRun primitives (count + 1) client}[result.2.occurred = true] ≤
      (count + 1 : ℕ) * epsilon := by
  exact (reporting_advantage_le_identity_sum primitives count fallback ordinaryFallback client creates).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

end BeaconcryptCore.Computational.PqxdhDynamicIdentityReports

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.source_snapshot_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.source_snapshot_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportAccepted_iff_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportAccepted_iff_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.occurred_probability_le_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.occurred_probability_le_stopped

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingRun_occurred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingRun_occurred

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingReductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingReductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingExecution_report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingExecution_report_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingExecution_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportingExecution_trace_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reporting_advantage_le_identity_count
