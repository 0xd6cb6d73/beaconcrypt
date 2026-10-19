import BeaconcryptCore.Computational.PqxdhJointIdentityFreshness

/-!
# Fresh authentication events with later identity compromise

An adversary may report any candidate signature at any time and continue with arbitrary service requests and seed reveals. Freshness is tested when a reported event occurs. Public verification and the already observed signing/reveal history make the first fresh valid signature recognizable without knowing an identity seed. A stopping client therefore retains the generated-identity loss without a report-position guessing loss. This is a signature-report wrapper, not a root/record freshness theorem or a production acceptance-event instantiation.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointIdentityEvents

open PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness

/-- The source's public history transition is determined by the actual query and returned value, including optional DH rejection and actual seed reveal. -/
def publicUpdate {count : ℕ} (query : (GlobalSpec count).Domain)
    (answer : (GlobalSpec count).Range query) (state : GlobalState count) : GlobalState count :=
  match query with
  | .inl (.inl _) => state
  | .inl (.inr (identity, request)) =>
    { state with histories := (Function.update state.histories identity
        (state.histories identity ++ [requestEvent request answer])) }
  | .inr identity => { state with reveals := state.reveals ++ [identity] }

/-- Every actual source reply yields exactly the publicly reconstructible full history state. -/
theorem sourceImpl_publicUpdate (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : (GlobalSpec count).Domain) (state : GlobalState count)
    (result : (GlobalSpec count).Range query × GlobalState count)
    (supported : result ∈ support ((sourceImpl primitives seeds query).run state)) :
    result.2 = publicUpdate query result.1 state := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      simp only [sourceImpl, familyImpl, StateT.run, bind_assoc, mem_support_bind_iff,
        mem_support_pure_iff] at supported
      obtain ⟨answer, _, histories, hHistories, final⟩ := supported
      subst histories
      subst result
      rfl
    | inr request =>
      rcases request with ⟨identity, service⟩
      simp only [sourceImpl, familyImpl, StateT.run, pure_bind, mem_support_pure_iff] at supported
      subst result
      rfl
  | inr identity =>
    simp only [sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    rfl

/-- A report's fresh-valid status is determined entirely by public keys and the accumulated public request/reply history. -/
def ReportEvent (primitives : Primitives) {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    (candidate : FamilyForgery count) (state : GlobalState count) : Prop :=
  Fresh candidate.identity state ∧
    wins primitives (publicKeys candidate.identity) candidate.forgery (state.histories candidate.identity) = true

instance (primitives : Primitives) {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    (candidate : FamilyForgery count) (state : GlobalState count) :
    Decidable (ReportEvent primitives publicKeys candidate state) := by
  unfold ReportEvent Fresh
  infer_instance

abbrev ReportSpec (count : ℕ) : OracleSpec (FamilyForgery count) := fun _ => Unit
abbrev ReportingSpec (count : ℕ) := GlobalSpec count + ReportSpec count

/-- The sticky event records freshness at its occurrence, so later compromise cannot erase that earlier event. -/
structure ReportingState (count : ℕ) where
  publicState : GlobalState count
  occurred : Bool
  reported : List (FamilyForgery count)

def reportingImpl (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    QueryImpl (ReportingSpec count) (StateT (ReportingState count) ProbComp) := fun query state =>
  match query with
  | .inl request => do
    let (answer, publicState) ← (sourceImpl primitives seeds request).run state.publicState
    pure (answer, { state with publicState })
  | .inr candidate =>
    pure ((), ⟨state.publicState, state.occurred ||
      decide (ReportEvent primitives (familyPublic primitives seeds) candidate state.publicState),
      state.reported ++ [candidate]⟩)

/-- Stop on the first publicly recognizable fresh valid reported signature, before any later compromise. All earlier source services and reveals are forwarded unchanged. -/
def stopAtFreshReport (primitives : Primitives) {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    {Result : Type} (client : OracleComp (ReportingSpec count) Result)
    (state : GlobalState count) : OracleComp (GlobalSpec count) (Option (FamilyForgery count)) :=
  OracleComp.recOn client
    (fun _ _ => pure none)
    (fun query _ recurse state => match query with
      | .inl request => do
        let answer ← (GlobalSpec count).query request
        recurse answer (publicUpdate request answer state)
      | .inr candidate =>
        if ReportEvent primitives publicKeys candidate state then pure (some candidate)
        else recurse () state) state

@[simp] theorem stopAtFreshReport_pure (primitives : Primitives) {count : ℕ}
    (publicKeys : Fin count → PublicIdentity) {Result : Type} (value : Result) (state : GlobalState count) :
    stopAtFreshReport primitives publicKeys (pure value) state = pure none := rfl

@[simp] theorem stopAtFreshReport_service (primitives : Primitives) {count : ℕ}
    (publicKeys : Fin count → PublicIdentity) {Result : Type} (request : (GlobalSpec count).Domain)
    (next : (GlobalSpec count).Range request → OracleComp (ReportingSpec count) Result) (state : GlobalState count) :
    stopAtFreshReport primitives publicKeys ((ReportingSpec count).query (.inl request) >>= next) state = (do
      let answer ← (GlobalSpec count).query request
      stopAtFreshReport primitives publicKeys (next answer) (publicUpdate request answer state)) := rfl

@[simp] theorem stopAtFreshReport_report (primitives : Primitives) {count : ℕ}
    (publicKeys : Fin count → PublicIdentity) {Result : Type} (candidate : FamilyForgery count)
    (next : Unit → OracleComp (ReportingSpec count) Result) (state : GlobalState count) :
    stopAtFreshReport primitives publicKeys ((ReportingSpec count).query (.inr candidate) >>= next) state =
      if ReportEvent primitives publicKeys candidate state then pure (some candidate)
      else stopAtFreshReport primitives publicKeys (next ()) state := rfl

/-- A stopped report contains the unchanged candidate and its exact fresh source state. -/
def StoppedReportEvent (primitives : Primitives) {count : ℕ} (publicKeys : Fin count → PublicIdentity)
    (result : Option (FamilyForgery count) × GlobalState count) : Prop :=
  match result.1 with
  | none => False
  | some candidate => ReportEvent primitives publicKeys candidate result.2

/-- Every fresh valid event in the complete execution is captured before subsequent compromise by the publicly recognizable stopping client. -/
theorem occurred_probability_le_stopped (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) {Result : Type}
    (client : OracleComp (ReportingSpec count) Result) (state : GlobalState count)
    (reported : List (FamilyForgery count)) :
    Pr[fun result => result.2.occurred = true |
      (simulateQ (reportingImpl primitives seeds) client).run ⟨state, false, reported⟩] ≤
    Pr[StoppedReportEvent primitives (familyPublic primitives seeds) |
      (simulateQ (sourceImpl primitives seeds)
        (stopAtFreshReport primitives (familyPublic primitives seeds) client state)).run state] := by
  classical
  induction client using OracleComp.inductionOn generalizing state reported with
  | pure value => simp [StoppedReportEvent]
  | query_bind query rest ih =>
    cases query with
    | inl request =>
      rw [stopAtFreshReport_service]
      simp only [simulateQ_query_bind, StateT.run_bind]
      change Pr[fun result => result.2.occurred = true |
        (((sourceImpl primitives seeds request).run state >>= fun result =>
          pure (result.1, ReportingState.mk result.2 false reported)) >>= fun result =>
            (simulateQ (reportingImpl primitives seeds) (rest result.1)).run result.2 : ProbComp _)] ≤
        Pr[StoppedReportEvent primitives (familyPublic primitives seeds) |
          ((sourceImpl primitives seeds request).run state >>= fun result =>
            (simulateQ (sourceImpl primitives seeds)
              (stopAtFreshReport primitives (familyPublic primitives seeds) (rest result.1)
                (publicUpdate request result.1 state))).run result.2 : ProbComp _)]
      simp only [bind_assoc, pure_bind, probEvent_bind_eq_tsum_subtype]
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      have exactState := sourceImpl_publicUpdate primitives seeds request state result.val result.property
      rw [← exactState]
      exact ih result.val.1 result.val.2 reported
    | inr candidate =>
      rw [stopAtFreshReport_report]
      by_cases accepted : ReportEvent primitives (familyPublic primitives seeds) candidate state
      · simp only [accepted, ite_eq_left, simulateQ_pure, StateT.run_pure, probEvent_pure,
          StoppedReportEvent]
        exact probEvent_le_one
      · simp only [accepted, ite_false, simulateQ_query_bind, StateT.run_bind]
        change Pr[fun result => result.2.occurred = true |
          (pure ((), ReportingState.mk state (false || decide
            (ReportEvent primitives (familyPublic primitives seeds) candidate state)) (reported ++ [candidate])) >>= fun result =>
              (simulateQ (reportingImpl primitives seeds) (rest result.1)).run result.2 : ProbComp _)] ≤ _
        simpa only [accepted, decide_false, Bool.or_self, pure_bind] using ih () state (reported ++ [candidate])

/-- The executable source client returns the first recognized candidate unchanged; a fixed fallback on no report can only enlarge the final-event bound. -/
def reportExtractor (primitives : Primitives) {count : ℕ} (fallback : FamilyForgery count)
    {Result : Type}
    (adversary : (Fin count → PublicIdentity) → OracleComp (ReportingSpec count) Result)
    (publicKeys : Fin count → PublicIdentity) : OracleComp (GlobalSpec count) (FamilyForgery count) :=
  (fun result => result.getD fallback) <$>
    stopAtFreshReport primitives publicKeys (adversary publicKeys) (initialState count)

/-- All later service calls and compromises are allowed in the source; the monitor retains every reported candidate and whether a fresh event ever occurred. -/
def reportingRun (primitives : Primitives) (count : ℕ) {Result : Type}
    (adversary : (Fin count → PublicIdentity) → OracleComp (ReportingSpec count) Result) :
    ProbComp (Result × ReportingState count) := do
  let seeds ← sampleFamily count
  (simulateQ (reportingImpl primitives seeds) (adversary (familyPublic primitives seeds))).run
    ⟨initialState count, false, []⟩

/-- The full source event probability is bounded by the final-freshness experiment on the concrete stopping extractor. -/
theorem reportingRun_le_extractor (primitives : Primitives) (count : ℕ)
    (fallback : FamilyForgery count) {Result : Type}
    (adversary : (Fin count → PublicIdentity) → OracleComp (ReportingSpec count) Result) :
    Pr[fun result => result.2.occurred = true | reportingRun primitives count adversary] ≤
      Pr[GlobalEvent primitives | globalRun primitives count (reportExtractor primitives fallback adversary)] := by
  unfold reportingRun globalRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro seeds
  apply mul_le_mul' le_rfl
  apply (occurred_probability_le_stopped primitives seeds _ (initialState count) []).trans
  simp only [reportExtractor, simulateQ_map, StateT.run_map, bind_pure_comp,
    probEvent_map, Function.comp_def]
  apply probEvent_mono
  intro result _ accepted
  dsimp only [StoppedReportEvent] at accepted
  cases candidate : result.1 with
  | none => simp [candidate] at accepted
  | some forgery =>
    rw [candidate] at accepted
    simpa only [candidate, Option.getD_some, GlobalEvent, TargetEvent, ReportEvent] using accepted

/-- Fresh reported authentication events reduce with one generated-identity sum and no report-position selection loss. -/
theorem reporting_advantage_le_identity_sum (primitives : Primitives) (count : ℕ)
    (fallback : FamilyForgery (count + 1)) (ordinaryFallback : Forgery) {Result : Type}
    (adversary : (Fin (count + 1) → PublicIdentity) → OracleComp (ReportingSpec (count + 1)) Result) :
    Pr[fun result => result.2.occurred = true | reportingRun primitives (count + 1) adversary] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback (reportExtractor primitives fallback adversary)) := by
  exact (reportingRun_le_extractor primitives (count + 1) fallback adversary).trans
    (global_advantage_le_sum primitives count ordinaryFallback (reportExtractor primitives fallback adversary))

/-- No later identity compromise or service call can erase an already recorded fresh authentication event. -/
theorem reportingImpl_occurred (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    QueryImpl.PreservesInv (reportingImpl primitives seeds) (fun state => state.occurred = true) := by
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

/-- Every complete continuation, including arbitrary post-event seed reveals, preserves the recorded event. -/
theorem reportingRun_occurred (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    {Result : Type} (client : OracleComp (ReportingSpec count) Result)
    (state : ReportingState count) (occurred : state.occurred = true) :
    ∀ result ∈ support ((simulateQ (reportingImpl primitives seeds) client).run state),
      result.2.occurred = true :=
  OracleComp.simulateQ_run_preserves_inv_of_query (reportingImpl primitives seeds)
    (fun state => state.occurred = true) (reportingImpl_occurred primitives seeds) client state occurred

/-- Lift an actual source query class through reporting; reports themselves are local verification work. -/
def sourceClass {count : ℕ} (predicate : (GlobalSpec count).Domain → Prop) :
    (ReportingSpec count).Domain → Prop
  | .inl request => predicate request
  | .inr _ => False

instance {count : ℕ} (predicate : (GlobalSpec count).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (sourceClass predicate) := fun query => by
  cases query with
  | inl request => exact inferInstanceAs (Decidable (predicate request))
  | inr _ => exact inferInstanceAs (Decidable False)

/-- Stopping retains each complete source service/reveal budget; checking reports creates no additional primitive-oracle call. -/
theorem stopAtFreshReport_query_bound (primitives : Primitives) {count : ℕ}
    (publicKeys : Fin count → PublicIdentity) {Result : Type}
    (client : OracleComp (ReportingSpec count) Result) (predicate : (GlobalSpec count).Domain → Prop)
    [DecidablePred predicate] (bound : ℕ) (bounded : client.IsQueryBoundP (sourceClass predicate) bound)
    (state : GlobalState count) :
    (stopAtFreshReport primitives publicKeys client state).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure value => simp
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl request =>
      rw [stopAtFreshReport_service, OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer) _⟩
    | inr candidate =>
      rw [stopAtFreshReport_report]
      split
      · simp
      · exact ih () bound (by simpa [sourceClass] using bounded.2 ()) state

/-- The unchanged-candidate extractor has exactly the inherited source class cap. -/
theorem reportExtractor_query_bound (primitives : Primitives) {count : ℕ}
    (fallback : FamilyForgery count) {Result : Type}
    (adversary : (Fin count → PublicIdentity) → OracleComp (ReportingSpec count) Result)
    (predicate : (GlobalSpec count).Domain → Prop) [DecidablePred predicate] (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (sourceClass predicate) bound)
    (publicKeys : Fin count → PublicIdentity) :
    (reportExtractor primitives fallback adversary publicKeys).IsQueryBoundP predicate bound := by
  simpa only [reportExtractor, OracleComp.isQueryBoundP_map_iff] using
    stopAtFreshReport_query_bound primitives publicKeys (adversary publicKeys) predicate bound (bounded _) (initialState count)

/-- Every constructed ordinary joint-use reduction inherits the service caps with all local seed draws charged. -/
theorem reportingReduction_query_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (fallback : FamilyForgery (count + 1)) (ordinaryFallback : Forgery) {Result : Type}
    (adversary : (Fin (count + 1) → PublicIdentity) → OracleComp (ReportingSpec (count + 1)) Result)
    (kind : Kind) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP
      (sourceClass (globalClass (IsClass kind))) bound) (publicKeys : PublicIdentity) :
    (globalReduction primitives target ordinaryFallback (reportExtractor primitives fallback adversary) publicKeys).IsQueryBoundP (IsClass kind) ((if kind = .uniform then 32 * count else 0) + bound) := by
  exact globalReduction_query_bound primitives target ordinaryFallback _ kind bound
    (reportExtractor_query_bound primitives fallback adversary _ bound bounded) publicKeys

/-- Complete interpreted reductions pay all identity-generation draws, including the target challenger, plus the source uniform budget. -/
theorem reportingReductionGame_uniform_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (fallback : FamilyForgery (count + 1)) (ordinaryFallback : Forgery) {Result : Type}
    (adversary : (Fin (count + 1) → PublicIdentity) → OracleComp (ReportingSpec (count + 1)) Result)
    (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP
      (sourceClass (globalClass (IsClass .uniform))) bound) :
    (game primitives (globalReduction primitives target ordinaryFallback
      (reportExtractor primitives fallback adversary))).IsTotalQueryBound (32 * (count + 1) + bound) := by
  exact globalReductionGame_uniform_bound primitives target ordinaryFallback _ bound
    (reportExtractor_query_bound primitives fallback adversary _ bound bounded)

/-- Every report attempt is counted, including invalid signatures, repeats, compromised targets and later accepted candidates. -/
def IsReport {count : ℕ} : (ReportingSpec count).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {count : ℕ} : DecidablePred (IsReport (count := count)) := fun query => by
  cases query <;> simp only [IsReport] <;> infer_instance

/-- The monitor appends exactly one unchanged candidate per report and none for an ordinary source request. -/
theorem reportingImpl_report_count (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : (ReportingSpec count).Domain) (state : ReportingState count)
    (result : (ReportingSpec count).Range query × ReportingState count)
    (supported : result ∈ support ((reportingImpl primitives seeds query).run state)) :
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

/-- The complete source history charges every adaptive authentication report against the explicit report cap. -/
theorem reportingExecution_report_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    {Result : Type} (client : OracleComp (ReportingSpec count) Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP IsReport bound) (state : ReportingState count)
    (result : Result × ReportingState count)
    (supported : result ∈ support ((simulateQ (reportingImpl primitives seeds) client).run state)) :
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
    have stepCount := reportingImpl_report_count primitives seeds query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : IsReport query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- Source event recognition uses public deterministic verification, with no extra random or primitive-oracle request. -/
theorem reportingImpl_uniform_bound (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (query : (ReportingSpec count).Domain) (state : ReportingState count) :
    ((reportingImpl primitives seeds query).run state).IsQueryBoundP (fun _ => True)
      (if sourceClass (globalClass (IsClass .uniform)) query then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [reportingImpl, StateT.run, sourceClass, bind_pure_comp]
    simp only [OracleComp.isQueryBoundP_map_iff]
    exact sourceImpl_uniform_bound primitives seeds request state.publicState
  | inr candidate =>
    change (pure _ : ProbComp _).IsQueryBoundP (fun _ => True) 0
    trivial

/-- The complete source experiment retains all identity generation and ambient uniform-oracle work. -/
theorem reportingRun_uniform_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (adversary : (Fin count → PublicIdentity) → OracleComp (ReportingSpec count) Result) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP
      (sourceClass (globalClass (IsClass .uniform))) bound) :
    (reportingRun primitives count adversary).IsTotalQueryBound (32 * count + bound) := by
  unfold reportingRun
  apply OracleComp.isTotalQueryBound_bind (sampleFamily_uniform_bound count)
  intro seeds
  exact (OracleComp.isQueryBoundP_true_iff _ _).mp
    ((bounded _).simulateQ_run_StateT_of_step (reportingImpl_uniform_bound primitives seeds)
      ⟨initialState count, false, []⟩)

/-- A common bound on the constructed reductions yields the generated-identity factor without multiplying by reports. -/
theorem reporting_advantage_le_identity_count (primitives : Primitives) (count : ℕ)
    (fallback : FamilyForgery (count + 1)) (ordinaryFallback : Forgery) {Result : Type}
    (adversary : (Fin (count + 1) → PublicIdentity) → OracleComp (ReportingSpec (count + 1)) Result)
    (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives
      (globalReduction primitives target ordinaryFallback (reportExtractor primitives fallback adversary)) ≤ epsilon) :
    Pr[fun result => result.2.occurred = true | reportingRun primitives (count + 1) adversary] ≤
      (count + 1 : ℕ) * epsilon := by
  exact (reporting_advantage_le_identity_sum primitives count fallback ordinaryFallback adversary).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

end BeaconcryptCore.Computational.PqxdhJointIdentityEvents

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.sourceImpl_publicUpdate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.sourceImpl_publicUpdate

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.occurred_probability_le_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.occurred_probability_le_stopped

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reporting_advantage_le_identity_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reporting_advantage_le_identity_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingRun_occurred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingRun_occurred

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingReductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingReductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingExecution_report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingExecution_report_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityEvents.reportingRun_uniform_bound
