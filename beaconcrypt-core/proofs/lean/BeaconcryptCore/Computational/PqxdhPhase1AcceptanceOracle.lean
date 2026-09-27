import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-!
# Optional Phase-1 acceptance in the joint identity experiment

Every candidate returns the complete actual attached-verifier/parser result to the original adaptive continuation. A public origin monitor is ghost instrumentation: erasing it preserves the entire generated private state and all signing, DH and reveal histories, without any verifier-compatibility premise. Ordinary functional attached-signature compatibility is used only to connect the monitored origin event to the existing N joint weak-EUF reductions.

The generated index on a candidate does not affect source acceptance. It labels only the report-time origin event; production byte ownership still needs an explicit map. This is the typed optional verification/parser boundary after four-field decoding, not native Cap'n Proto extraction, a new security endpoint, or global root/record composition. Duplicate local public verification and history work remain computation; only declared source and reduction query classes are bounded here.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports

abbrev AcceptedInput := Ed25519PublicKey × Phase1KeyTuple
abbrev AcceptanceSpec : OracleSpec CandidateReport := fun _ => Option AcceptedInput
abbrev SourceSpec := DynamicSpec + AcceptanceSpec
abbrev CompleteState (count : ℕ) := Monitor count × ReportingState count

/-- Public instrumentation forwards one unchanged source slot, then returns the actual typed parsing result to the original continuation. -/
def instrument (primitives : Primitives) : QueryImpl SourceSpec (OracleComp ProtocolSpec) :=
  fun query => match query with
  | .inl request => ProtocolSpec.query (.inl request)
  | .inr candidate => do
    let _ ← ProtocolSpec.query (.inr candidate)
    pure (acceptPhase1Candidate primitives.verify candidate.candidate)

def instrumentedClient (primitives : Primitives) {Result : Type}
    (client : OracleComp SourceSpec Result) : OracleComp ProtocolSpec Result :=
  simulateQ (instrument primitives) client

/-- The source-facing interpreter computes the attached-verifier result, retains the report instrumentation, and returns the complete optional decoded input. A rejection never becomes a fabricated accepted key tuple. -/
def acceptanceImpl (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) :
    QueryImpl SourceSpec (StateT (CompleteState count) ProbComp) := fun query =>
  match query with
  | .inl request => sourceImpl primitives count (.inl request)
  | .inr candidate => do
    let accepted := sourceAccept attachedVerify candidate.candidate
    let _ ← sourceImpl primitives count (.inr candidate)
    pure accepted

/-- Functional attached-signature compatibility identifies the complete per-query result and private poststate, not merely its acceptance bit. -/
theorem acceptanceImpl_eq (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) :
    acceptanceImpl attachedVerify primitives count =
      QueryImpl.compose (sourceImpl primitives count) (instrument primitives) := by
  funext query
  cases query with
  | inl request => simp [acceptanceImpl, instrument, QueryImpl.compose]
  | inr candidate =>
    simp only [acceptanceImpl, QueryImpl.compose, instrument, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, sourceAccept_eq attachedVerify primitives adapter]

def initialState (count : ℕ) : CompleteState count :=
  (initialMonitor count, ⟨initialSource count, initialSnapshot count, false, []⟩)

def actualRun (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp SourceSpec Result) : ProbComp (Result × CompleteState count) :=
  (simulateQ (acceptanceImpl attachedVerify primitives count) client).run (initialState count)

/-- Every adaptive continuation receives the same complete optional source input; all identity/private/monitor state remains jointly retained. -/
theorem actualRun_eq (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result) :
    actualRun attachedVerify primitives count client =
      PqxdhJointPhase1Reports.run primitives count (instrumentedClient primitives client) := by
  simp only [actualRun, acceptanceImpl_eq attachedVerify primitives adapter,
    QueryImpl.simulateQ_compose, PqxdhJointPhase1Reports.run, instrumentedClient, initialState]

/-- Instrumentation forwards exactly one original slot and changes only the candidate reply type. -/
def sourceQuery : SourceSpec.Domain → ProtocolSpec.Domain
  | .inl request => .inl request
  | .inr candidate => .inr candidate

def IsSourceClass (predicate : ProtocolSpec.Domain → Prop) : SourceSpec.Domain → Prop :=
  fun query => predicate (sourceQuery query)

instance (predicate : ProtocolSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (IsSourceClass predicate) := fun query => inferInstanceAs (Decidable (predicate (sourceQuery query)))

/-- Each exact source slot retains its query class even when validation rejects or no forgery is forwarded. -/
theorem instrument_query_bound (primitives : Primitives) (predicate : ProtocolSpec.Domain → Prop)
    [DecidablePred predicate] (query : SourceSpec.Domain) :
    (instrument primitives query).IsQueryBoundP predicate
      (if IsSourceClass predicate query then 1 else 0) := by
  cases query with
  | inl request =>
    change OracleComp.IsQueryBoundP
      (ProtocolSpec.query (.inl request) : OracleComp ProtocolSpec _) predicate
      (if predicate (.inl request) then 1 else 0)
    rw [OracleComp.isQueryBoundP_query_iff]
    split <;> simp_all
  | inr candidate =>
    simp only [instrument, bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff]
    by_cases selected : IsSourceClass predicate (.inr candidate)
    · rw [ite_eq_left selected]
      exact fun _ => Nat.zero_lt_one
    · intro accepted
      exact (selected (show IsSourceClass predicate (.inr candidate) from accepted)).elim

/-- Every original class is retained through every possible optional acceptance response and subsequent continuation. -/
theorem instrumentedClient_query_bound (primitives : Primitives) {Result : Type}
    (client : OracleComp SourceSpec Result) (predicate : ProtocolSpec.Domain → Prop)
    [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsSourceClass predicate) bound) :
    (instrumentedClient primitives client).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp [instrumentedClient]
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    change (simulateQ (instrument primitives) (SourceSpec.query query >>= next)).IsQueryBoundP predicate bound
    rw [simulateQ_query_bind]
    change (instrument primitives query >>= fun answer => simulateQ (instrument primitives) (next answer)).IsQueryBoundP predicate bound
    have rest : ∀ answer, (simulateQ (instrument primitives) (next answer)).IsQueryBoundP predicate
        (if IsSourceClass predicate query then bound - 1 else bound) :=
      fun answer => ih answer _ (bounded.2 answer)
    have total : (if IsSourceClass predicate query then 1 else 0) +
        (if IsSourceClass predicate query then bound - 1 else bound) = bound := by
      by_cases selected : IsSourceClass predicate query
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, if_true]
        omega
      · simp [selected]
    simpa only [total] using OracleComp.isQueryBoundP_bind
      (instrument_query_bound primitives predicate query) (fun answer _ => rest answer)

/-- The source receives actual acceptance results while the same report-time event reduces to the existing N joint weak-EUF games. No field or acceptance-attempt selector is introduced. -/
theorem acceptance_advantage_le_sum
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : client.IsQueryBoundP (IsSourceClass (SourceClass IsCreate)) (count + 1)) :
    Pr[(fun result => result.2.1.occurred = true) | actualRun attachedVerify primitives (count + 1) client] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback
              (routedClient primitives (count + 1) (instrumentedClient primitives client))))) := by
  rw [actualRun_eq attachedVerify primitives adapter]
  exact fieldOrigin_advantage_le_sum primitives count _ fallback ordinaryFallback
    (instrumentedClient_query_bound primitives client _ (count + 1) creates)

abbrev BareState (count : ℕ) :=
  PqxdhJointIdentityFreshness.GlobalState count × PqxdhDynamicIdentityPool.SourceState

/-- The uninstrumented typed source retains every joint identity operation and returns the actual optional Phase-1 input without adding any report oracle. -/
def bareImpl (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) :
    QueryImpl SourceSpec (StateT (BareState count) ProbComp) := fun query state =>
  match query with
  | .inl request => (sourceWithHistory count (lazyImpl primitives) request).run state
  | .inr candidate => pure (sourceAccept attachedVerify candidate.candidate, state)

/-- Erasing instrumentation keeps the complete generated seed prefix, all dynamic observations, signing/DH/reveal histories and the actual returned answer. -/
def erase {count : ℕ} {Result : Type} (result : Result × CompleteState count) : Result × BareState count :=
  (result.1, result.2.2.source)

/-- Candidate instrumentation preserves the whole underlying dynamic identity state, including all previous optional replies and actual seed reveals. -/
theorem sourceCandidate_erase (primitives : Primitives) (count : ℕ) (candidate : CandidateReport)
    (state : CompleteState count) :
    erase <$> ((sourceImpl primitives count (.inr candidate)).run state) = pure ((), state.2.source) := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [Functor.map_map]
  change (fun result => (result.1.1, result.2.source)) <$>
    ((simulateQ (reportingImpl primitives count)
      ((wrapper primitives count (.inr candidate)).run state.1)).run state.2) = _
  cases translated : translateReport primitives candidate state.1.snapshot with
  | none =>
    simp only [wrapper, StateT.run, translated, pure_bind, simulateQ_pure]
    rfl
  | some forgery =>
    simp only [wrapper, StateT.run, translated, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Identity creation, signing, converted-DH and reveal requests keep the exact original reply and complete underlying source state after monitor erasure. -/
theorem sourceIdentity_erase (primitives : Primitives) (count : ℕ) (request : DynamicSpec.Domain)
    (state : CompleteState count) :
    erase <$> ((sourceImpl primitives count (.inl request)).run state) =
      ((sourceWithHistory count (lazyImpl primitives) request).run state.2.source) := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [Functor.map_map]
  change (fun result => (result.1.1, result.2.source)) <$>
    ((simulateQ (reportingImpl primitives count)
      ((wrapper primitives count (.inl request)).run state.1)).run state.2) = _
  simp only [wrapper, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (fun result : (DynamicSpec.Range request × Monitor count) × ReportingState count =>
      (result.1.1, result.2.source)) <$>
    ((do
      let answer ← reportingImpl primitives count (.inl request)
      pure (answer, { state.1 with
        requests := state.1.requests + 1
        snapshot := observe request answer state.1.snapshot })).run state.2) = _
  rw [StateT.run_bind]
  simp only [StateT.run_pure, map_bind, map_pure]
  simp [reportingImpl, StateT.run]

set_option backward.isDefEq.respectTransparency false in
/-- Every source query has the exact uninstrumented reply and complete dynamic poststate after erasing the public report monitor. No attached-verifier compatibility premise is needed for this erasure. -/
theorem acceptanceImpl_erase
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) (query : SourceSpec.Domain) (state : CompleteState count) :
    erase <$> ((acceptanceImpl attachedVerify primitives count query).run state) =
      ((bareImpl attachedVerify primitives count query).run state.2.source) := by
  cases query with
  | inl request => exact sourceIdentity_erase primitives count request state
  | inr candidate =>
    change _ = (pure (sourceAccept attachedVerify candidate.candidate, state.2.source) :
      ProbComp (Option AcceptedInput × BareState count))
    have projected := congrArg
      (fun computation => (fun result : Unit × BareState count =>
        (sourceAccept attachedVerify candidate.candidate, result.2)) <$> computation)
      (sourceCandidate_erase primitives count candidate state)
    simpa only [acceptanceImpl, StateT.run_bind, StateT.run_pure, StateT.run_map,
      bind_pure_comp, Functor.map_map, erase, map_pure, Function.comp_def] using projected

/-- The complete adaptive source execution without report instrumentation. The original client still receives every actual optional acceptance reply. -/
def bareRun (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp SourceSpec Result) : ProbComp (Result × BareState count) :=
  (simulateQ (bareImpl attachedVerify primitives count) client).run (initialState count).2.source

/-- Whole-run erasure preserves the actual optional inputs seen by every adaptive continuation jointly with all generated secrets and source histories. The monitor is analysis instrumentation only. -/
theorem actualRun_erase
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result) :
    erase <$> actualRun attachedVerify primitives count client =
      bareRun attachedVerify primitives count client :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (acceptanceImpl attachedVerify primitives count) (bareImpl attachedVerify primitives count)
    (fun state => state.2.source)
    (acceptanceImpl_erase attachedVerify primitives count) client (initialState count)

/-- Each constructed joint reduction inherits all original signing, optional-DH and explicit-coin caps, charging every other reserved seed. -/
theorem reduction_query_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp SourceSpec Result) (kind : Kind) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsSourceClass (SourceClass (dynamicClass (IsClass kind)))) bound)
    (jointPublic : PublicIdentity) :
    (globalReduction primitives target ordinaryFallback
      (routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback
          (routedClient primitives (count + 1) (instrumentedClient primitives client)))) jointPublic).IsQueryBoundP
      (IsClass kind) ((if kind = .uniform then 32 * count else 0) + bound) :=
  fieldReduction_query_bound primitives count target fallback ordinaryFallback _ kind bound
    (instrumentedClient_query_bound primitives client _ bound bounded) jointPublic

/-- The full ordinary joint challenger additionally pays for its secret target seed: all N reserved seeds cost 32N byte queries. -/
theorem reductionGame_uniform_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp SourceSpec Result) (qUniform : ℕ)
    (bounded : client.IsQueryBoundP (IsSourceClass (SourceClass (dynamicClass (IsClass .uniform)))) qUniform) :
    (game primitives (globalReduction primitives target ordinaryFallback
      (routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback
          (routedClient primitives (count + 1) (instrumentedClient primitives client)))))).IsTotalQueryBound
      (32 * (count + 1) + qUniform) :=
  fieldReductionGame_uniform_bound primitives count target fallback ordinaryFallback _ qUniform
    (instrumentedClient_query_bound primitives client _ qUniform bounded)

/-- The actual source, distinct from a reserved reduction family, pays for its on-demand creation budget and every explicit coin request. -/
theorem actualRun_uniform_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (IsSourceClass (SourceClass IsCreate)) qCreate)
    (coins : client.IsQueryBoundP (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsUniform)) qUniform) :
    (actualRun attachedVerify primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [actualRun_eq attachedVerify primitives adapter]
  exact run_uniform_bound primitives count _ qCreate qUniform
    (instrumentedClient_query_bound primitives client _ qCreate creates)
    (instrumentedClient_query_bound primitives client _ qUniform coins)

/-- Erasing the complete analysis monitor preserves the actual source sampling cap. Local signature/parsing/history work is still present. -/
theorem bareRun_uniform_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (IsSourceClass (SourceClass IsCreate)) qCreate)
    (coins : client.IsQueryBoundP (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsUniform)) qUniform) :
    (bareRun attachedVerify primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [← actualRun_erase attachedVerify primitives count client,
    OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
  exact actualRun_uniform_bound attachedVerify primitives adapter count client qCreate qUniform creates coins

/-- Every actual candidate is counted, including malformed, attacker-owned, already-signed and compromised cases that contribute no fresh forgery. -/
theorem actualRun_attempt_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result) (qAttempts : ℕ)
    (bounded : client.IsQueryBoundP (IsSourceClass IsCandidateReport) qAttempts)
    (result : Result × CompleteState count)
    (supported : result ∈ support (actualRun attachedVerify primitives count client)) :
    result.2.1.attempted.length ≤ qAttempts := by
  rw [actualRun_eq attachedVerify primitives adapter] at supported
  exact run_attempt_bound primitives count _ qAttempts
    (instrumentedClient_query_bound primitives client _ qAttempts bounded) result supported

/-- Later source compromise does not delete an event recognized at the original acceptance position. -/
theorem actualRun_occurred
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result)
    (result : Result × CompleteState count)
    (supported : result ∈ support (actualRun attachedVerify primitives count client)) :
    result.2.1.occurred = true ↔ ∃ observation ∈ result.2.1.attempted, observation.accepted = true := by
  rw [actualRun_eq attachedVerify primitives adapter] at supported
  exact run_occurred primitives count _ result supported

/-- Exactly one instrumented slot corresponds to each original request, including rejected candidates and rejected identity services. -/
theorem instrumentedClient_total_bound (primitives : Primitives) {Result : Type}
    (client : OracleComp SourceSpec Result) (qQueries : ℕ) (bounded : client.IsTotalQueryBound qQueries) :
    (instrumentedClient primitives client).IsTotalQueryBound qQueries := by
  have source : client.IsQueryBoundP (IsSourceClass (fun _ => True)) qQueries := by
    change client.IsQueryBoundP (fun _ => True) qQueries
    exact (OracleComp.isQueryBoundP_true_iff client qQueries).mpr bounded
  exact (OracleComp.isQueryBoundP_true_iff _ qQueries).mp
    (instrumentedClient_query_bound primitives client (fun _ => True) qQueries source)

/-- The public monitor retains the original position of every source request, with an explicit bound on all attempts and interleaved operations. -/
theorem actualRun_request_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : ℕ) {Result : Type} (client : OracleComp SourceSpec Result)
    (qQueries : ℕ) (bounded : client.IsTotalQueryBound qQueries)
    (result : Result × CompleteState count)
    (supported : result ∈ support (actualRun attachedVerify primitives count client)) :
    result.2.1.requests ≤ qQueries := by
  rw [actualRun_eq attachedVerify primitives adapter] at supported
  exact run_request_bound primitives count _ qQueries
    (instrumentedClient_total_bound primitives client qQueries bounded) result supported

end BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptanceImpl_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptanceImpl_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrument_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrument_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrumentedClient_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrumentedClient_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptance_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptance_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.sourceCandidate_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.sourceCandidate_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.sourceIdentity_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.sourceIdentity_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptanceImpl_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.acceptanceImpl_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.reduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.reduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.reductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.reductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.bareRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.bareRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_attempt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_attempt_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_occurred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_occurred

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrumentedClient_total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.instrumentedClient_total_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_request_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.actualRun_request_bound
