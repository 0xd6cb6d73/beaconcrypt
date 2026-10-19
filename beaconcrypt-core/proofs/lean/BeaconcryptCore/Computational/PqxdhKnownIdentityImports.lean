import BeaconcryptCore.Computational.PqxdhDynamicIdentityReports

/-!
# Known seed imports alongside dynamically generated identities

The public wrapper stores generated-index references and attacker-submitted known seeds. Generated seed material remains in the existing dynamic source interpreter. Known-seed operations are evaluated locally using the same joint primitive functions; their source calls remain counted as local work. A report can win only for a generated owner, with the existing report-time freshness test. No entropy claim is made about an imported seed or arbitrary honest caller-supplied material.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKnownIdentityImports
open PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool (DynamicSpec PoolQuery)
open PqxdhDynamicIdentityRouting (DynamicForgery dynamicClass)
open PqxdhDynamicIdentityReports (ReportingSpec ReportingState reportingClass)

/-- Generated entries retain only the already observed source index and public values. Imported seeds are exactly adversary-supplied input. -/
inductive Owner where
  | generated (identity : ℕ) (publicKey : PublicIdentity)
  | imported (seed : IdentitySeed)

inductive Request where
  | create
  | importKnown (seed : IdentitySeed)
  | service (handle : ℕ) (request : JointSpec.Domain)
  | reveal (handle : ℕ)
  | report (candidate : DynamicForgery)

def RequestRange : Request → Type
  | .create => Option (ℕ × PublicIdentity)
  | .importKnown _ => ℕ × PublicIdentity
  | .service _ request => Option (JointSpec.Range request)
  | .reveal _ => Option IdentitySeed
  | .report _ => Unit

abbrev LocalSpec : OracleSpec Request := RequestRange
abbrev OwnedSpec := unifSpec + LocalSpec
abbrev Observation := (query : OwnedSpec.Domain) × OwnedSpec.Range query

/-- The wrapper is public: imported seeds arrived in actual requests, while generated entries contain no private seed. All actual replies, including invalid-index and DH rejection, remain in order. -/
structure PublicState where
  owners : List Owner
  transcript : List Observation

def initialState : PublicState := ⟨[], []⟩

def record (query : OwnedSpec.Domain) (answer : OwnedSpec.Range query) (state : PublicState) : PublicState :=
  { state with transcript := state.transcript ++ [⟨query, answer⟩] }

/-- Generated requests use the exact existing dynamic interface. Imported services use their known seed and return the same optional DH or signature bytes; imported reports cannot establish honest-owner freshness. -/
def wrapper (primitives : Primitives) : QueryImpl OwnedSpec
    (StateT PublicState (OracleComp ReportingSpec)) := fun query state =>
  match query with
  | .inl coin => do
    let answer ← ReportingSpec.query (.inl (.inl coin))
    pure (answer, record (.inl coin) answer state)
  | .inr .create => do
    let created ← ReportingSpec.query (.inl (.inr .create))
    match created with
    | none => pure (none, record (.inr .create) none state)
    | some (identity, publicKey) =>
      let answer := some (state.owners.length, publicKey)
      pure (answer, record (.inr .create) answer
        { state with owners := state.owners ++ [.generated identity publicKey] })
  | .inr (.importKnown seed) =>
    let answer := (state.owners.length, primitives.publicKeys seed)
    pure (answer, record (.inr (.importKnown seed)) answer
      { state with owners := state.owners ++ [.imported seed] })
  | .inr (.service handle request) =>
    match state.owners[handle]? with
    | none => pure (none, record (.inr (.service handle request)) none state)
    | some (.imported seed) =>
      let answer := some (primitiveReply primitives seed request)
      pure (answer, record (.inr (.service handle request)) answer state)
    | some (.generated identity _) => do
      let answer ← ReportingSpec.query (.inl (.inr (.service identity request)))
      pure (answer, record (.inr (.service handle request)) answer state)
  | .inr (.reveal handle) =>
    match state.owners[handle]? with
    | none => pure (none, record (.inr (.reveal handle)) none state)
    | some (.imported seed) => pure (some seed, record (.inr (.reveal handle)) (some seed) state)
    | some (.generated identity _) => do
      let answer ← ReportingSpec.query (.inl (.inr (.reveal identity)))
      pure (answer, record (.inr (.reveal handle)) answer state)
  | .inr (.report candidate) =>
    match state.owners[candidate.identity]? with
    | some (.generated identity _) => do
      let answer ← ReportingSpec.query (.inr ⟨identity, candidate.forgery⟩)
      pure (answer, record (.inr (.report candidate)) answer state)
    | _ => pure ((), record (.inr (.report candidate)) () state)

/-- The public routing client receives only actual replies and stores imported input seeds. It has no argument for any generated private seed. -/
def routedClient (primitives : Primitives) {Result : Type}
    (client : OracleComp OwnedSpec Result) : OracleComp ReportingSpec (Result × PublicState) :=
  (simulateQ (wrapper primitives) client).run initialState

/-- The composed source retains the entire public owner state and complete actual generated source, including every earlier private state, reveal and report. -/
def sourceImpl (primitives : Primitives) (count : ℕ) :
    QueryImpl OwnedSpec (StateT (PublicState × ReportingState count) ProbComp) :=
  QueryImpl.Stateful.link (wrapper primitives) (PqxdhDynamicIdentityReports.reportingImpl primitives count)

def run (primitives : Primitives) (count : ℕ) {Result : Type} (client : OracleComp OwnedSpec Result) :
    ProbComp (Result × (PublicState × ReportingState count)) :=
  (simulateQ (sourceImpl primitives count) client).run
    (initialState, ⟨PqxdhDynamicIdentityReports.initialSource count,
      PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩)

/-- Complete linked execution equals the existing reporting experiment with the public owner wrapper, preserving all state jointly and only reassociating products. -/
theorem run_complete (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp OwnedSpec Result) :
    run primitives count client =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        PqxdhDynamicIdentityReports.reportingRun primitives count (routedClient primitives client) := by
  simp only [run, sourceImpl, QueryImpl.Stateful.simulateQ_link_run,
    PqxdhDynamicIdentityReports.reportingRun, routedClient]
  rfl

/-- The event is the existing report-time signature event of generated owners. Imported identities are explicitly nonfresh at birth, independent of any entropy in their submitted seed. -/
def ReportEvent {Result : Type} {count : ℕ}
    (result : Result × (PublicState × ReportingState count)) : Prop := result.2.2.occurred = true

/-- Exact event transport uses the full source run and does not replace imported seeds, earlier observations or later reveals. -/
theorem run_event (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp OwnedSpec Result) :
    Pr[ReportEvent | run primitives count client] =
      Pr[(fun result => result.2.occurred = true) |
        PqxdhDynamicIdentityReports.reportingRun primitives count (routedClient primitives client)] := by
  rw [run_complete, probEvent_map]
  rfl

/-- All public source request classes, including imports and report attempts, have independent budgets. -/
inductive Cost where
  | uniform | create | importKnown | sign | staticDh | reveal | report
  deriving DecidableEq

def requestCost : OwnedSpec.Domain → Cost
  | .inl _ => .uniform
  | .inr .create => .create
  | .inr (.importKnown _) => .importKnown
  | .inr (.service _ (.sign _)) => .sign
  | .inr (.service _ (.staticDh _)) => .staticDh
  | .inr (.reveal _) => .reveal
  | .inr (.report _) => .report

def IsCost (kind : Cost) (query : OwnedSpec.Domain) : Prop := requestCost query = kind
instance (kind : Cost) : DecidablePred (IsCost kind) := fun _ => inferInstanceAs (Decidable (_ = _))

def forwardedCost : ReportingSpec.Domain → Cost
  | .inl (.inl _) => .uniform
  | .inl (.inr .create) => .create
  | .inl (.inr (.service _ (.sign _))) => .sign
  | .inl (.inr (.service _ (.staticDh _))) => .staticDh
  | .inl (.inr (.reveal _)) => .reveal
  | .inr _ => .report

def ForwardedCost (kind : Cost) (query : ReportingSpec.Domain) : Prop := forwardedCost query = kind
instance (kind : Cost) : DecidablePred (ForwardedCost kind) := fun _ => inferInstanceAs (Decidable (_ = _))

/-- Every public query forwards at most one request of exactly the same class. Known-seed work never invokes a hidden generated-seed oracle. -/
theorem wrapper_query_step (primitives : Primitives) (kind : Cost) (query : OwnedSpec.Domain)
    (state : PublicState) :
    ((wrapper primitives query).run state).IsQueryBoundP (ForwardedCost kind)
      (if IsCost kind query then 1 else 0) := by
  cases query with
  | inl coin =>
    simp only [wrapper, StateT.run, bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff, ForwardedCost, forwardedCost, IsCost, requestCost]
    by_cases same : Cost.uniform = kind <;> simp [same]
  | inr request =>
    cases request with
    | create =>
      simp only [wrapper, StateT.run, OracleComp.isQueryBoundP_query_bind_iff,
        ForwardedCost, forwardedCost, IsCost, requestCost]
      constructor
      · by_cases same : Cost.create = kind <;> simp [same]
      · intro answer
        cases answer <;> trivial
    | importKnown seed => trivial
    | service handle request =>
      simp only [wrapper, StateT.run]
      cases found : state.owners[handle]? with
      | none => trivial
      | some owner =>
        cases owner with
        | imported seed => trivial
        | generated identity publicKey =>
          simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
            OracleComp.isQueryBoundP_query_iff]
          cases request <;> simp only [ForwardedCost, forwardedCost, IsCost, requestCost] <;>
            intro same <;> simp_all
    | reveal handle =>
      simp only [wrapper, StateT.run]
      cases found : state.owners[handle]? with
      | none => trivial
      | some owner =>
        cases owner with
        | imported seed => trivial
        | generated identity publicKey =>
          simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
            OracleComp.isQueryBoundP_query_iff, ForwardedCost, forwardedCost, IsCost, requestCost]
          by_cases same : Cost.reveal = kind <;> simp [same]
    | report candidate =>
      simp only [wrapper, StateT.run]
      cases found : state.owners[candidate.identity]? with
      | none => trivial
      | some owner =>
        cases owner with
        | imported seed => trivial
        | generated identity publicKey =>
          simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
            OracleComp.isQueryBoundP_query_iff, ForwardedCost, forwardedCost, IsCost, requestCost]
          by_cases same : Cost.report = kind <;> simp [same]

/-- The complete public wrapper preserves every underlying request-class cap across arbitrary imported-key and generated-key scheduling. -/
theorem routedClient_query_bound (primitives : Primitives) {Result : Type}
    (client : OracleComp OwnedSpec Result) (kind : Cost) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsCost kind) bound) :
    (routedClient primitives client).IsQueryBoundP (ForwardedCost kind) bound :=
  bounded.simulateQ_run_StateT_of_step (wrapper_query_step primitives kind) initialState

/-- Creation forwarded by the mixed-owner interface is exactly honest dynamic source creation. -/
theorem forwarded_create : ForwardedCost .create =
    reportingClass PqxdhDynamicIdentityPool.IsCreate := by
  funext query
  cases query with
  | inl request =>
    cases request with
    | inl coin => simp [ForwardedCost, forwardedCost, reportingClass, PqxdhDynamicIdentityPool.IsCreate]
    | inr request => cases request with
      | create => simp [ForwardedCost, forwardedCost, reportingClass, PqxdhDynamicIdentityPool.IsCreate]
      | service identity request => cases request <;> simp [ForwardedCost, forwardedCost, reportingClass, PqxdhDynamicIdentityPool.IsCreate]
      | reveal identity => simp [ForwardedCost, forwardedCost, reportingClass, PqxdhDynamicIdentityPool.IsCreate]
  | inr candidate => simp [ForwardedCost, forwardedCost, reportingClass]

/-- Honest creation remains the only identity selection factor even when known-seed imports are adaptively chosen from all earlier observations. -/
theorem report_advantage_le_sum (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp OwnedSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : client.IsQueryBoundP (IsCost .create) (count + 1)) :
    Pr[ReportEvent | run primitives (count + 1) client] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
            (PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback
              (routedClient primitives client)))) := by
  rw [run_event]
  apply PqxdhDynamicIdentityReports.reporting_advantage_le_identity_sum
  simpa only [forwarded_create] using
    routedClient_query_bound primitives client .create (count + 1) creates

/-- Every wrapper operation appends its actual outer request and returned value, retaining imported-key work and unforwarded reports in the source transcript. -/
theorem wrapper_transcript (primitives : Primitives) (query : OwnedSpec.Domain)
    (state : PublicState) (result : OwnedSpec.Range query × PublicState)
    (supported : result ∈ support ((wrapper primitives query).run state)) :
    result.2.transcript = state.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl coin =>
    simp only [wrapper, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    rfl
  | inr request =>
    cases request with
    | importKnown seed =>
      obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
      rfl
    | create =>
      simp only [wrapper, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      cases answer with
      | none =>
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        rfl
      | some created =>
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        rfl
    | service handle request =>
      simp only [wrapper, StateT.run] at supported
      cases found : state.owners[handle]? with
      | none =>
        simp only [found] at supported
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        rfl
      | some owner =>
        cases owner with
        | imported seed =>
          simp only [found] at supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl
        | generated identity publicKey =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨answer, _, supported⟩ := supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl
    | reveal handle =>
      simp only [wrapper, StateT.run] at supported
      cases found : state.owners[handle]? with
      | none =>
        simp only [found] at supported
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        rfl
      | some owner =>
        cases owner with
        | imported seed =>
          simp only [found] at supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl
        | generated identity publicKey =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨answer, _, supported⟩ := supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl
    | report candidate =>
      simp only [wrapper, StateT.run] at supported
      cases found : state.owners[candidate.identity]? with
      | none =>
        simp only [found] at supported
        obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
        rfl
      | some owner =>
        cases owner with
        | imported seed =>
          simp only [found] at supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl
        | generated identity publicKey =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨answer, _, supported⟩ := supported
          obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
          rfl

/-- The primitive challenger classes are explicit source classes; imports retain their separate local-work class. -/
def primitiveCost : Kind → Cost
  | .uniform => .uniform
  | .sign => .sign
  | .staticDh => .staticDh

/-- Primitive budgets use exactly the earlier reporting source predicates, with no relabeling of imports as oracle randomness. -/
theorem forwarded_primitive (kind : Kind) : ForwardedCost (primitiveCost kind) =
    reportingClass (dynamicClass (IsClass kind)) := by
  funext query
  cases query with
  | inl request =>
    cases request with
    | inl coin => cases kind <;> simp [ForwardedCost, forwardedCost, primitiveCost, reportingClass, dynamicClass, IsClass]
    | inr request =>
      cases request with
      | create => cases kind <;> simp [ForwardedCost, forwardedCost, primitiveCost, reportingClass, dynamicClass]
      | service identity request =>
        cases kind <;> cases request <;>
          simp [ForwardedCost, forwardedCost, primitiveCost, reportingClass, dynamicClass, IsClass]
      | reveal identity => cases kind <;> simp [ForwardedCost, forwardedCost, primitiveCost, reportingClass, dynamicClass]
  | inr candidate => cases kind <;> simp [ForwardedCost, forwardedCost, primitiveCost, reportingClass]

/-- Every selected joint-use reduction keeps all attempted service budgets and the other reserved seed draws, while known-seed evaluations remain local source work. -/
theorem reduction_query_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp OwnedSpec Result) (target : Fin (count + 1))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (kind : Kind) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsCost (primitiveCost kind)) bound) (jointPublic : PublicIdentity) :
    (globalReduction primitives target ordinaryFallback
      (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
        (PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback
          (routedClient primitives client))) jointPublic).IsQueryBoundP (IsClass kind)
            ((if kind = .uniform then 32 * count else 0) + bound) := by
  apply PqxdhDynamicIdentityReports.reportingReduction_query_bound
  simpa only [forwarded_primitive] using
    routedClient_query_bound primitives client (primitiveCost kind) bound bounded

/-- The complete selected challenger charges all N reserved seeds, including its own target seed and every unused reservation, plus all explicit source coins. -/
theorem reductionGame_uniform_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp OwnedSpec Result) (target : Fin (count + 1))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsCost .uniform) bound) :
    (game primitives (globalReduction primitives target ordinaryFallback
      (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
        (PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback
          (routedClient primitives client))))).IsTotalQueryBound (32 * (count + 1) + bound) := by
  apply PqxdhDynamicIdentityReports.reportingReductionGame_uniform_bound
  simpa only [← forwarded_primitive, primitiveCost] using
    routedClient_query_bound primitives client .uniform bound bounded

/-- The actual mixed-owner source samples only requested honest seeds. Known imports use the exact supplied bytes and introduce no hidden generator call. -/
theorem run_uniform_bound (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp OwnedSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (IsCost .create) qCreate)
    (coins : client.IsQueryBoundP (IsCost .uniform) qUniform) :
    (run primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [run_complete]
  simp only [OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
  apply PqxdhDynamicIdentityReports.reportingRun_uniform_bound
  · simpa only [forwarded_create] using routedClient_query_bound primitives client .create qCreate creates
  · simpa only [← PqxdhDynamicIdentityRouting.dynamicClass_uniform, ← forwarded_primitive, primitiveCost] using
      routedClient_query_bound primitives client .uniform qUniform coins

/-- Count actual outer attempts, including locally evaluated imported-key services and reports that cannot win. -/
def traceCount (kind : Cost) (state : PublicState) : ℕ :=
  state.transcript.countP (fun observation => decide (IsCost kind observation.1))

/-- Each actual public request contributes exactly one entry to its own retained source class. -/
theorem wrapper_trace_count (primitives : Primitives) (kind : Cost) (query : OwnedSpec.Domain)
    (state : PublicState) (result : OwnedSpec.Range query × PublicState)
    (supported : result ∈ support ((wrapper primitives query).run state)) :
    traceCount kind result.2 = traceCount kind state + if IsCost kind query then 1 else 0 := by
  simp only [traceCount, wrapper_transcript primitives query state result supported,
    List.countP_append, List.countP_singleton, decide_eq_true_eq]

/-- The complete public wrapper retains every declared source cost, including imports, rejected indices, repeated reveals and locally processed reports. -/
theorem wrapperRun_trace_bound (primitives : Primitives) (kind : Cost) {Result : Type}
    (client : OracleComp OwnedSpec Result) (bound : ℕ) (bounded : client.IsQueryBoundP (IsCost kind) bound)
    (state : PublicState) (result : Result × PublicState)
    (supported : result ∈ support ((simulateQ (wrapper primitives) client).run state)) :
    traceCount kind result.2 ≤ traceCount kind state + bound := by
  induction client using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    obtain ⟨reply, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    have counted := wrapper_trace_count primitives kind query state reply step
    have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 result rest
    by_cases selected : IsCost kind query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_true] at counted remaining
      omega
    · simp only [selected, ite_false] at counted remaining
      omega

/-- Actual interpretation cannot introduce a public transcript outside the exact wrapper support. The source keeps the same complete private generated state alongside it. -/
theorem run_public_support (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp OwnedSpec Result) (result : Result × (PublicState × ReportingState count))
    (supported : result ∈ support (run primitives count client)) :
    (result.1, result.2.1) ∈ support (routedClient primitives client) := by
  rw [run_complete] at supported
  obtain ⟨actual, actualSupported, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  apply OracleComp.support_simulateQ_run'_subset
    (PqxdhDynamicIdentityReports.reportingImpl primitives count) (routedClient primitives client)
    ⟨PqxdhDynamicIdentityReports.initialSource count,
      PqxdhDynamicIdentityReports.initialSnapshot count, false, []⟩
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ actualSupported

/-- All actual source attempts retain their separate class budgets; deterministic imported-key work is not made free by the absence of a primitive-oracle request. -/
theorem run_trace_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp OwnedSpec Result) (kind : Cost) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsCost kind) bound)
    (result : Result × (PublicState × ReportingState count)) (supported : result ∈ support (run primitives count client)) :
    traceCount kind result.2.1 ≤ bound := by
  have counted := wrapperRun_trace_bound primitives kind client bound bounded initialState
    (result.1, result.2.1) (run_public_support primitives count client result supported)
  simpa only [traceCount, initialState, List.countP_nil, Nat.zero_add] using counted

/-- A local known-input operation preserves the entire generated-source interpreter state, not just its public-key marginal. -/
theorem source_pure_step (primitives : Primitives) (count : ℕ) (query : OwnedSpec.Domain)
    (state : PublicState) (source : ReportingState count) (reply : OwnedSpec.Range query × PublicState)
    (localStep : (wrapper primitives query).run state = pure reply) :
    (sourceImpl primitives count query).run (state, source) =
      pure (reply.1, (reply.2, source)) := by
  rw [sourceImpl, QueryImpl.Stateful.link_impl_apply_run, localStep]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

/-- Import uses exactly the submitted seed and joint public map, publishes the next outer handle, and preserves all generated source state. -/
theorem import_source (primitives : Primitives) (count : ℕ) (seed : IdentitySeed)
    (state : PublicState) (source : ReportingState count) :
    (sourceImpl primitives count (.inr (.importKnown seed))).run (state, source) =
      pure ((state.owners.length, primitives.publicKeys seed),
        (record (.inr (.importKnown seed)) (state.owners.length, primitives.publicKeys seed)
          { state with owners := state.owners ++ [.imported seed] }, source)) :=
  source_pure_step primitives count (.inr (.importKnown seed)) state source _ rfl

/-- Both local primitive operations use the exact same imported seed, including the actual optional rejection of chosen static-DH input. Every generated history and secret stays in its original state. -/
theorem imported_service_source (primitives : Primitives) (count : ℕ) (handle : ℕ)
    (request : JointSpec.Domain) (seed : IdentitySeed) (state : PublicState) (source : ReportingState count)
    (owned : state.owners[handle]? = some (.imported seed)) :
    (sourceImpl primitives count (.inr (.service handle request))).run (state, source) =
      pure (some (primitiveReply primitives seed request),
        (record (.inr (.service handle request)) (some (primitiveReply primitives seed request)) state, source)) := by
  apply source_pure_step primitives count (.inr (.service handle request)) state source
    (some (primitiveReply primitives seed request),
      record (.inr (.service handle request)) (some (primitiveReply primitives seed request)) state)
  simp only [wrapper, StateT.run, owned]

/-- Revealing an imported owner returns the already submitted seed and retains the exact attempted reveal in the outer transcript. -/
theorem imported_reveal_source (primitives : Primitives) (count : ℕ) (handle : ℕ)
    (seed : IdentitySeed) (state : PublicState) (source : ReportingState count)
    (owned : state.owners[handle]? = some (.imported seed)) :
    (sourceImpl primitives count (.inr (.reveal handle))).run (state, source) =
      pure (some seed, (record (.inr (.reveal handle)) (some seed) state, source)) := by
  apply source_pure_step primitives count (.inr (.reveal handle)) state source
    (some seed, record (.inr (.reveal handle)) (some seed) state)
  simp only [wrapper, StateT.run, owned]

/-- Imported-owner reports remain in the complete outer history but cannot change generated-owner freshness or its sticky event. -/
theorem imported_report_source (primitives : Primitives) (count : ℕ) (candidate : DynamicForgery)
    (seed : IdentitySeed) (state : PublicState) (source : ReportingState count)
    (owned : state.owners[candidate.identity]? = some (.imported seed)) :
    (sourceImpl primitives count (.inr (.report candidate))).run (state, source) =
      pure ((), (record (.inr (.report candidate)) () state, source)) := by
  apply source_pure_step primitives count (.inr (.report candidate)) state source
    ((), record (.inr (.report candidate)) () state)
  simp only [wrapper, StateT.run, owned]

/-- A common endpoint bound incurs only the honest generated-identity factor. Imported handles and all adaptive reports retain their own work counts without multiplying this probability bound. -/
theorem report_advantage_le_count (primitives : Primitives) (count : ℕ)
    {Result : Type} (client : OracleComp OwnedSpec Result)
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : client.IsQueryBoundP (IsCost .create) (count + 1)) (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives
      (globalReduction primitives target ordinaryFallback
        (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
          (PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback
            (routedClient primitives client)))) ≤ epsilon) :
    Pr[ReportEvent | run primitives (count + 1) client] ≤ (count + 1 : ℕ) * epsilon := by
  exact (report_advantage_le_sum primitives count client fallback ordinaryFallback creates).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

end BeaconcryptCore.Computational.PqxdhKnownIdentityImports

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.report_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.report_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.reduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.reduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.reductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.reductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.run_trace_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.import_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.import_source

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_service_source

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_reveal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_reveal_source

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_report_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.imported_report_source

/--
info: 'BeaconcryptCore.Computational.PqxdhKnownIdentityImports.report_advantage_le_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKnownIdentityImports.report_advantage_le_count
