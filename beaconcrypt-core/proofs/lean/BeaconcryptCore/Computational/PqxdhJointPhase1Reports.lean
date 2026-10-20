import BeaconcryptCore.Computational.PqxdhKnownIdentityImports

/-!
# Source-facing Phase-1 fields in the adaptive joint identity experiment

Original four-field candidate reports retain their position among all identity operations. The public translator verifies the actual source-shaped candidate and selects its first unissued attached field against the complete signing history. Exact full-state and event simulation connects this field-origin event to the existing report-time joint weak-EUF experiment, without a field or report-position factor.

Earlier signing, optional converted-DH observations, identity creation, reveals and later compromise remain in the source. The endpoint's extra DH service is explicitly stronger than plain Ed25519 weak-EUF. The single-bundle changed-field corollary requires the independently checked exact three-message source log; no general once-only signing policy is assumed. Native decoding, ownership lookup, optional generator/error instantiation and root/record global composition remain separate boundaries. No primitive algorithm or implementation proof appears here.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhJointPhase1Reports
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports

/-- Preserve the actual attached buffers in the server's PQ, prekey, one-time verification order. -/
def candidateFields (candidate : Phase1Candidate) : List Forgery :=
  [candidate.pqKey, candidate.preKey, candidate.oneTimeKey].filterMap fun bytes =>
    (splitAttachedSignature bytes).map fun pair => ⟨pair.2, pair.1⟩

/-- Every extracted field of an actually accepted candidate verifies under the decoded identity. -/
theorem acceptedFields_valid (primitives : Primitives) (candidate : Phase1Candidate)
    (identity : Ed25519PublicKey) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate primitives.verify candidate = some (identity, decoded))
    (forgery : Forgery) (member : forgery ∈ candidateFields candidate) :
    primitives.verify identity forgery.message forgery.signature = true := by
  obtain ⟨_, pqSignature, preSignature, oneSignature, pqAttached, pqVerified,
    preAttached, preVerified, oneAttached, oneVerified⟩ :=
    acceptPhase1Candidate_some_witness primitives.verify candidate identity decoded accepted
  simp only [candidateFields, List.filterMap_cons, pqAttached, preAttached, oneAttached,
    splitAttachedSignature_attach, Option.map_some, List.filterMap_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact pqVerified
  · exact preVerified
  · exact oneVerified

/-- Selection uses only the actual public signing history; DH observations do not erase or invent signing messages. -/
def selectUnissued (history : History) (candidate : Phase1Candidate) : Option Forgery :=
  (candidateFields candidate).find? fun forgery => decide (forgery.message ∉ signedMessages history)

/-- An omitted result means every parsed candidate field was already signed, including repeated signatures on an old message. -/
theorem selectUnissued_none_iff (history : History) (candidate : Phase1Candidate) :
    selectUnissued history candidate = none ↔
      ∀ forgery ∈ candidateFields candidate, forgery.message ∈ signedMessages history := by
  simp [selectUnissued, List.find?_eq_none]

/-- A selected field is one of the original attached inputs and is fresh against the entire prior signing log. -/
theorem selectUnissued_some (history : History) (candidate : Phase1Candidate)
    (forgery : Forgery) (selected : selectUnissued history candidate = some forgery) :
    forgery ∈ candidateFields candidate ∧ forgery.message ∉ signedMessages history := by
  exact ⟨List.mem_of_find?_eq_some selected, of_decide_eq_true (List.find?_some (p := fun item : Forgery =>
    decide (item.message ∉ signedMessages history)) selected)⟩

/-- First-unissued selection loses no field factor and requires no assumption that all earlier DH/sign observations are absent. -/
theorem selected_weak_euf (primitives : Primitives) (candidate : Phase1Candidate)
    (identity : PublicIdentity) (decoded : Phase1KeyTuple) (history : History)
    (accepted : acceptPhase1Candidate primitives.verify candidate = some (identity.ed25519, decoded))
    (forgery : Forgery) (selected : selectUnissued history candidate = some forgery) :
    wins primitives identity forgery history = true := by
  obtain ⟨member, fresh⟩ := selectUnissued_some history candidate forgery selected
  simp [wins, acceptedFields_valid primitives candidate identity.ed25519 decoded accepted forgery member, fresh]

/-- A source-facing report keeps the selected generated index and all four decoded registration fields unchanged. -/
structure CandidateReport where
  identity : ℕ
  candidate : Phase1Candidate

/-- Translation parses and verifies the actual candidate, then selects one unissued original attached field. It never reads an identity seed. -/
def translateReport (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (state : PublicSnapshot count) : Option DynamicForgery :=
  if valid : report.identity < count then
    match state.keys report.identity with
    | none => none
    | some publicKey =>
      match acceptPhase1Candidate primitives.verify report.candidate with
      | none => none
      | some (candidateKey, _) =>
        if candidateKey = publicKey.ed25519 then
          (selectUnissued (state.history.histories ⟨report.identity, valid⟩) report.candidate).map
            fun forgery => ⟨report.identity, forgery⟩
        else none
  else none

/-- The protocol-facing event is actual typed acceptance under a created identity, with an unissued signed field and freshness at this report. Earlier and later non-target work is unrestricted. -/
def FieldOriginFailure (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (state : PublicSnapshot count) : Prop :=
  ∃ valid : report.identity < count, ∃ publicKey decoded,
    state.keys report.identity = some publicKey ∧
    acceptPhase1Candidate primitives.verify report.candidate = some (publicKey.ed25519, decoded) ∧
    ⟨report.identity, valid⟩ ∉ state.history.reveals ∧
    ∃ forgery ∈ candidateFields report.candidate,
      forgery.message ∉ signedMessages (state.history.histories ⟨report.identity, valid⟩)

/-- Every translated candidate is an ordinary weak-EUF report at the exact same generated index. -/
theorem translated_index (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (state : PublicSnapshot count) (forgery : DynamicForgery)
    (translated : translateReport primitives report state = some forgery) :
    forgery.identity = report.identity := by
  unfold translateReport at translated
  split at translated
  · split at translated
    · contradiction
    · split at translated
      · contradiction
      · split at translated
        · obtain ⟨selected, _, rfl⟩ := Option.map_eq_some_iff.mp translated
          rfl
        · contradiction
  · contradiction

/-- The original accepted-field event is exactly the existing report-time joint weak-EUF winning event after public translation. No target or field is guessed. -/
theorem translateReport_event (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (state : PublicSnapshot count) :
    (∃ forgery, translateReport primitives report state = some forgery ∧
      reportAccepted primitives forgery state = true) ↔ FieldOriginFailure primitives report state := by
  by_cases valid : report.identity < count
  · cases key : state.keys report.identity with
    | none => simp [translateReport, FieldOriginFailure, valid, key]
    | some publicKey =>
      cases accepted : acceptPhase1Candidate primitives.verify report.candidate with
      | none => simp [translateReport, FieldOriginFailure, valid, key, accepted]
      | some pair =>
        rcases pair with ⟨candidateKey, decoded⟩
        by_cases same : candidateKey = publicKey.ed25519
        · subst candidateKey
          cases selected : selectUnissued (state.history.histories ⟨report.identity, valid⟩)
              report.candidate with
          | none =>
            have allSigned := (selectUnissued_none_iff _ _).mp selected
            simp [translateReport, FieldOriginFailure, valid, key, accepted, selected]
            intro _
            exact allSigned
          | some forgery =>
            have wins := selected_weak_euf primitives report.candidate publicKey decoded
              (state.history.histories ⟨report.identity, valid⟩) accepted forgery selected
            have unissued : ∃ forgery ∈ candidateFields report.candidate,
                forgery.message ∉ signedMessages (state.history.histories ⟨report.identity, valid⟩) :=
              ⟨forgery, (selectUnissued_some _ _ _ selected).1,
                (selectUnissued_some _ _ _ selected).2⟩
            simp [translateReport, FieldOriginFailure, valid, key, accepted, selected,
              reportAccepted, wins, unissued]
        · simp [translateReport, FieldOriginFailure, valid, key, accepted, same]
  · simp [translateReport, FieldOriginFailure, valid]

abbrev CandidateSpec : OracleSpec CandidateReport := fun _ => Unit
abbrev ProtocolSpec := DynamicSpec + CandidateSpec

/-- Every attempted source candidate is retained, including malformed input, attacker-key candidates, prior-message reuse and post-reveal reports. -/
structure CandidateObservation where
  position : ℕ
  original : CandidateReport
  translated : Option DynamicForgery
  accepted : Bool

/-- The entire monitor is public: only actual public creation/service/reveal replies and original candidate reports enter it. -/
structure Monitor (count : ℕ) where
  requests : ℕ
  snapshot : PublicSnapshot count
  occurred : Bool
  attempted : List CandidateObservation

def initialMonitor (count : ℕ) : Monitor count := ⟨0, initialSnapshot count, false, []⟩

/-- The public field-origin detector runs the ordinary existing report predicate only on an original parsed field. -/
def candidateAccepted (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (snapshot : PublicSnapshot count) : Bool :=
  (translateReport primitives report snapshot).any fun forgery => reportAccepted primitives forgery snapshot

/-- Detection is precisely the accepted source-field origin event, with freshness at this report. -/
theorem candidateAccepted_iff (primitives : Primitives) {count : ℕ} (report : CandidateReport)
    (snapshot : PublicSnapshot count) :
    candidateAccepted primitives report snapshot = true ↔ FieldOriginFailure primitives report snapshot := by
  rw [← translateReport_event]
  simp [candidateAccepted, Option.any_eq_true]

/-- The protocol-facing wrapper forwards all identity operations unchanged and translates at most one ordinary forgery per original Phase-1 report. -/
def wrapper (primitives : Primitives) (count : ℕ) :
    QueryImpl ProtocolSpec (StateT (Monitor count) (OracleComp ReportingSpec)) := fun query state =>
  match query with
  | .inl request => do
    let answer ← ReportingSpec.query (.inl request)
    pure (answer, { state with
      requests := state.requests + 1
      snapshot := observe request answer state.snapshot })
  | .inr report => do
    let translated := translateReport primitives report state.snapshot
    let accepted := candidateAccepted primitives report state.snapshot
    match translated with
    | none => pure ()
    | some forgery => ReportingSpec.query (.inr forgery)
    pure ((), { state with
      requests := state.requests + 1
      occurred := state.occurred || accepted
      attempted := state.attempted ++ [⟨state.requests, report, translated, accepted⟩] })

/-- The translated client retains the complete public monitor and never receives a generated identity seed except through an actual permitted reveal. -/
def routedClient (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) : OracleComp ReportingSpec (Result × Monitor count) :=
  (simulateQ (wrapper primitives count) client).run (initialMonitor count)

/-- Source instrumentation keeps the existing complete private interpreter beside the public field-origin monitor. -/
def sourceImpl (primitives : Primitives) (count : ℕ) :
    QueryImpl ProtocolSpec (StateT (Monitor count × ReportingState count) ProbComp) :=
  QueryImpl.Stateful.link (wrapper primitives count) (reportingImpl primitives count)

def run (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) : ProbComp (Result × (Monitor count × ReportingState count)) :=
  (simulateQ (sourceImpl primitives count) client).run
    (initialMonitor count, ⟨initialSource count, initialSnapshot count, false, []⟩)

/-- Exact full-output translation retains all generated private state, prior joint-use observations, original candidates and later continuation. -/
theorem run_complete (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) :
    run primitives count client = (fun result => (result.1.1, (result.1.2, result.2))) <$>
      reportingRun primitives count (routedClient primitives count client) := by
  simp only [run, sourceImpl, QueryImpl.Stateful.simulateQ_link_run, reportingRun, routedClient]
  rfl

/-- The source and public monitor retain the same observed identity/history snapshot and the same sticky event. -/
def Compatible {count : ℕ} (monitor : Monitor count) (source : ReportingState count) : Prop :=
  monitor.snapshot = source.publicSnapshot ∧ monitor.occurred = source.occurred

/-- One translated source step preserves exact public observations and report-time origin recognition. -/
theorem wrapper_source_preserves (primitives : Primitives) (count : ℕ)
    (query : ProtocolSpec.Domain) (monitor : Monitor count) (source : ReportingState count)
    (compatible : Compatible monitor source)
    (result : (ProtocolSpec.Range query × Monitor count) × ReportingState count)
    (supported : result ∈ support ((simulateQ (reportingImpl primitives count)
      ((wrapper primitives count query).run monitor)).run source)) :
    Compatible result.1.2 result.2 := by
  obtain ⟨snapshot, occurred⟩ := compatible
  cases query with
  | inl request =>
    simp only [wrapper, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure] at supported
    obtain ⟨reply, actual, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    change reply ∈ support (do
      let response ← (sourceWithHistory count (lazyImpl primitives) request).run source.source
      pure (response.1, { source with
        source := response.2
        publicSnapshot := observe request response.1 source.publicSnapshot })) at actual
    obtain ⟨response, _, actual⟩ := (mem_support_bind_iff _ _ _).mp actual
    obtain rfl := eq_of_mem_support_pure actual
    exact ⟨congrArg (observe request response.1) snapshot, occurred⟩
  | inr report =>
    cases translated : translateReport primitives report monitor.snapshot with
    | none =>
      simp only [wrapper, StateT.run, translated, simulateQ_pure] at supported
      subst result
      simp only [Compatible, candidateAccepted, translated, Option.any_none, Bool.or_false]
      exact ⟨snapshot, occurred⟩
    | some forgery =>
      simp only [wrapper, StateT.run, translated, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure] at supported
      subst result
      simp only [Compatible, candidateAccepted, translated, Option.any_some]
      exact ⟨snapshot, by rw [snapshot, occurred]⟩

/-- The full linked interpreter preserves the public/actual snapshot and sticky-event relation. -/
theorem sourceImpl_preserves (primitives : Primitives) (count : ℕ) :
    QueryImpl.PreservesInv (sourceImpl primitives count) (fun state => Compatible state.1 state.2) := by
  intro query state compatible result supported
  rw [sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact wrapper_source_preserves primitives count query state.1 state.2 compatible inner actual

/-- Every complete source run recognizes exactly the underlying signature report-time event, even after later identity compromise. -/
theorem run_compatible (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support (run primitives count client)) : Compatible result.2.1 result.2.2 :=
  OracleComp.simulateQ_run_preservesInv (sourceImpl primitives count) _
    (sourceImpl_preserves primitives count) client _ ⟨rfl, rfl⟩ result supported

/-- Full-state event transport changes only product association; original candidates and the actual identity interpreter remain retained. -/
theorem run_event (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) :
    Pr{let result ← run primitives count client}[result.2.1.occurred = true] =
      Pr{let result ← reportingRun primitives count (routedClient primitives count client)}[
        result.2.occurred = true] := by
  calc
    _ = Pr{let result ← run primitives count client}[result.2.2.occurred = true] := by
      refine prEvent_congr_of_support _ _ _ fun result supported => ?_
      rw [(run_compatible primitives count client result supported).2]
    _ = _ := by rw [run_complete, prEvent_map]

/-- Each original identity request keeps its source class; candidate reports are separate local verification work. -/
def SourceClass (predicate : DynamicSpec.Domain → Prop) : ProtocolSpec.Domain → Prop
  | .inl request => predicate request
  | .inr _ => False

instance (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SourceClass predicate) := fun query => by
  cases query with
  | inl request => exact inferInstanceAs (Decidable (predicate request))
  | inr _ => exact inferInstanceAs (Decidable False)

/-- Translation forwards one unchanged identity request or zero such requests on a candidate report, including all rejection branches. -/
theorem wrapper_query_step (primitives : Primitives) (count : ℕ)
    (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (query : ProtocolSpec.Domain) (state : Monitor count) :
    ((wrapper primitives count query).run state).IsQueryBoundP (reportingClass predicate)
      (if SourceClass predicate query then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [wrapper, StateT.run, bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff, reportingClass, SourceClass]
    by_cases selected : predicate request <;> simp [selected]
  | inr report =>
    simp only [wrapper, StateT.run]
    cases translated : translateReport primitives report state.snapshot with
    | none => trivial
    | some forgery =>
      simp only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
        OracleComp.isQueryBoundP_query_iff, reportingClass, SourceClass]
      intro impossible
      exact impossible.elim

/-- Complete source translation retains the same identity-creation, uniform, signing, DH and reveal caps. -/
theorem routedClient_query_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (predicate : DynamicSpec.Domain → Prop)
    [DecidablePred predicate] (bound : ℕ)
    (bounded : client.IsQueryBoundP (SourceClass predicate) bound) :
    (routedClient primitives count client).IsQueryBoundP (reportingClass predicate) bound :=
  bounded.simulateQ_run_StateT_of_step (wrapper_query_step primitives count predicate) (initialMonitor count)

/-- Every original accepted-field origin failure reduces to the same N generated-identity joint weak-EUF family, without a field, report-position or session factor. -/
theorem fieldOrigin_advantage_le_sum (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : client.IsQueryBoundP (SourceClass IsCreate) (count + 1)) :
    Pr{let result ← run primitives (count + 1) client}[result.2.1.occurred = true] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback (routedClient primitives (count + 1) client)))) := by
  rw [run_event]
  exact reporting_advantage_le_identity_sum primitives count fallback ordinaryFallback _
    (routedClient_query_bound primitives (count + 1) client IsCreate (count + 1) creates)

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum_vcvioLegacy :
    ∀ (primitives : BeaconcryptCore.Computational.PqxdhJointIdentity.Primitives) (count : ℕ) {Result : Type} (client : OracleComp BeaconcryptCore.Computational.PqxdhJointPhase1Reports.ProtocolSpec Result) (fallback : BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : BeaconcryptCore.Computational.PqxdhJointIdentity.Forgery) (creates : client.IsQueryBoundP (BeaconcryptCore.Computational.PqxdhJointPhase1Reports.SourceClass BeaconcryptCore.Computational.PqxdhDynamicIdentityPool.IsCreate) (count + 1)), (probEvent (BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run primitives (count + 1) client) fun (result : Result × BeaconcryptCore.Computational.PqxdhJointPhase1Reports.Monitor (count + 1) × BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.ReportingState (count + 1)) => result.2.1.occurred = Bool.true) ≤ ∑ target : Fin (count + 1), BeaconcryptCore.Computational.PqxdhJointIdentity.advantage primitives (BeaconcryptCore.Computational.PqxdhJointIdentityFreshness.globalReduction primitives target ordinaryFallback (BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback (BeaconcryptCore.Computational.PqxdhDynamicIdentityReports.reportExtractor primitives (count + 1) fallback (BeaconcryptCore.Computational.PqxdhJointPhase1Reports.routedClient primitives (count + 1) client)))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum

/-- The native attached verifier uses the fixed sixty-four-byte signature prefix and rejects a shorter input. This is a functional primitive-format contract, not signature authentication. -/
theorem source_attached_adapter (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      c.verify publicKey.toList bytes = none) :
    HasAttachedVerificationAdapter (fun publicKey => c.verify publicKey.toList) primitives.verify := by
  intro publicKey bytes
  change c.verify publicKey.toList bytes = openAttached primitives.verify publicKey bytes
  cases split : splitAttachedSignature bytes with
  | none =>
    rw [shortRejects publicKey bytes ((splitAttachedSignature_eq_none_iff bytes).mp split)]
    simp [openAttached, split]
  | some pair =>
    obtain ⟨signature, message⟩ := pair
    have attached := (splitAttachedSignature_eq_some_iff bytes signature message).mp split
    subst bytes
    simpa [openAttached] using wiring.verifyAttached publicKey message signature

/-- Actual source verification order after four-field decoding: identity, PQ signature, prekey signature, one-time signature, then all core tag and width checks. -/
def sourceAccept (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : Phase1Candidate) : Option (Ed25519PublicKey × Phase1KeyTuple) := do
  let publicKey ← parseIdentity candidate.identityKey
  let pqPayload ← attachedVerify publicKey candidate.pqKey
  let prePayload ← attachedVerify publicKey candidate.preKey
  let onePayload ← attachedVerify publicKey candidate.oneTimeKey
  let _ ← parseIdentity candidate.identityKey
  let prekey ← parsePrekeyMessage prePayload
  let oneTime ← parseOneTimeMessage onePayload
  let pqKey ← parsePqMessage pqPayload
  pure (publicKey, ⟨prekey, oneTime, pqKey⟩)

/-- The complete source attached-verification/parser result equals the exact detached endpoint on all decoded field bytes, including short and malformed rejection. -/
theorem sourceAccept_eq (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (candidate : Phase1Candidate) :
    sourceAccept attachedVerify candidate = acceptPhase1Candidate primitives.verify candidate := by
  have equation : attachedVerify = openAttached primitives.verify := funext fun publicKey =>
    funext fun bytes => adapter publicKey bytes
  simp only [sourceAccept, acceptPhase1Candidate, decodePhase1Candidate, equation, bind_assoc, pure_bind]

/-- Parsing keeps at most three original fields, so first-unissued selection never enumerates a message universe. -/
theorem candidateFields_length (candidate : Phase1Candidate) : (candidateFields candidate).length ≤ 3 :=
  List.length_filterMap_le _ _

/-- Each selected joint reduction inherits all source signing/DH/rejection caps and pays the other N-1 reserved seeds. -/
theorem fieldReduction_query_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp ProtocolSpec Result) (kind : Kind) (bound : ℕ)
    (bounded : client.IsQueryBoundP (SourceClass (dynamicClass (IsClass kind))) bound)
    (jointPublic : PublicIdentity) :
    (globalReduction primitives target ordinaryFallback
      (routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback
          (routedClient primitives (count + 1) client))) jointPublic).IsQueryBoundP
      (IsClass kind) ((if kind = .uniform then 32 * count else 0) + bound) :=
  reportingReduction_query_bound primitives count target fallback ordinaryFallback _ kind bound
    (routedClient_query_bound primitives (count + 1) client (dynamicClass (IsClass kind)) bound bounded)
    jointPublic

/-- The complete selected challenger samples all N seeds, including the target seed kept private by the primitive endpoint. -/
theorem fieldReductionGame_uniform_bound (primitives : Primitives) (count : ℕ)
    (target : Fin (count + 1)) (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    {Result : Type} (client : OracleComp ProtocolSpec Result) (qUniform : ℕ)
    (bounded : client.IsQueryBoundP (SourceClass (dynamicClass (IsClass .uniform))) qUniform) :
    (game primitives (globalReduction primitives target ordinaryFallback
      (routedAdversary count ordinaryFallback
        (reportExtractor primitives (count + 1) fallback
          (routedClient primitives (count + 1) client))))).IsTotalQueryBound
      (32 * (count + 1) + qUniform) :=
  reportingReductionGame_uniform_bound primitives count target fallback ordinaryFallback _ qUniform
    (routedClient_query_bound primitives (count + 1) client (dynamicClass (IsClass .uniform)) qUniform bounded)

/-- Actual on-demand source execution charges only its actual creation budget, separately from reduction reservations. Candidate parsing/verification is local counted work. -/
theorem run_uniform_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (qCreate qUniform : ℕ)
    (creates : client.IsQueryBoundP (SourceClass IsCreate) qCreate)
    (coins : client.IsQueryBoundP (SourceClass PqxdhDynamicIdentityPool.IsUniform) qUniform) :
    (run primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [run_complete, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff]
  exact reportingRun_uniform_bound primitives count _ qCreate qUniform
    (routedClient_query_bound primitives count client IsCreate qCreate creates)
    (routedClient_query_bound primitives count client PqxdhDynamicIdentityPool.IsUniform qUniform coins)

/-- Every source report has a separate counted attempt, including malformed, attacker-key, reused-message and post-reveal cases. -/
def IsCandidateReport : ProtocolSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred IsCandidateReport := fun query => by
  cases query <;> simp [IsCandidateReport] <;> infer_instance

/-- Exact public instrumentation preserves the position of every original candidate relative to all identity operations. -/
theorem wrapper_observation (primitives : Primitives) (count : ℕ) (query : ProtocolSpec.Domain)
    (state : Monitor count) (result : ProtocolSpec.Range query × Monitor count)
    (supported : result ∈ support ((wrapper primitives count query).run state)) :
    result.2.requests = state.requests + 1 ∧
    result.2.attempted = (match query with
      | .inl _ => state.attempted
      | .inr report => state.attempted ++ [⟨state.requests, report,
          translateReport primitives report state.snapshot, candidateAccepted primitives report state.snapshot⟩]) ∧
    result.2.occurred = (match query with
      | .inl _ => state.occurred
      | .inr report => state.occurred || candidateAccepted primitives report state.snapshot) := by
  cases query with
  | inl request =>
    simp only [wrapper, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    exact ⟨rfl, rfl, rfl⟩
  | inr report =>
    cases translated : translateReport primitives report state.snapshot with
    | none =>
      simp only [wrapper, StateT.run, translated, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, by simp only [translated], rfl⟩
    | some forgery =>
      simp only [wrapper, StateT.run, translated, mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      obtain rfl := eq_of_mem_support_pure supported
      exact ⟨rfl, by simp only [translated], rfl⟩

/-- All candidate attempts are charged, whether or not a detached report is forwarded. -/
theorem wrapper_attempt_count (primitives : Primitives) (count : ℕ) (query : ProtocolSpec.Domain)
    (state : Monitor count) (result : ProtocolSpec.Range query × Monitor count)
    (supported : result ∈ support ((wrapper primitives count query).run state)) :
    result.2.attempted.length = state.attempted.length + if IsCandidateReport query then 1 else 0 := by
  rw [(wrapper_observation primitives count query state result supported).2.1]
  cases query <;> simp [IsCandidateReport]

/-- Finite adaptive execution charges each original candidate once, preserving malformed and unsuccessful positions. -/
theorem wrapperRun_attempt_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (qReport : ℕ)
    (bounded : client.IsQueryBoundP IsCandidateReport qReport)
    (state : Monitor count) (result : Result × Monitor count)
    (supported : result ∈ support ((simulateQ (wrapper primitives count) client).run state)) :
    result.2.attempted.length ≤ state.attempted.length + qReport := by
  induction client using OracleComp.inductionOn generalizing qReport state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    obtain ⟨reply, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    have counted := wrapper_attempt_count primitives count query state reply step
    have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 result rest
    by_cases report : IsCandidateReport query
    · have positive : 0 < qReport := bounded.1.resolve_left (not_not.mpr report)
      simp only [report, ite_true] at counted remaining
      omega
    · simp only [report, ite_false] at counted remaining
      omega

/-- Interpreting the same source cannot introduce a public monitor result outside the complete public translation support. -/
theorem run_public_support (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support (run primitives count client)) :
    (result.1, result.2.1) ∈ support (routedClient primitives count client) := by
  rw [run_complete] at supported
  obtain ⟨actual, actualSupported, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  apply OracleComp.support_simulateQ_run'_subset
    (reportingImpl primitives count) (routedClient primitives count client)
    ⟨initialSource count, initialSnapshot count, false, []⟩
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ actualSupported

/-- The actual full source run retains and charges all original candidate attempts, including those that produce no underlying forgery report. -/
theorem run_attempt_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (qReport : ℕ)
    (bounded : client.IsQueryBoundP IsCandidateReport qReport)
    (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support (run primitives count client)) :
    result.2.1.attempted.length ≤ qReport := by
  have counted := wrapperRun_attempt_bound primitives count client qReport bounded (initialMonitor count)
    (result.1, result.2.1) (run_public_support primitives count client result supported)
  simpa only [initialMonitor, List.length_nil, Nat.zero_add] using counted

/-- The sticky source event records exactly the accepted flags of original candidate observations. -/
theorem wrapper_occurred (primitives : Primitives) (count : ℕ) (query : ProtocolSpec.Domain)
    (state : Monitor count) (recorded : state.occurred = state.attempted.any (fun entry => entry.accepted))
    (result : ProtocolSpec.Range query × Monitor count)
    (supported : result ∈ support ((wrapper primitives count query).run state)) :
    result.2.occurred = result.2.attempted.any (fun entry => entry.accepted) := by
  have observation := wrapper_observation primitives count query state result supported
  rw [observation.2.1, observation.2.2]
  cases query <;> simp [List.any_append, recorded]

/-- Full continuation preserves every reported origin event even if later source operations reveal that identity. -/
theorem wrapperRun_occurred (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (state : Monitor count)
    (recorded : state.occurred = state.attempted.any (fun entry => entry.accepted))
    (result : Result × Monitor count)
    (supported : result ∈ support ((simulateQ (wrapper primitives count) client).run state)) :
    result.2.occurred = result.2.attempted.any (fun entry => entry.accepted) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact recorded
  | query_bind query next ih =>
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    obtain ⟨reply, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    exact ih reply.1 reply.2 (wrapper_occurred primitives count query state recorded reply step) result rest

/-- The final full source event is exactly the existence of an original candidate accepted by the report-time field-origin detector, with its retained source position. -/
theorem run_occurred (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support (run primitives count client)) :
    result.2.1.occurred = true ↔ ∃ report ∈ result.2.1.attempted, report.accepted = true := by
  have recorded := wrapperRun_occurred primitives count client (initialMonitor count) rfl
    (result.1, result.2.1) (run_public_support primitives count client result supported)
  rw [recorded, List.any_eq_true]

/-- With the retained source bundle's exact three-message log, any accepted same-identity changed field is unissued. This is the structural single-bundle corollary, not a premise on the general report reduction. -/
theorem singleBundle_unissued (primitives : Primitives) {Context : Type}
    (identity : Ed25519PublicKey) (material : Phase1Material Context) (candidate : Phase1Candidate)
    (changed : phase1FieldSubstitutionBit primitives.verify identity material candidate = true) :
    ∃ forgery ∈ candidateFields candidate, forgery.message ∉ honestPhase1Messages material := by
  obtain ⟨decoded, accepted, different⟩ :=
    (phase1FieldSubstitutionBit_eq_true_iff primitives.verify identity material candidate).mp changed
  obtain ⟨_, pqSignature, preSignature, oneSignature, pqAttached, _, preAttached, _, oneAttached, _⟩ :=
    acceptPhase1Candidate_some_witness primitives.verify candidate identity decoded accepted
  have fields : candidateFields candidate =
      [⟨pqMessage decoded.pqKey, pqSignature⟩, ⟨prekeyMessage decoded.prekey, preSignature⟩,
        ⟨oneTimeMessage decoded.oneTime, oneSignature⟩] := by
    simp [candidateFields, pqAttached, preAttached, oneAttached]
  by_cases pqChanged : decoded.pqKey ≠ material.pqKey
  · exact ⟨⟨pqMessage decoded.pqKey, pqSignature⟩, by simp [fields],
      pqMessage_not_mem_honestPhase1Messages_of_ne material decoded.pqKey pqChanged⟩
  · by_cases preChanged : decoded.prekey ≠ material.prekey
    · exact ⟨⟨prekeyMessage decoded.prekey, preSignature⟩, by simp [fields],
        prekeyMessage_not_mem_honestPhase1Messages_of_ne material decoded.prekey preChanged⟩
    · have oneChanged : decoded.oneTime ≠ material.oneTime := by
        intro equal
        exact different (Phase1KeyTuple.ext' (not_ne_iff.mp preChanged) equal (not_ne_iff.mp pqChanged))
      exact ⟨⟨oneTimeMessage decoded.oneTime, oneSignature⟩, by simp [fields],
        oneTimeMessage_not_mem_honestPhase1Messages_of_ne material decoded.oneTime oneChanged⟩

/-- The previously checked exact three-message source log plugs into the general report event; prior DH history remains unrestricted because it contributes no signing message. -/
theorem singleBundle_fieldOrigin (primitives : Primitives) {Context : Type} {count : ℕ}
    (report : CandidateReport) (state : PublicSnapshot count) (valid : report.identity < count)
    (publicKey : PublicIdentity) (material : Phase1Material Context)
    (created : state.keys report.identity = some publicKey)
    (fresh : ⟨report.identity, valid⟩ ∉ state.history.reveals)
    (exactLog : signedMessages (state.history.histories ⟨report.identity, valid⟩) = honestPhase1Messages material)
    (changed : phase1FieldSubstitutionBit primitives.verify publicKey.ed25519 material report.candidate = true) :
    FieldOriginFailure primitives report state := by
  obtain ⟨decoded, accepted, _⟩ :=
    (phase1FieldSubstitutionBit_eq_true_iff primitives.verify publicKey.ed25519 material report.candidate).mp changed
  refine ⟨valid, publicKey, decoded, created, accepted, fresh, ?_⟩
  rw [exactLog]
  exact singleBundle_unissued primitives publicKey.ed25519 material report.candidate changed

/-- The retained outer position counter counts every original query, including candidate reports rejected before forwarding. -/
theorem wrapperRun_request_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (qQueries : ℕ) (bounded : client.IsTotalQueryBound qQueries)
    (state : Monitor count) (result : Result × Monitor count)
    (supported : result ∈ support ((simulateQ (wrapper primitives count) client).run state)) :
    result.2.requests ≤ state.requests + qQueries := by
  induction client using OracleComp.inductionOn generalizing qQueries state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isTotalQueryBound_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    obtain ⟨reply, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    have counted := (wrapper_observation primitives count query state reply step).1
    have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 result rest
    omega

/-- Actual complete source positions retain their original total-query bound; no failed candidate slot is declared free. -/
theorem run_request_bound (primitives : Primitives) (count : ℕ) {Result : Type}
    (client : OracleComp ProtocolSpec Result) (qQueries : ℕ) (bounded : client.IsTotalQueryBound qQueries)
    (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support (run primitives count client)) : result.2.1.requests ≤ qQueries := by
  have counted := wrapperRun_request_bound primitives count client qQueries bounded (initialMonitor count)
    (result.1, result.2.1) (run_public_support primitives count client result supported)
  simpa only [initialMonitor, Nat.zero_add] using counted

end BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.translateReport_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.translateReport_event

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_compatible

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_event

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.source_attached_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.source_attached_adapter

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.sourceAccept_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.sourceAccept_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldReductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.fieldReductionGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.wrapper_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.wrapper_observation

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_attempt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_attempt_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_occurred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_occurred

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.singleBundle_fieldOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.singleBundle_fieldOrigin

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_request_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.run_request_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1Reports.candidateFields_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1Reports.candidateFields_length
