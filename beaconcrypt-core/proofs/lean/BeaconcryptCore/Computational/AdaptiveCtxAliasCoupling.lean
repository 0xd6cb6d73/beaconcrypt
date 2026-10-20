import BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxReplayTable AdaptiveCtxHonestCache AdaptiveCtxStoppedRaw
open CtxHonestTagSampling CtxComputationalSecurity

/-- Reconstruct the logged reply only from the actual already installed commitment cell and the previous challenger-produced sealing log. -/
def postLoggedReply (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) : Option Pqxdh.Bytes :=
  match decode raw with
  | none => none
  | some target => if state.ctx.cache.suffixCache (outerSuffix target.nonce target.context target.record.tag) = some target.record.commit then
      AdaptiveRawNonceAead.loggedPlaintext (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target)
    else none

/-- Both source raw kernels perform the same actual private lookup; replacing the replay-only optional reply with its logged opening recovers the exact logged kernel and full next state. -/
theorem loggedRaw_eq_replayRaw (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    EvalDistEq (loggedRaw decode raw state)
      ((fun result => (postLoggedReply decode raw result.2, result.2)) <$> replayRaw decode raw state) := by
  cases parsed : decode raw with
  | none => simp [loggedRaw, replayRaw, postLoggedReply, parsed]
  | some target =>
    simp only [loggedRaw, replayRaw, parsed, map_bind, map_pure]
    refine OracleComp.EvalDistEq.bind_congr_of_support _ fun lookup supported => ?_
    have installed := suffixStep_installs _ _ lookup supported
    have pureEq : ∀ {α : Type} {a b : α}, a = b → EvalDistEq (pure a : ProbComp α) (pure b) :=
      fun same => by subst same; exact EvalDistEq.refl _
    apply pureEq
    simp only [postLoggedReply, parsed, installed, Option.some.injEq]
    congr 1
    simp only [ctxIndependentTagStateToModifiedNonceAead, eq_comm]

/-- Replay-only raw processing preserves the actual commitment, nonce and base-log invariants while retaining every rejected lookup. -/
theorem replayRaw_preserves_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) (invariant : LoggedInvariant c key state)
    (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (replayRaw decode raw state)) :
    LoggedInvariant c key result.2 := by
  cases parsed : decode raw with
  | none =>
    simp only [replayRaw, parsed, mem_support_pure_iff] at supported
    subst result
    exact invariant
  | some target =>
    simp only [replayRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, lookupSupported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    refine ⟨?_, invariant.2⟩
    intro entry member
    exact suffixStep_preserves _ _ _ _ (invariant.1 entry member) _ lookupSupported

/-- On the actual supported raw result, its optional plaintext differs from the logged opening exactly at the checked post-lookup alias event. -/
theorem replayRaw_discrepancy_iff (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) (invariant : LoggedInvariant c key state)
    (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (replayRaw decode raw state)) :
    postLoggedReply decode raw result.2 ≠ result.1 ↔ RawBad decode raw result.2 := by
  cases parsed : decode raw with
  | none =>
    simp only [replayRaw, parsed, mem_support_pure_iff] at supported
    subst result
    simp [postLoggedReply, RawBad, parsed]
  | some target =>
    simp only [replayRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, lookupSupported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    have installed := suffixStep_installs _ _ lookup lookupSupported
    have classified := replay_discrepancy_iff c key state invariant target lookup lookupSupported
    rw [← replayPlaintext_none_iff] at classified
    simp only [postLoggedReply, parsed, RawBad, Option.some.injEq, exists_eq_left',
      Eligible, installed, ctxIndependentTagStateToModifiedNonceAead] at ⊢ classified
    simpa only [replayPlaintext, eq_comm, and_assoc, and_left_comm, and_comm] using classified

/-- Both games share the actual replay kernel and a sticky optional-reply discrepancy flag; only the logged world's returned plaintext is reconstructed. -/
noncomputable def flaggedImpl (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) : QueryImpl ReceiveSpec (StateT (AdaptiveCtxReceive.ReceiveState × Bool) ProbComp) :=
  fun query state => match query with
  | .inl request => do
    let result ← (replayImpl decode c key (.inl request)).run state.1
    pure (result.1, (result.2, state.2))
  | .inr raw => do
    let result ← replayRaw decode raw state.1
    let actual := postLoggedReply decode raw result.2
    pure (if logged then actual else result.1,
      (result.2, state.2 || decide (actual ≠ result.1)))

/-- Every complete next-state output whose flag remains clear has exactly the same probability in both optional-plaintext games. -/
theorem flaggedImpl_agree_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (answer : ReceiveSpec.Range query) (next : AdaptiveCtxReceive.ReceiveState) :
    Pr{let x ← (flaggedImpl true decode c key query).run (state, false)}[x = (answer, (next, false))] =
      Pr{let x ← (flaggedImpl false decode c key query).run (state, false)}[x = (answer, (next, false))] := by
  classical
  let : DecidableEq AdaptiveCtxReceive.ReceiveState := Classical.decEq _
  cases query with
  | inl request => rfl
  | inr raw =>
    unfold flaggedImpl StateT.run
    refine prEvent_bind_congr _ _ _ _ _ fun result => ?_
    simp only [prEvent_pure]
    by_cases equal : postLoggedReply decode raw result.2 = result.1
    · simp [equal]
    · simp [equal]

/-- Every primitive, malformed input, failed lookup and subsequent divergent continuation preserves an already raised flag. -/
theorem flaggedImpl_bad_mono (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState × Bool) (bad : state.2 = true) :
    ∀ result ∈ support ((flaggedImpl logged decode c key query).run state), result.2.2 = true := by
  intro result supported
  cases query with
  | inl request =>
    simp only [flaggedImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨reply, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    exact bad
  | inr raw =>
    simp only [flaggedImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨reply, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    simp only [bad, Bool.true_or]

/-- Once a discrepancy occurs, every later complete adaptive execution retains it with probability one. -/
theorem flagged_bad_probability_one {Result : Type} (logged : Bool) (decode : RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) :
    Pr{let result ← (simulateQ (flaggedImpl logged decode c key) adversary).run (state, true)}[result.2.2 = true] = 1 := by
  exact OracleComp.prEvent_eq_one_of_forall_mem_support _ _
    (simulateQ_run_preservesInv (flaggedImpl logged decode c key) (fun pair => pair.2 = true)
      (flaggedImpl_bad_mono logged decode c key) adversary (state, true) rfl)

/-- The replay-only source preserves the same actual-cache invariant for every original query class. -/
theorem replayImpl_preserves_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (replayImpl decode c key) (LoggedInvariant c key) := by
  intro query state invariant result supported
  cases query with
  | inr raw => exact replayRaw_preserves_invariant decode c key raw state invariant result supported
  | inl request =>
    cases request <;> exact loggedImpl_preserves_invariant decode c key _ state invariant result supported

/-- The full replay-only execution's sticky discrepancy probability is exactly the monitor already bounded by the stopped raw family. -/
theorem flagged_bad_eq_first {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (invariant : LoggedInvariant c key state) :
    Pr{let result ← (simulateQ (flaggedImpl false decode c key) adversary).run (state, false)}[result.2.2 = true] =
    Pr{let bad ← firstDiscrepancy decode c key adversary state}[bad = true] := by
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, firstDiscrepancy_pure, prEvent_pure]
  | query_bind query next ih =>
    cases query with
    | inr raw =>
      rw [firstDiscrepancy_receive]
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query]
      change Pr{let result ← (do
        let result ← (do
          let reply ← replayRaw decode raw state
          pure (reply.1, (reply.2, decide (postLoggedReply decode raw reply.2 ≠ reply.1))))
        (simulateQ (flaggedImpl false decode c key) (next result.1)).run result.2)}[result.2.2 = true] = _
      simp only [bind_assoc, pure_bind]
      refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun result supported => ?_
      have same := replayRaw_discrepancy_iff decode c key raw state invariant result supported
      have kept := replayRaw_preserves_invariant decode c key raw state invariant result supported
      by_cases bad : RawBad decode raw result.2
      · have decision : decide (postLoggedReply decode raw result.2 ≠ result.1) = true := decide_eq_true (same.mpr bad)
        rw [decision, flagged_bad_probability_one, ite_eq_left bad, prEvent_pure]
        simp
      · have decision : decide (postLoggedReply decode raw result.2 ≠ result.1) = false := decide_eq_false (fun different => bad (same.mp different))
        rw [decision, ite_eq_right bad, ih result.1 result.2 kept]
    | inl request =>
      rw [firstDiscrepancy_primitive]
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query]
      change Pr{let result ← (do
        let result ← (do
          let reply ← (replayImpl decode c key (.inl request)).run state
          pure (reply.1, (reply.2, false)))
        (simulateQ (flaggedImpl false decode c key) (next result.1)).run result.2)}[result.2.2 = true] = _
      simp only [bind_assoc, pure_bind]
      refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun result supported => ?_
      exact ih result.1 result.2
        (replayImpl_preserves_invariant decode c key (.inl request) state invariant result supported)

/-- The two uninstrumented source interpreters differ only in the permitted raw optional plaintext. -/
noncomputable def sourceImpl (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  if logged then loggedImpl decode c key else replayImpl decode c key

/-- Project only the auxiliary flag; preserve the complete protocol-facing result and actual private state. -/
def sourceProjection {Result : Type} (result : Result × (AdaptiveCtxReceive.ReceiveState × Bool)) :
    Result × AdaptiveCtxReceive.ReceiveState := (result.1, result.2.1)

/-- The exact complete query result projects to the intended source kernel in both worlds. -/
theorem flagged_query_projection (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState × Bool) :
    EvalDistEq (sourceProjection <$> (flaggedImpl logged decode c key query).run state)
      ((sourceImpl logged decode c key query).run state.1) := by
  cases query with
  | inl request =>
    cases request <;> cases logged <;>
      simp [flaggedImpl, sourceImpl, sourceProjection, replayImpl, loggedImpl,
        StateT.run, bind_pure_comp, Functor.map_map]
  | inr raw =>
    cases logged with
    | false =>
      simp [flaggedImpl, sourceImpl, sourceProjection, replayImpl,
        StateT.run, bind_pure_comp, Functor.map_map]
    | true =>
      simp only [flaggedImpl, sourceImpl, ↓reduceIte, StateT.run,
        map_bind, map_pure, sourceProjection, loggedImpl]
      change EvalDistEq (do
        let result ← replayRaw decode raw state.1
        pure (postLoggedReply decode raw result.2, result.2))
          (loggedRaw decode raw state.1)
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (loggedRaw_eq_replayRaw decode raw state.1).symm

/-- Full adaptive source simulation preserves every reply, cache, log and counter, projecting only the ghost discrepancy flag. -/
theorem flagged_run_projection {Result : Type} (logged : Bool) (decode : RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState × Bool) :
    EvalDistEq (sourceProjection <$> (simulateQ (flaggedImpl logged decode c key) adversary).run state)
      ((simulateQ (sourceImpl logged decode c key) adversary).run state.1) := by
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value => simp [sourceProjection]
  | query_bind query next ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, map_bind, OracleQuery.input_query]
    change EvalDistEq (do
      let result ← (flaggedImpl logged decode c key query).run state
      sourceProjection <$> (simulateQ (flaggedImpl logged decode c key) (next result.1)).run result.2) _
    have folded : ((flaggedImpl logged decode c key query).run state >>= fun result =>
        (simulateQ (sourceImpl logged decode c key) (next result.1)).run result.2.1) =
        ((sourceProjection <$> (flaggedImpl logged decode c key query).run state) >>= fun result =>
          (simulateQ (sourceImpl logged decode c key) (next result.1)).run result.2) := by
      rw [bind_map_left]
      rfl
    refine (OracleComp.EvalDistEq.bind_congr_of_support _ fun result _ => ih result.1 result.2).trans ?_
    rw [folded]
    exact (flagged_query_projection logged decode c key query state).bind_left _

/-- Both full optional-plaintext games encounter their first discrepancy with the same probability, even though later adversarial continuations may differ. -/
theorem flagged_bad_eq {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) (state : AdaptiveCtxReceive.ReceiveState) :
    Pr{let result ← (simulateQ (flaggedImpl true decode c key) adversary).run (state, false)}[result.2.2 = true] =
      Pr{let result ← (simulateQ (flaggedImpl false decode c key) adversary).run (state, false)}[result.2.2 = true] := by
  have equal := OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (flaggedImpl true decode c key) (flaggedImpl false decode c key)
    (fun query state answer next => by
      simpa only [VCVioLegacy.probOutput_eq_prEvent] using
        flaggedImpl_agree_good decode c key query state answer next)
    (flaggedImpl_bad_mono true decode c key)
    (flaggedImpl_bad_mono false decode c key) adversary state
  rw [VCVioLegacy.probEvent_eq_prEvent, VCVioLegacy.probEvent_eq_prEvent] at equal
  exact equal

/-- The complete source state and actual optional plaintext differ only at one of the qRaw charged commitment guesses. -/
theorem flagged_distance_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    ENNReal.ofReal (tvDist
      ((simulateQ (flaggedImpl true decode c key) adversary).run (initialState, false))
      ((simulateQ (flaggedImpl false decode c key) adversary).run (initialState, false))) ≤
        (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  have distance := OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (flaggedImpl true decode c key) (flaggedImpl false decode c key) adversary initialState
    (fun query state answer next => by
      simpa only [VCVioLegacy.probOutput_eq_prEvent] using
        flaggedImpl_agree_good decode c key query state answer next)
    (flaggedImpl_bad_mono true decode c key)
    (flaggedImpl_bad_mono false decode c key)
  rw [VCVioLegacy.probEvent_eq_prEvent] at distance
  rw [flagged_bad_eq, flagged_bad_eq_first decode c key adversary initialState (initial_invariant c key)] at distance
  exact (ENNReal.ofReal_le_ofReal distance).trans
    (ENNReal.ofReal_toReal_le.trans (firstDiscrepancy_bound decode c key adversary qRaw bounded))

/-- Removing only the ghost flag yields the exact full logged/replay source distance, retaining every private cache and failed raw lookup. -/
theorem source_distance_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    ENNReal.ofReal (tvDist
      ((simulateQ (loggedImpl decode c key) adversary).run initialState)
      ((simulateQ (replayImpl decode c key) adversary).run initialState)) ≤
        (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  have projection := tvDist_map_le sourceProjection
    ((simulateQ (flaggedImpl true decode c key) adversary).run (initialState, false))
    ((simulateQ (flaggedImpl false decode c key) adversary).run (initialState, false))
  have same : tvDist
      (sourceProjection <$> (simulateQ (flaggedImpl true decode c key) adversary).run (initialState, false))
      (sourceProjection <$> (simulateQ (flaggedImpl false decode c key) adversary).run (initialState, false)) =
      tvDist ((simulateQ (loggedImpl decode c key) adversary).run initialState)
        ((simulateQ (replayImpl decode c key) adversary).run initialState) := by
    have flaggedTrue := (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).2
      (flagged_run_projection true decode c key adversary (initialState, false))
    have flaggedFalse := (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).2
      (flagged_run_projection false decode c key adversary (initialState, false))
    simp only [tvDist, flaggedTrue, flaggedFalse, sourceImpl, Bool.false_eq_true, ↓reduceIte]
  rw [same] at projection
  exact (ENNReal.ofReal_le_ofReal projection).trans (flagged_distance_bound decode c key adversary qRaw bounded)

/-- The sampled key remains paired with the complete terminal source state only for analysis; the client never receives that key. -/
noncomputable def retainedReplayGame {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Result) : ProbComp (CtxKey × (Result × AdaptiveCtxReceive.ReceiveState)) := do
  let key ← $ᵗ CtxKey
  let result ← (simulateQ (replayImpl decode c key) adversary).run initialState
  pure (key, result)

/-- Mixing the same sampled key with both complete source continuations preserves the qRaw/2^512 bound and all key/transcript correlations. -/
theorem retained_distance_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    ENNReal.ofReal (tvDist (retainedDirectLoggedGame decode c adversary)
      (retainedReplayGame decode c adversary)) ≤ (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  simp only [retainedDirectLoggedGame, loggedGame, retainedReplayGame, bind_pure_comp]
  apply ofReal_tvDist_bind_left_le_const'
  intro key
  exact (ENNReal.ofReal_le_ofReal (tvDist_map_le (Prod.mk key) _ _)).trans
    (source_distance_bound decode c key adversary qRaw bounded)

/-- Canonical shared-ROM adaptive CTX is close to full-tuple replay-only opening with the existing conventional reduction, both explicit integrity sums, the public-prefix term and one qRaw/2^512 private-guess term. -/
theorem canonical_replay_distance_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp ReceiveSpec Result)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (tvDist
      (AdaptiveCtxPrefixValidation.canonicalProjection <$> AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c adversary)
      (retainedReplayGame decode c adversary)) ≤
        ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
          (AdaptiveCtxPrefixValidation.validationReduction decode c adversary qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) +
        (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  have canonical := AdaptiveCtxPrefixValidation.canonical_distance_le_indDollar_add_two_intctxt
    decode c fallback adversary qHash qSeal qRaw hashBound sealBound rawBound small
  rw [← retainedDirectLoggedGame_eq_client] at canonical
  have aliasBound := retained_distance_bound decode c adversary qRaw rawBound
  have triangle := ENNReal.ofReal_le_ofReal (tvDist_triangle
    (AdaptiveCtxPrefixValidation.canonicalProjection <$> AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c adversary)
    (retainedDirectLoggedGame decode c adversary) (retainedReplayGame decode c adversary))
  rw [ENNReal.ofReal_add (tvDist_nonneg _ _) (tvDist_nonneg _ _)] at triangle
  exact triangle.trans (add_le_add canonical aliasBound)

end BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.loggedRaw_eq_replayRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.loggedRaw_eq_replayRaw

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.replayRaw_discrepancy_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.replayRaw_discrepancy_iff

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flaggedImpl_agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flaggedImpl_agree_good

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flaggedImpl_bad_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flaggedImpl_bad_mono

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_bad_eq_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_bad_eq_first

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_run_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_run_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_bad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.flagged_bad_eq

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.source_distance_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.source_distance_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.retained_distance_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.retained_distance_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.canonical_replay_distance_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling.canonical_replay_distance_bound
