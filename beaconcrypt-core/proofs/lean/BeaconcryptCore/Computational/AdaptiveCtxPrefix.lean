import BeaconcryptCore.Computational.AdaptiveCtxRetainedKey

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxPrefix
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxPrefixIsolation
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent

/-- Only a public complete-input hash request can cross the hidden key prefix. Private raw-attempt lookups remain in both games. -/
def prefixFires (key : CtxKey) : ReceiveSpec.Domain → Bool
  | .inl (.inr (.inl query)) => decide (SecretPrefixQuery key query.2)
  | _ => false

/-- Routed shared-cache and independent-public experiments retain exactly the same raw optional opening and private cache updates. -/
noncomputable def sourceImpl (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) : QueryImpl ReceiveSpec (StateT ReceiveState ProbComp) :=
  if routed then splitImpl decode c key else independentImpl decode c key

/-- Away from the actual public key prefix, the complete query kernels agree. -/
theorem sourceImpl_eq_of_not_prefix (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (notPrefix : prefixFires key query = false) :
    sourceImpl true decode c key query = sourceImpl false decode c key query := by
  funext state
  cases query with
  | inl query =>
    cases query with
    | inl coin => rfl
    | inr query =>
      cases query with
      | inl input =>
        have no : ¬SecretPrefixQuery key input.2 := by simpa [prefixFires] using notPrefix
        have step := ctxSplitRoutedPublicOracle_eq_independent_of_not_prefix key input state.ctx no
        change (do
          let (answer, ctx) ← (ctxSplitRoutedPublicOracle key input).run state.ctx
          pure (answer, (⟨ctx, state.rawAttempts, state.privateInputs⟩ : ReceiveState)) : ProbComp _) = _
        rw [step]
        rfl
      | inr input => rfl
  | inr raw => rfl

/-- The sticky prefix bit is analysis instrumentation; it never changes an adversarial reply. -/
noncomputable def flaggedImpl (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) : QueryImpl ReceiveSpec (StateT (ReceiveState × Bool) ProbComp) :=
  fun query => withStickyBad (prefixFires key query) (sourceImpl routed decode c key query)

/-- Any prefix request makes the bit true, even if its hash was previously cached. -/
theorem flaggedImpl_bad_mono (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : ReceiveState × Bool)
    (bad : state.2 = true) (result : ReceiveSpec.Range query × (ReceiveState × Bool))
    (supported : result ∈ support ((flaggedImpl routed decode c key query).run state)) :
    result.2.2 = true :=
  withStickyBad_mono _ _ state bad result supported

/-- Output-based coupling permits the two public caches to differ on the prefix query itself. -/
theorem flaggedImpl_agree_good (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : ReceiveState)
    (answer : ReceiveSpec.Range query) (next : ReceiveState) :
    Pr[= (answer, (next, false)) | (flaggedImpl true decode c key query).run (state, false)] =
      Pr[= (answer, (next, false)) | (flaggedImpl false decode c key query).run (state, false)] := by
  cases fires : prefixFires key query with
  | false => rw [flaggedImpl, flaggedImpl, sourceImpl_eq_of_not_prefix decode c key query fires]
  | true =>
    have zero (routed : Bool) :
        Pr[= (answer, (next, false)) | (flaggedImpl routed decode c key query).run (state, false)] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro supported
      have hit := withStickyBad_true (sourceImpl routed decode c key query)
        (state, false) (answer, next, false) (by simpa only [flaggedImpl, fires] using supported)
      simp at hit
    rw [zero true, zero false]

/-- The complete arbitrary receive continuation, including both dictionaries and every failed private lookup. -/
noncomputable def flaggedGame (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × (ReceiveState × Bool)) :=
  (simulateQ (flaggedImpl routed decode c key) adversary).run (initialState, false)

/-- Removing only the analysis bit preserves every actual reply and complete source poststate. -/
theorem flaggedGame_projection (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Prod.map id Prod.fst <$> flaggedGame routed decode c key adversary =
      (simulateQ (sourceImpl routed decode c key) adversary).run initialState := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (flaggedImpl routed decode c key) (sourceImpl routed decode c key) Prod.fst
    (fun query state => withStickyBad_fst_map_run _ _ state) adversary (initialState, false)

/-- Both adaptive worlds encounter the actual public-prefix event with exactly the same probability. -/
theorem flaggedGame_bad_eq (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Pr[fun result => result.2.2 = true | flaggedGame true decode c key adversary] =
      Pr[fun result => result.2.2 = true | flaggedGame false decode c key adversary] :=
  OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (flaggedImpl true decode c key) (flaggedImpl false decode c key)
    (flaggedImpl_agree_good decode c key) (flaggedImpl_bad_mono true decode c key)
    (flaggedImpl_bad_mono false decode c key) adversary initialState

/-- The shared-cache routing hop charges its real adaptive prefix event once, while retaining all post-cache effects. -/
theorem flaggedGame_distance_le_prefix (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    tvDist (flaggedGame true decode c key adversary) (flaggedGame false decode c key adversary) ≤
      Pr[fun result => result.2.2 = true | flaggedGame false decode c key adversary].toReal := by
  rw [← flaggedGame_bad_eq]
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (flaggedImpl true decode c key) (flaggedImpl false decode c key)
    adversary initialState (flaggedImpl_agree_good decode c key)
    (flaggedImpl_bad_mono true decode c key) (flaggedImpl_bad_mono false decode c key)

/-- Projected canonical shared-ROM receive and direct independent-public receive differ only at the actual prefix event. -/
theorem canonicalGame_distance_le_prefix (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    tvDist (Prod.map id (splitState key) <$> canonicalGame decode c key adversary)
      (independentGame decode c key adversary) ≤
      Pr[fun result => result.2.2 = true | flaggedGame false decode c key adversary].toReal := by
  rw [canonicalGame_split]
  change tvDist ((simulateQ (sourceImpl true decode c key) adversary).run initialState)
    ((simulateQ (sourceImpl false decode c key) adversary).run initialState) ≤ _
  rw [← flaggedGame_projection, ← flaggedGame_projection]
  exact (tvDist_map_le (Prod.map id Prod.fst) _ _).trans
    (flaggedGame_distance_le_prefix decode c key adversary)

/-- The public trace stores each requested complete byte string, including repeated cache hits. -/
def publicTraceAfter (query : ReceiveSpec.Domain) (previous : List Pqxdh.Bytes) : List Pqxdh.Bytes :=
  match query with
  | .inl (.inr (.inl input)) => input.2 :: previous
  | _ => previous

/-- Raw receive leaves the public query trace unchanged even when its private suffix lookup misses. -/
theorem splitRaw_publicInputs (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : ReceiveState) (result : Option Pqxdh.Bytes × ReceiveState)
    (supported : result ∈ support (splitRaw decode c key raw state)) :
    result.2.ctx.publicInputs = state.ctx.publicInputs := by
  cases parsed : decode raw with
  | none =>
    simp only [splitRaw, parsed, mem_support_pure_iff] at supported
    subst result
    rfl
  | some target =>
    simp only [splitRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨⟨digest, cache⟩, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    rfl

/-- The complete source query kernel records exactly its public input and no private input in that public trace. -/
theorem independentImpl_publicInputs (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : ReceiveState) (result : ReceiveSpec.Range query × ReceiveState)
    (supported : result ∈ support ((independentImpl decode c key query).run state)) :
    result.2.ctx.publicInputs = publicTraceAfter query state.ctx.publicInputs := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      simp only [independentImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
    | inr query =>
      cases query with
      | inl input =>
        change result ∈ support (independentCtx c key (.inl input) state) at supported
        simp only [independentCtx, bind_pure_comp] at supported
        obtain ⟨⟨answer, ctx⟩, step, equality⟩ := OracleComp.mem_support_map_peel _ _ supported
        subst result
        exact CtxNonceAeadIndDollar.ctxIndependentPublicOracle_publicInputs input state.ctx (answer, ctx) step
      | inr input =>
        change result ∈ support (independentCtx c key (.inr input) state) at supported
        simp only [independentCtx, bind_pure_comp] at supported
        obtain ⟨⟨answer, ctx⟩, step, equality⟩ := OracleComp.mem_support_map_peel _ _ supported
        subst result
        exact CtxNonceAeadIndDollar.ctxKeyFreeSealOracle_publicInputs c key input state.ctx (answer, ctx) step
  | inr raw => exact splitRaw_publicInputs decode c key raw state result supported

/-- The analysis bit is exactly membership in the actual complete public-input trace. -/
def PrefixInvariant (key : CtxKey) (state : ReceiveState × Bool) : Prop :=
  state.2 = true ↔ ∃ input ∈ state.1.ctx.publicInputs, SecretPrefixQuery key input

/-- No private raw lookup, including a failed one, is mislabeled as a public key guess. -/
theorem flaggedImpl_preserves_prefix (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (flaggedImpl false decode c key) (PrefixInvariant key) := by
  intro query state invariant result supported
  obtain ⟨intermediate, step, rfl⟩ := withStickyBad_result_state (prefixFires key query)
    (sourceImpl false decode c key query) state result supported
  have trace := independentImpl_publicInputs decode c key query state.1 intermediate step
  unfold PrefixInvariant at invariant ⊢
  rw [trace]
  cases query with
  | inl query =>
    cases query with
    | inl coin => simpa [prefixFires, publicTraceAfter] using invariant
    | inr query =>
      cases query with
      | inl input => simp [prefixFires, publicTraceAfter, Bool.or_eq_true, invariant, or_comm]
      | inr input => simpa [prefixFires, publicTraceAfter] using invariant
  | inr raw => simpa [prefixFires, publicTraceAfter] using invariant

/-- Full adaptive execution retains the exact prefix-bit/public-trace relation. -/
theorem flaggedGame_prefix (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (result : Result × (ReceiveState × Bool))
    (supported : result ∈ support (flaggedGame false decode c key adversary)) :
    PrefixInvariant key result.2 := by
  exact OracleComp.simulateQ_run_preservesInv (flaggedImpl false decode c key) (PrefixInvariant key)
    (flaggedImpl_preserves_prefix decode c key) adversary (initialState, false)
    (by simp [PrefixInvariant, initialState, emptyCtxIndependentTagState]) result supported

/-- The prefix cost is a concrete event on the independent direct source transcript, not a new security premise. -/
theorem flaggedGame_bad_eq_public_prefix (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Pr[fun result => result.2.2 = true | flaggedGame false decode c key adversary] =
      Pr[fun result => ∃ input ∈ result.2.ctx.publicInputs, SecretPrefixQuery key input |
        independentGame decode c key adversary] := by
  change _ = Pr[fun result => ∃ input ∈ result.2.ctx.publicInputs, SecretPrefixQuery key input |
    (simulateQ (sourceImpl false decode c key) adversary).run initialState]
  rw [← flaggedGame_projection, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result supported
  exact flaggedGame_prefix decode c key adversary result supported

/-- Each public hash request contributes one trace entry, even when its digest is already cached. -/
theorem independentImpl_public_count (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : ReceiveState) (result : ReceiveSpec.Range query × ReceiveState)
    (supported : result ∈ support ((independentImpl decode c key query).run state)) :
    result.2.ctx.publicInputs.length = state.ctx.publicInputs.length +
      if AdaptiveCtxQueryBounds.SourceHash query then 1 else 0 := by
  rw [independentImpl_publicInputs decode c key query state result supported]
  cases query with
  | inl query =>
    cases query with
    | inl coin => rfl
    | inr query => cases query <;> simp [publicTraceAfter, AdaptiveCtxQueryBounds.SourceHash]
  | inr raw => rfl

/-- The complete adaptive public-query trace is bounded by the source hash budget, independently of raw attempts and seals. -/
theorem independentRun_public_count (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash count)
    (state : ReceiveState) (result : Result × ReceiveState)
    (supported : result ∈ support ((simulateQ (independentImpl decode c key) adversary).run state)) :
    result.2.ctx.publicInputs.length ≤ state.ctx.publicInputs.length + count := by
  induction adversary using OracleComp.inductionOn generalizing count state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, tail⟩ := supported
    have stepCount := independentImpl_public_count decode c key query state (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result tail
    by_cases isHash : AdaptiveCtxQueryBounds.SourceHash query
    · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr isHash)
      simp only [isHash, if_pos] at stepCount remaining
      omega
    · simp only [isHash, if_false] at stepCount remaining
      omega

/-- The bounded public prefix-probe vector tests precisely the actual source event. It does not create a key guess for a private cache lookup. -/
theorem independentGame_prefix_probe_iff (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash count)
    (result : Result × ReceiveState) (supported : result ∈ support (independentGame decode c key adversary)) :
    CtxNonceAeadIndDollar.CtxKeyProbeHit key
      (CtxNonceAeadIndDollar.ctxPrefixProbeVector count result.2.ctx.publicInputs) ↔
      ∃ input ∈ result.2.ctx.publicInputs, SecretPrefixQuery key input := by
  apply CtxNonceAeadIndDollar.ctxPrefixProbeVector_hit_iff_of_length_le
  simpa [initialState, emptyCtxIndependentTagState] using
    independentRun_public_count decode c key adversary count bounded initialState result supported

/-- The routed canonical-cache transcript keeps the one sampled key only for terminal analysis. -/
noncomputable def retainedRoutedGame (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × ReceiveState)) := do
  let key ← $ᵗ CtxKey
  let result ← splitGame decode c key adversary
  pure (key, result)

/-- A concrete key-dependent event on the complete direct source poststate. -/
def RetainedPrefix {Result : Type} (result : CtxKey × (Result × ReceiveState)) : Prop :=
  ∃ input ∈ result.2.2.ctx.publicInputs, SecretPrefixQuery result.1 input

/-- The adaptive prefix coupling preserves the sampled-key/transcript correlation, rather than replacing the key by an unrelated later sample. -/
theorem retainedRoutedGame_distance_le_prefix (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    tvDist (retainedRoutedGame decode c adversary)
      (AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary) ≤
      Pr[RetainedPrefix | AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary].toReal := by
  have convex := tvDist_bind_left_le ($ᵗ CtxKey)
    (fun key => (Prod.mk key) <$> splitGame decode c key adversary)
    (fun key => (Prod.mk key) <$> independentGame decode c key adversary)
  rw [tsum_fintype] at convex
  calc
    _ ≤ ∑ key : CtxKey, Pr[= key | ($ᵗ CtxKey)].toReal *
        (Pr[fun result => ∃ input ∈ result.2.ctx.publicInputs, SecretPrefixQuery key input |
          independentGame decode c key adversary]).toReal := by
      refine convex.trans (Finset.sum_le_sum fun key _ => ?_)
      have pointwise := canonicalGame_distance_le_prefix decode c key adversary
      rw [canonicalGame_split, flaggedGame_bad_eq_public_prefix] at pointwise
      exact mul_le_mul_of_nonneg_left ((tvDist_map_le (Prod.mk key) _ _).trans pointwise)
        ENNReal.toReal_nonneg
    _ = _ := by
      unfold AdaptiveCtxRetainedKey.retainedIndependentGame
      simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map]
      rw [tsum_fintype, ENNReal.toReal_sum]
      · simp only [Function.comp_def, RetainedPrefix, ENNReal.toReal_mul]
      · intro key _
        exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top

/-- Both structural adaptive hops now occur in the same retained-key source experiment. The prefix probability remains an event to reduce, not a primitive assumption. -/
theorem retainedRoutedGame_distance_le_prefix_add_intctxt (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    ENNReal.ofReal (tvDist (retainedRoutedGame decode c adversary)
      (AdaptiveCtxRetainedKey.sourceProjection <$>
        AdaptiveCtxRetainedKey.retainedLinkedGame false decode c adversary)) ≤
      Pr[RetainedPrefix | AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary] +
        ∑ index ∈ Finset.range count,
          CtxNonceAeadIntCtxt.modifiedNonceAeadINTCTXTAdvantage c
            (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) := by
  have triangle := tvDist_triangle (retainedRoutedGame decode c adversary)
    (AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary)
    (AdaptiveCtxRetainedKey.sourceProjection <$> AdaptiveCtxRetainedKey.retainedLinkedGame false decode c adversary)
  apply (ENNReal.ofReal_le_ofReal triangle).trans
  rw [ENNReal.ofReal_add (tvDist_nonneg _ _) (tvDist_nonneg _ _)]
  apply add_le_add
  · exact (ENNReal.ofReal_le_ofReal (retainedRoutedGame_distance_le_prefix decode c adversary)).trans_eq
      (ENNReal.ofReal_toReal probEvent_ne_top)
  · exact AdaptiveCtxRetainedKey.retainedIndependentGame_distance_le_intctxt_sum decode c fallback adversary count bounded

end BeaconcryptCore.Computational.AdaptiveCtxPrefix

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefix.flaggedImpl_agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefix.flaggedImpl_agree_good

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefix.flaggedGame_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefix.flaggedGame_prefix

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefix.independentGame_prefix_probe_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefix.independentGame_prefix_probe_iff

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefix.retainedRoutedGame_distance_le_prefix_add_intctxt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefix.retainedRoutedGame_distance_le_prefix_add_intctxt
