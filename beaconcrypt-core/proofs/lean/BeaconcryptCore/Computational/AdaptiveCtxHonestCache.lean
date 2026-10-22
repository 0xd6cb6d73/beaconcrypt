import BeaconcryptCore.Computational.AdaptiveCtxReplayTable
import BeaconcryptCore.Computational.JointTableFreshCandidates

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxHonestCache
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxReplayTable JointEagerTable CtxHonestTagSampling

/-- The direct honest-only comparison preserves ordinary full replay replies and address instrumentation, while evaluating private cells only for seal outputs. -/
noncomputable def honestNativeImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => match query with
  | .inl request => loggedImpl decode c key (.inl request) state
  | .inr raw => match decode raw with
    | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
    | some target =>
      let address := typedSuffix target.nonce target.context target.record.tag target.record.tagLength
      pure (replayPlaintext state.ctx target, ⟨state.ctx, state.rawAttempts + 1,
        address.toList :: state.privateInputs⟩)

/-- Honest-only cache provenance is justified only after raw private queries have been removed by the complete fixed-table simulation. -/
def HonestInvariant (c : Pqxdh.Crypto) (key : CtxKey) (state : AdaptiveCtxReceive.ReceiveState) : Prop :=
  LoggedInvariant c key state ∧ CtxIndependentTagStateSuffixCacheProvenance state.ctx

/-- Each direct comparison step preserves actual honest commitment values, nonce uniqueness, ordinary seal correctness and provenance of its honest-only private cache. -/
theorem honestNative_preserves (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (honestNativeImpl decode c key) (HonestInvariant c key) := by
  intro query state invariant result supported
  cases query with
  | inr raw =>
    cases parsed : decode raw with
    | none =>
      simp only [honestNativeImpl, StateT.run, parsed, mem_support_pure_iff] at supported
      subst result
      exact invariant
    | some target =>
      simp only [honestNativeImpl, StateT.run, parsed, mem_support_pure_iff] at supported
      subst result
      exact invariant
  | inl request =>
    have logged := loggedImpl_preserves_invariant decode c key (.inl request) state invariant.1 result supported
    refine ⟨logged, ?_⟩
    cases request with
    | inl coin =>
      change result ∈ support ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)) at supported
      obtain ⟨value, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      exact invariant.2
    | inr operation =>
      change result ∈ support (independentCtx c key operation state) at supported
      unfold independentCtx at supported
      obtain ⟨ctxResult, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      have old : CtxIndependentTagStateInvariant state.ctx :=
        ⟨invariant.1.2.1, invariant.1.2.2.1, invariant.2⟩
      rw [ctxIndependentTagImpl_eq_directSample_step_of_invariant c key operation state.ctx old] at step
      exact (ctxDirectSampleIndependentTagImpl_preserves_invariant c key operation state.ctx old ctxResult step).2.2

/-- The exact fresh source state satisfies the comparison invariant without any new cryptographic premise. -/
theorem honest_initial (c : Pqxdh.Crypto) (key : CtxKey) :
    HonestInvariant c key AdaptiveCtxReceive.initialState := by
  refine ⟨initial_invariant c key, ?_⟩
  exact emptyCtxIndependentTagState_invariant.2.2

/-- Link only the honest-output dictionary client to the same actual mixed lazy interpreter. -/
noncomputable def honestLinked (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT DictionaryState ProbComp) :=
  QueryImpl.Stateful.link (honestOnlyImpl decode c key) lazyDictionary

/-- This linked state contains the complete comparison source state and its duplicate actual honest-output dictionary. -/
theorem honestLinked_run (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache) :
    (honestLinked decode c key query).run (state, dictionary) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ lazyDictionary ((honestOnlyImpl decode c key query).run state)).run dictionary := rfl

/-- Actual honest-only dictionary execution projects to the exact comparison query and full source state. -/
theorem honestLinked_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : DictionaryState) (aligned : SourceDictionaryAligned state) :
    Prod.map id Prod.fst <$> (honestLinked decode c key query).run state =
      (honestNativeImpl decode c key query).run state.1 := by
  rcases state with ⟨state, dictionary⟩
  cases query with
  | inl request =>
    cases request with
    | inl coin => exact dictionaryLinked_projection decode c key (.inl (.inl coin)) (state, dictionary) aligned
    | inr operation =>
      cases operation <;> exact dictionaryLinked_projection decode c key _ (state, dictionary) aligned
  | inr raw =>
    rw [honestLinked_run]
    cases parsed : decode raw <;>
      simp [honestOnlyImpl, honestOnlyRaw, honestNativeImpl, StateT.run, parsed] <;> rfl

/-- Removing raw private queries preserves external/source dictionary alignment: those raw calls change only their counter and retained address history. -/
theorem honestLinked_preserves (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (honestLinked decode c key) SourceDictionaryAligned := by
  rintro query ⟨state, dictionary⟩ aligned result supported
  cases query with
  | inl request =>
    cases request with
    | inl coin => exact dictionaryLinked_preserves decode c key (.inl (.inl coin)) (state, dictionary) aligned result supported
    | inr operation =>
      cases operation <;> exact dictionaryLinked_preserves decode c key _ (state, dictionary) aligned result supported
  | inr raw =>
    rw [honestLinked_run] at supported
    cases parsed : decode raw <;>
      simp only [honestOnlyImpl, StateT.run, honestOnlyRaw, parsed] at supported <;>
      subst result <;> exact aligned

/-- The complete adaptive honest-only mixed client projects to its actual direct comparison source. -/
theorem honestRun_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary) :
    Prod.fst <$> (simulateQ lazyDictionary
      ((simulateQ (honestOnlyImpl decode c key) adversary).run state)).run dictionary =
      (simulateQ (honestNativeImpl decode c key) adversary).run state := by
  have related := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (honestLinked decode c key) (honestNativeImpl decode c key) SourceDictionaryAligned Prod.fst
    (honestLinked_preserves decode c key) (honestLinked_projection decode c key)
    adversary (state, dictionary) aligned
  unfold honestLinked at related
  rw [QueryImpl.Stateful.simulateQ_link_run] at related
  simpa only [Functor.map_map, Function.comp_def, QueryImpl.Stateful.Frame.prod,
    QueryImpl.Stateful.Frame.linkReshape, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
    PFunctor.Lens.State.mk_put, Prod.map, id_eq] using related

/-- The duplicate honest-only dictionary remains the exact restriction of its complete source cache. -/
theorem honestRun_dictionary (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary)
    (result : (Result × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ lazyDictionary
      ((simulateQ (honestOnlyImpl decode c key) adversary).run state)).run dictionary)) :
    result.2 = sourceDictionary result.1.2 := by
  have linkedSupport : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (honestLinked decode c key) adversary).run (state, dictionary)) := by
    unfold honestLinked
    rw [QueryImpl.Stateful.simulateQ_link_run, support_map]
    exact ⟨result, supported, rfl⟩
  have kept := OracleComp.simulateQ_run_preservesInv (honestLinked decode c key)
    SourceDictionaryAligned (honestLinked_preserves decode c key) adversary
    (state, dictionary) aligned (result.1.1, (result.1.2, result.2)) linkedSupport
  exact aligned_dictionary_eq result.1.2 result.2 kept

/-- Every actual honest-only final dictionary agrees with the complete comparison state and has proved honest suffix provenance; rejected raw requests have not been silently placed in that dictionary. -/
theorem honestClient_cache_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (result : (Result × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ mixedLazyImpl
      (honestClient decode c key adversary)).run ∅)) :
    result.2 = sourceDictionary result.1.2 ∧ HonestInvariant c key result.1.2 := by
  rw [← lazyDictionary_eq_mixed] at supported
  have aligned := honestRun_dictionary decode c key adversary AdaptiveCtxReceive.initialState ∅
    initial_dictionary_aligned result supported
  refine ⟨aligned, ?_⟩
  have projected : result.1 ∈ support ((simulateQ (honestNativeImpl decode c key) adversary).run
      AdaptiveCtxReceive.initialState) := by
    rw [← honestRun_projection decode c key adversary AdaptiveCtxReceive.initialState ∅ initial_dictionary_aligned,
      support_map]
    exact ⟨result, supported, rfl⟩
  exact OracleComp.simulateQ_run_preservesInv (honestNativeImpl decode c key) (HonestInvariant c key)
    (honestNative_preserves decode c key) adversary AdaptiveCtxReceive.initialState
    (honest_initial c key) result.1 projected

/-- A successful fresh full-tuple guess on a retained base ciphertext must address an absent honest-only cell. Cache hits contradict actual honest commitments and per-key nonce uniqueness. -/
theorem freshGuess_address_absent (c : Pqxdh.Crypto) (key : CtxKey)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (invariant : HonestInvariant c key state) (aligned : dictionary = sourceDictionary state)
    (target : CtxUnclaimedAcceptance.Target) (tail : Suffix → CtxDigest)
    (fresh : replayPlaintext state.ctx target = none)
    (baseHit : AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target) ≠ none)
    (guessed : target.record.commit = tableExtending dictionary tail
      (typedSuffix target.nonce target.context target.record.tag target.record.tagLength)) :
    dictionary (typedSuffix target.nonce target.context target.record.tag target.record.tagLength) = none := by
  cases cached : dictionary (typedSuffix target.nonce target.context target.record.tag target.record.tagLength) with
  | none => rfl
  | some digest =>
    have sourceCached : state.ctx.cache.suffixCache
        (outerSuffix target.nonce target.context target.record.tag) = some digest := by
      simpa only [aligned, sourceDictionary, QueryCache.toFn_ofFn, typedSuffix, List.Vector.toList] using cached
    have commit : target.record.commit = digest := by
      simpa only [tableExtending, cached, Option.getD_some] using guessed
    have lookup : (digest, state.ctx.cache) ∈ support
        (ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache) := by
      simp only [ctxKeyFreeSuffixStep, sourceCached, mem_support_pure_iff]
    have hasAlias := loggedFresh_is_alias key state.ctx target digest state.ctx.cache invariant.1.1
      ((replayPlaintext_none_iff state.ctx target).mp fresh) commit baseHit lookup
    have excluded := alias_excludes_honestSuffix key state.ctx target invariant.1.2.2.1 hasAlias
    have present : state.ctx.cache.suffixCache (outerSuffix target.nonce target.context target.record.tag) ≠ none := by
      rw [sourceCached]
      intro impossible
      cases impossible
    obtain ⟨honest, member, sameSuffix⟩ := invariant.2 _ present
    exact False.elim (excluded honest member sameSuffix)

/-- Eligibility is tested from the actual successful public seal history: no full CTX replay and an unchanged previously issued base tuple. -/
def Eligible (state : AdaptiveCtxReceive.ReceiveState) (target : CtxUnclaimedAcceptance.Target) : Prop :=
  replayPlaintext state.ctx target = none ∧
    AdaptiveRawNonceAead.loggedPlaintext (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals
      (baseTarget target) ≠ none

instance (state : AdaptiveCtxReceive.ReceiveState) (target : CtxUnclaimedAcceptance.Target) :
    Decidable (Eligible state target) := inferInstanceAs (Decidable (_ ∧ _))

/-- Ineligible or malformed slots remain explicit `none` candidates. Candidate selection reads no private table or restored private cache. -/
def candidate (state : AdaptiveCtxReceive.ReceiveState) : Option CtxUnclaimedAcceptance.Target → Option (Suffix × CtxDigest)
  | none => none
  | some target => if Eligible state target then
      some (typedSuffix target.nonce target.context target.record.tag target.record.tagLength, target.record.commit)
    else none

/-- A selected vector retains every slot and every repeated guess; only its public-history eligibility test can replace a slot by none. -/
def candidates {Result : Type} {bound : ℕ}
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (result : Result × AdaptiveCtxReceive.ReceiveState) : List.Vector (Option (Suffix × CtxDigest)) bound :=
  (selector result.1).map (candidate result.2)

/-- The final guessing event uses the unchanged selected commitment and the SAME retained private table, with actual full-tuple freshness. -/
def GuessEvent {Result : Type} {bound : ℕ}
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (terminal : (Suffix → CtxDigest) × (Result × AdaptiveCtxReceive.ReceiveState)) : Prop :=
  ∃ index : Fin bound, ∃ target,
    (selector terminal.2.1).get index = some target ∧ Eligible terminal.2.2 target ∧
      target.record.commit = terminal.1 (typedSuffix target.nonce target.context target.record.tag target.record.tagLength)

/-- Full source reconstruction changes only the private cache; final public-history eligibility and the unchanged selected guess are preserved exactly. -/
theorem GuessEvent_restore {Result : Type} {bound : ℕ}
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (terminal : (Suffix → CtxDigest) × (Result × AdaptiveCtxReceive.ReceiveState)) :
    GuessEvent selector (restoreTerminal terminal) ↔ GuessEvent selector terminal := Iff.rfl

/-- Every successful eligible vector slot is a proved final honest-cache miss, so it satisfies the ordinary independent-tail fresh-guess event without an assumed source freshness interface. -/
theorem guessEvent_implies_freshHit {Result : Type} {bound : ℕ} (c : Pqxdh.Crypto) (key : CtxKey)
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (result : (Result × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (invariant : HonestInvariant c key result.1.2) (aligned : result.2 = sourceDictionary result.1.2)
    (tail : Suffix → CtxDigest) (won : GuessEvent selector (tableExtending result.2 tail, result.1)) :
    ∃ index : Fin bound, JointTableFreshCandidates.FreshHit result.2 (tableExtending result.2 tail)
      ((candidates selector result.1).get index) := by
  obtain ⟨index, target, selected, eligible, guessed⟩ := won
  have absent := freshGuess_address_absent c key result.1.2 result.2 invariant aligned target tail
    eligible.1 eligible.2 guessed
  refine ⟨index, ?_⟩
  simp only [candidates, List.Vector.get_map, selected, candidate, ite_eq_left eligible,
    JointTableFreshCandidates.FreshHit]
  exact ⟨absent, guessed.symm⟩

/-- After every adaptive honest-only dictionary execution, a vector of unchanged final eligible guesses costs at most one independent 512-bit cell per slot. All repetitions and omitted slots remain counted. -/
theorem honestCompletion_guess_bound {Result : Type} {bound : ℕ} (decode : RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound) :
    Pr{let x ← mixedCompletedLazy (honestClient decode c key adversary) ∅}[GuessEvent selector x] ≤
      (bound : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  unfold mixedCompletedLazy
  generalize sampled : ($ᵗ (Suffix → CtxDigest) : ProbComp (Suffix → CtxDigest)) = sample
  have step : ∀ {X Q T Y : Type} (run : ProbComp (X × Q)) (draw : ProbComp T) (extend : Q → T → Y)
      (event : Y × X → Prop) (ε : ℝ≥0∞),
      (∀ result ∈ support run, Pr{let tail ← draw}[event (extend result.2 tail, result.1)] ≤ ε) →
      Pr{let x ← run >>= fun result => draw >>= fun tail => pure (extend result.2 tail, result.1)}[event x] ≤
        ε := by
    intro X Q T Y run draw extend event ε bound
    refine prEvent_bind_le_of_forall_le_of_support run _ event fun result supported => ?_
    rw [bind_pure_comp _ draw, prEvent_map]
    exact bound result supported
  have mono : ∀ {T C X E : Type} {n : ℕ} (draw : ProbComp T) (extend : C → T → T) (cache : C) (res : X)
      (event : T × X → Prop) (fresh : C → T → E → Prop) (cands : List.Vector E n),
      (∀ tail ∈ support draw, event (extend cache tail, res) →
        ∃ index : Fin n, fresh cache (extend cache tail) (cands.get index)) →
      Pr{let tail ← draw}[event (extend cache tail, res)] ≤
        Pr{let tail ← draw}[∃ index : Fin n, fresh cache (extend cache tail) (cands.get index)] :=
    fun draw _ _ _ _ _ _ implied => prEvent_mono_of_support draw _ _ implied
  refine step _ sample tableExtending (GuessEvent selector) _ fun result supported => ?_
  obtain ⟨aligned, invariant⟩ := honestClient_cache_invariant decode c key adversary result supported
  calc
    _ ≤ Pr{let tail ← sample}[∃ index : Fin bound,
        JointTableFreshCandidates.FreshHit result.2 (tableExtending result.2 tail)
          ((candidates selector result.1).get index)] :=
      mono sample tableExtending result.2 result.1 (GuessEvent selector) JointTableFreshCandidates.FreshHit
        (candidates selector result.1) fun tail _ won =>
          guessEvent_implies_freshHit c key selector result invariant aligned tail won
    _ ≤ (bound : ℝ≥0∞) * (Nat.card CtxDigest : ℝ≥0∞)⁻¹ := by
      subst sampled
      let : MeasurableSpace CtxDigest := ⊤
      let : DiscreteMeasurableSpace CtxDigest := ⟨fun _ => by simp⟩
      exact JointTableFreshCandidates.fixed_vector_bound result.2 (candidates selector result.1)
    _ = _ := by rw [Nat.card_eq_fintype_card, ctxDigest_card, div_eq_mul_inv]

/-- The actual replay-only source, including every earlier rejected private lookup and complete cache, obeys the same final-vector bound through the checked SAME-table reconstruction. No public-HKDF table or extra primitive security premise is used. -/
theorem completedSource_guess_bound {Result : Type} {bound : ℕ} (decode : RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound) :
    Pr{let x ← completedSource decode c key adversary AdaptiveCtxReceive.initialState}[GuessEvent selector x] ≤
      (bound : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  rw [(completedSource_eq_honestCompletion decode c key adversary).prEvent_eq (GuessEvent selector),
    prEvent_map]
  exact honestCompletion_guess_bound decode c key adversary selector

end BeaconcryptCore.Computational.AdaptiveCtxHonestCache

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestNative_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestNative_preserves

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestClient_cache_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestClient_cache_invariant

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.freshGuess_address_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.freshGuess_address_absent

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.guessEvent_implies_freshHit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.guessEvent_implies_freshHit

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestCompletion_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.honestCompletion_guess_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxHonestCache.completedSource_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxHonestCache.completedSource_guess_bound
