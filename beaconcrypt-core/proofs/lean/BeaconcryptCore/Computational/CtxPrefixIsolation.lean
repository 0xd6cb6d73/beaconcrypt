import BeaconcryptCore.Computational.CtxRomAuth
import VCVio.ProgramLogic.Relational.SimulateQ

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxPrefixIsolation

open CtxRomAuth

/-- The public query exposes the hidden 32-byte key prefix. -/
def SecretPrefixQuery (key : CtxKey) (input : Pqxdh.Bytes) : Prop :=
  input.take 32 = key.toList

instance (key : CtxKey) : DecidablePred (SecretPrefixQuery key) :=
  fun input => by
    unfold SecretPrefixQuery
    infer_instance

/-- Every exact modified-CTX outer input exposes the key under `take 32`. -/
theorem secretPrefixQuery_outerInput (key : CtxKey) (nonce : CtxNonce)
    (context : CtxRecordContext) (tag : Pqxdh.Bytes) :
    SecretPrefixQuery key (outerInput key nonce context tag) := by
  simp [SecretPrefixQuery, outerInput, Pqxdh.ctxPreimage,
    key.toList_length]

/-- Add a sticky output bad flag to any stateful step. -/
def withStickyBad {m : Type → Type} [Monad m] {α σ : Type}
    (fires : Bool) (step : StateT σ m α) : StateT (σ × Bool) m α :=
  fun state => do
    let (output, state') ← step.run state.1
    pure (output, state', state.2 || fires)

/-- Dropping the sticky flag recovers the underlying stateful step exactly. -/
theorem withStickyBad_fst_map_run {m : Type → Type} [Monad m] [LawfulMonad m]
    {α σ : Type} (fires : Bool) (step : StateT σ m α)
    (state : σ × Bool) :
    Prod.map id Prod.fst <$> (withStickyBad fires step).run state =
      step.run state.1 := by
  rcases state with ⟨state, bad⟩
  change Prod.map id Prod.fst <$> (step.run state >>= fun intermediate =>
    pure (intermediate.1, intermediate.2, bad || fires)) = step.run state
  simp

/-- A sticky wrapper never clears a fired flag. -/
theorem withStickyBad_mono {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] {α σ : Type}
    (fires : Bool) (step : StateT σ m α)
    (state : σ × Bool) (hbad : state.2 = true)
    (result : α × (σ × Bool))
    (hresult : result ∈ support ((withStickyBad fires step).run state)) :
    result.2.2 = true := by
  rcases state with ⟨state, bad⟩
  simp only at hbad
  subst bad
  change result ∈ support (step.run state >>= fun intermediate =>
    pure (intermediate.1, intermediate.2, true || fires)) at hresult
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hresult
  obtain ⟨intermediate, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  simpa using congrArg (fun p => p.2.2) hresult

/-- A firing sticky wrapper sets bad on every supported result. -/
theorem withStickyBad_true {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] {α σ : Type}
    (step : StateT σ m α)
    (state : σ × Bool) (result : α × (σ × Bool))
    (hresult : result ∈ support ((withStickyBad true step).run state)) :
    result.2.2 = true := by
  rcases state with ⟨state, bad⟩
  change result ∈ support (step.run state >>= fun intermediate =>
    pure (intermediate.1, intermediate.2, bad || true)) at hresult
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hresult
  obtain ⟨intermediate, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  simpa using congrArg (fun p => p.2.2) hresult

/-- Prefix-query branch of the prefix-isolated game.

It samples independently instead of reading the shared cache, then records the public input in the exact current handler state.
The branch is observable only once prefix-bad has fired. -/
noncomputable def ctxPrefixIsolatedPublic (query : CtxRO.Domain) :
    StateT CtxHandlerState ProbComp CtxDigest := fun state => do
  let digest ← $ᵗ CtxDigest
  let cache := state.cache.cacheQuery query digest
  pure (digest, state.addPublic query.2 cache)

/-- The exact current real handler with an explicit public-prefix bad flag. -/
noncomputable def ctxRealWithPrefixFlagImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT (CtxHandlerState × Bool) ProbComp) :=
  fun query => match query with
  | .inl input =>
      withStickyBad (decide (SecretPrefixQuery key input.2))
        (ctxPublicOracle input)
  | .inr input => withStickyBad false (ctxSealOracle c key input)

/-- Prefix-isolated handler: the only changed transition is a public secret-prefix query. -/
noncomputable def ctxPrefixIsolatedImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT (CtxHandlerState × Bool) ProbComp) :=
  fun query => match query with
  | .inl input =>
      if SecretPrefixQuery key input.2 then
        withStickyBad true (ctxPrefixIsolatedPublic input)
      else
        withStickyBad false (ctxPublicOracle input)
  | .inr input => withStickyBad false (ctxSealOracle c key input)

/-- Dropping the flag from one real step gives the tracked `ctxAdversaryImpl` step. -/
theorem ctxRealWithPrefixFlagImpl_proj_step (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxHandlerState × Bool) :
    Prod.map id Prod.fst <$>
        (ctxRealWithPrefixFlagImpl c key query).run state =
      (ctxAdversaryImpl c key query).run state.1 := by
  rcases query with query | input
  · exact withStickyBad_fst_map_run _ _ state
  · exact withStickyBad_fst_map_run _ _ state

/-- Dropping the flag from the full real run gives the tracked generated run exactly. -/
theorem ctxRealWithPrefixFlagImpl_proj_run (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : CtxAdversary) :
    Prod.map id Prod.fst <$>
        (simulateQ (ctxRealWithPrefixFlagImpl c key) adversary.main).run
          (emptyCtxHandlerState, false) =
      (simulateQ (ctxAdversaryImpl c key) adversary.main).run
        emptyCtxHandlerState := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxRealWithPrefixFlagImpl c key) (ctxAdversaryImpl c key) Prod.fst
    (ctxRealWithPrefixFlagImpl_proj_step c key) adversary.main
    (emptyCtxHandlerState, false)

/-- The two handlers agree on every output transition that remains non-bad. -/
theorem ctxReal_prefixIsolated_agree_good (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxHandlerState)
    (output : CtxAdversarySpec.Range query) (state' : CtxHandlerState) :
    Pr[= (output, (state', false)) |
        (ctxRealWithPrefixFlagImpl c key query).run (state, false)] =
      Pr[= (output, (state', false)) |
        (ctxPrefixIsolatedImpl c key query).run (state, false)] := by
  rcases query with query | input
  · by_cases hprefix : SecretPrefixQuery key query.2
    · rw [probOutput_eq_zero_of_not_mem_support,
        probOutput_eq_zero_of_not_mem_support]
      · intro hsupport
        let step : StateT CtxHandlerState ProbComp
            (CtxAdversarySpec.Range (.inl query)) :=
          ctxPrefixIsolatedPublic query
        have hsupport' : (output, (state', false)) ∈
            support ((withStickyBad true step).run (state, false)) := by
          simpa [ctxPrefixIsolatedImpl, hprefix, step] using hsupport
        have htrue := withStickyBad_true step
          (state, false) (output, state', false) hsupport'
        simp at htrue
      · intro hsupport
        let step : StateT CtxHandlerState ProbComp
            (CtxAdversarySpec.Range (.inl query)) := ctxPublicOracle query
        have hsupport' : (output, (state', false)) ∈
            support ((withStickyBad true step).run (state, false)) := by
          simpa [ctxRealWithPrefixFlagImpl, hprefix, step] using hsupport
        have htrue := withStickyBad_true step
          (state, false) (output, state', false) hsupport'
        simp at htrue
    · simp [ctxRealWithPrefixFlagImpl, ctxPrefixIsolatedImpl, hprefix]
  · rfl

/-- The flagged real handler never clears bad. -/
theorem ctxRealWithPrefixFlagImpl_bad_mono (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxHandlerState × Bool)
    (hbad : state.2 = true)
    (result : CtxAdversarySpec.Range query × (CtxHandlerState × Bool))
    (hresult : result ∈ support
      ((ctxRealWithPrefixFlagImpl c key query).run state)) :
    result.2.2 = true := by
  rcases query with query | input
  · exact withStickyBad_mono _ _ state hbad result hresult
  · exact withStickyBad_mono _ _ state hbad result hresult

/-- The prefix-isolated handler never clears bad. -/
theorem ctxPrefixIsolatedImpl_bad_mono (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxHandlerState × Bool)
    (hbad : state.2 = true)
    (result : CtxAdversarySpec.Range query × (CtxHandlerState × Bool))
    (hresult : result ∈ support ((ctxPrefixIsolatedImpl c key query).run state)) :
    result.2.2 = true := by
  rcases query with query | input
  · by_cases hprefix : SecretPrefixQuery key query.2
    · exact withStickyBad_mono _ _ state hbad result
        (by simpa [ctxPrefixIsolatedImpl, hprefix] using hresult)
    · exact withStickyBad_mono _ _ state hbad result
        (by simpa [ctxPrefixIsolatedImpl, hprefix] using hresult)
  · exact withStickyBad_mono _ _ state hbad result hresult

/-- Supported sticky-wrapper results have the wrapper's explicit post-state shape. -/
theorem withStickyBad_result_state {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] {α σ : Type}
    (fires : Bool) (step : StateT σ m α) (state : σ × Bool)
    (result : α × (σ × Bool))
    (hresult : result ∈ support ((withStickyBad fires step).run state)) :
    ∃ intermediate ∈ support (step.run state.1),
      result = (intermediate.1, intermediate.2, state.2 || fires) := by
  rcases state with ⟨state, bad⟩
  change result ∈ support (step.run state >>= fun intermediate =>
    pure (intermediate.1, intermediate.2, bad || fires)) at hresult
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hresult
  obtain ⟨intermediate, hintermediate, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  exact ⟨intermediate, hintermediate, hresult⟩

/-- A public step records exactly its current byte-string query at the list head. -/
theorem ctxPublicOracle_publicInputs (query : CtxRO.Domain)
    (state : CtxHandlerState) (result : CtxDigest × CtxHandlerState)
    (hresult : result ∈ support ((ctxPublicOracle query).run state)) :
    result.2.publicInputs = query.2 :: state.publicInputs := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache >>= fun oracleResult =>
      pure (oracleResult.1, state.addPublic query.2 oracleResult.2)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rfl

/-- A sealing step never changes the public-query history. -/
theorem ctxSealOracle_publicInputs (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxHandlerState)
    (result : Option CtxRomRecord × CtxHandlerState)
    (hresult : result ∈ support ((ctxSealOracle c key input).run state)) :
    result.2.publicInputs = state.publicInputs := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · change result ∈ support
      (if input.nonce ∈ state.usedNonces then pure (none, state) else _) at hresult
    rw [if_pos hused, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    rfl
  · let base := c.aeadSeal key.toList input.nonce.toList
      input.context.ad.bytes input.plaintext
    let query : CtxRO.Domain :=
      ((), outerInput key input.nonce input.context base.2)
    change result ∈ support
      (if input.nonce ∈ state.usedNonces then pure (none, state) else
        (ctxRandomOracle query).run state.cache >>= fun oracleResult =>
          let record : CtxRomRecord :=
            ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, oracleResult.1⟩
          pure (some record,
            state.addSeal ⟨input, record⟩ oracleResult.2)) at hresult
    rw [if_neg hused, mem_support_bind_iff] at hresult
    obtain ⟨oracleResult, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    rfl

/-- The sticky bit is exact: it is set iff a recorded public input exposes the key prefix. -/
def CtxPrefixFlagInvariant (key : CtxKey)
    (state : CtxHandlerState × Bool) : Prop :=
  state.2 = true ↔
    ∃ input ∈ state.1.publicInputs, SecretPrefixQuery key input

@[simp] theorem emptyCtxPrefixFlagInvariant (key : CtxKey) :
    CtxPrefixFlagInvariant key (emptyCtxHandlerState, false) := by
  simp [CtxPrefixFlagInvariant, emptyCtxHandlerState]

/-- Every exact real query step preserves exactness of the recorded prefix flag. -/
theorem ctxRealWithPrefixFlagImpl_preserves_prefix_flag
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (ctxRealWithPrefixFlagImpl c key)
      (CtxPrefixFlagInvariant key) := by
  intro query state hinvariant result hresult
  cases query with
  | inl publicQuery =>
      obtain ⟨intermediate, hintermediate, rfl⟩ :=
        withStickyBad_result_state
          (decide (SecretPrefixQuery key publicQuery.2))
          (ctxPublicOracle publicQuery) state result hresult
      have hpublic := ctxPublicOracle_publicInputs publicQuery state.1
        intermediate hintermediate
      unfold CtxPrefixFlagInvariant at hinvariant ⊢
      rw [hpublic]
      simp only [List.mem_cons, exists_eq_or_imp]
      simp [Bool.or_eq_true, hinvariant, or_comm]
  | inr sealInput =>
      obtain ⟨intermediate, hintermediate, rfl⟩ :=
        withStickyBad_result_state false (ctxSealOracle c key sealInput)
          state result hresult
      have hpublic := ctxSealOracle_publicInputs c key sealInput state.1
        intermediate hintermediate
      unfold CtxPrefixFlagInvariant at hinvariant ⊢
      rw [hpublic]
      simpa using hinvariant

/-- Convert the exact current handler state into the tracked pre-verification view. -/
def handlerStateToBeforeVerify (key : CtxKey) (target : CtxAliasTarget)
    (state : CtxHandlerState) : CtxBeforeVerify :=
  ⟨key, target, state.successfulSeals, state.usedNonces, state.publicInputs⟩

/-- The tracked alias predicate is definitionally recovered from handler state. -/
theorem fullAliasShape_toBeforeVerify (key : CtxKey) (target : CtxAliasTarget)
    (state : CtxHandlerState) :
    CtxFullAliasShape (handlerStateToBeforeVerify key target state) ↔
      (∀ entry ∈ state.successfulSeals,
          ¬ target.sameFullTupleAsSuccessfulSeal entry) ∧
        ∃ entry ∈ state.successfulSeals,
          target.matchesSuccessfulSeal entry := by
  rfl

/-- Public-prefix bad in the tracked view is definitionally the public-input event used here. -/
theorem secretPrefixQueried_toBeforeVerify (key : CtxKey)
    (target : CtxAliasTarget) (state : CtxHandlerState) :
    CtxSecretPrefixQueried (handlerStateToBeforeVerify key target state) ↔
      ∃ input ∈ state.publicInputs, SecretPrefixQuery key input := by
  rfl

/-- Projection from an unflagged handler result to the tracked result-and-cache shape. -/
def trackedProjection (key : CtxKey)
    (result : CtxAliasTarget × CtxHandlerState) :
    CtxBeforeVerify × CtxRO.QueryCache :=
  (handlerStateToBeforeVerify key result.1 result.2, result.2.cache)

/-- The fixed-key flagged real transcript. -/
noncomputable def ctxRealWithPrefixFlagBeforeVerify (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : CtxAdversary) :
    ProbComp (CtxAliasTarget × (CtxHandlerState × Bool)) :=
  (simulateQ (ctxRealWithPrefixFlagImpl c key) adversary.main).run
    (emptyCtxHandlerState, false)

/-- The fixed-key flagged prefix-isolated transcript. -/
noncomputable def ctxPrefixIsolatedFlaggedBeforeVerify (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : CtxAdversary) :
    ProbComp (CtxAliasTarget × (CtxHandlerState × Bool)) :=
  (simulateQ (ctxPrefixIsolatedImpl c key) adversary.main).run
    (emptyCtxHandlerState, false)

/-- The exact prefix-flag invariant holds after every adaptive real execution. -/
theorem ctxRealWithPrefixFlag_run_prefix_flag
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × (CtxHandlerState × Bool))
    (hresult : result ∈ support
      (ctxRealWithPrefixFlagBeforeVerify c key adversary)) :
    CtxPrefixFlagInvariant key result.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (ctxRealWithPrefixFlagImpl c key) (CtxPrefixFlagInvariant key)
    (ctxRealWithPrefixFlagImpl_preserves_prefix_flag c key)
    adversary.main (emptyCtxHandlerState, false)
    (emptyCtxPrefixFlagInvariant key) result hresult

/-- Mapping away the real flag recovers the tracked fixed-key game exactly. -/
theorem trackedProjection_realWithPrefixFlag_eq_ctxBeforeVerifyInner
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    (fun result => trackedProjection key (result.1, result.2.1)) <$>
        ctxRealWithPrefixFlagBeforeVerify c key adversary =
      ctxBeforeVerifyInner c adversary key := by
  let realRun :=
    (simulateQ (ctxRealWithPrefixFlagImpl c key) adversary.main).run
      (emptyCtxHandlerState, false)
  let currentRun :=
    (simulateQ (ctxAdversaryImpl c key) adversary.main).run
      emptyCtxHandlerState
  have hdrop : Prod.map id Prod.fst <$> realRun = currentRun := by
    simpa [realRun, currentRun] using
      ctxRealWithPrefixFlagImpl_proj_run c key adversary
  have hlhs :
      (fun result => trackedProjection key (result.1, result.2.1)) <$> realRun =
        trackedProjection key <$> (Prod.map id Prod.fst <$> realRun) := by
    rw [Functor.map_map]
    rfl
  have hrhs :
      ctxBeforeVerifyInner c adversary key =
        trackedProjection key <$> currentRun := by
    rfl
  calc
    (fun result => trackedProjection key (result.1, result.2.1)) <$>
          ctxRealWithPrefixFlagBeforeVerify c key adversary =
        (fun result => trackedProjection key (result.1, result.2.1)) <$>
          realRun := by rfl
    _ = trackedProjection key <$> (Prod.map id Prod.fst <$> realRun) := hlhs
    _ = trackedProjection key <$> currentRun := by rw [hdrop]
    _ = ctxBeforeVerifyInner c adversary key := hrhs.symm

/-- Fixed-key probability of a public hidden-key-prefix query. -/
noncomputable def ctxPrefixBadProbability (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : CtxAdversary) : ℝ≥0∞ :=
  Pr[fun result => result.2.2 = true |
    ctxRealWithPrefixFlagBeforeVerify c key adversary]

/-- Fixed-key form of the tracked public hidden-key-prefix probability. -/
noncomputable def ctxSecretPrefixQueriedProbabilityInner
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) : ℝ≥0∞ :=
  Pr[fun result => CtxSecretPrefixQueried result.1 |
    ctxBeforeVerifyInner c adversary key]

/-- The auxiliary sticky-bit probability is exactly the tracked fixed-key prefix event. -/
theorem ctxPrefixBadProbability_eq_secretPrefixQueriedProbabilityInner
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ctxPrefixBadProbability c key adversary =
      ctxSecretPrefixQueriedProbabilityInner c key adversary := by
  unfold ctxPrefixBadProbability ctxSecretPrefixQueriedProbabilityInner
  rw [← trackedProjection_realWithPrefixFlag_eq_ctxBeforeVerifyInner,
    probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  have hinvariant := ctxRealWithPrefixFlag_run_prefix_flag
    c key adversary result hresult
  have hnormalize := secretPrefixQueried_toBeforeVerify key result.1 result.2.1
  exact hinvariant.trans hnormalize.symm

/-- The current real game and the prefix-isolated game are identical until a public prefix query. -/
theorem tvDist_ctxReal_prefixIsolated_le_prefixBad
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxRealWithPrefixFlagBeforeVerify c key adversary)
        (ctxPrefixIsolatedFlaggedBeforeVerify c key adversary) ≤
      (ctxPrefixBadProbability c key adversary).toReal := by
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (ctxRealWithPrefixFlagImpl c key) (ctxPrefixIsolatedImpl c key)
    adversary.main emptyCtxHandlerState (ctxReal_prefixIsolated_agree_good c key)
    (ctxRealWithPrefixFlagImpl_bad_mono c key)
    (ctxPrefixIsolatedImpl_bad_mono c key)

/-- Fixed-key fundamental lemma stated directly with the tracked prefix-query event. -/
theorem tvDist_ctxReal_prefixIsolated_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxRealWithPrefixFlagBeforeVerify c key adversary)
        (ctxPrefixIsolatedFlaggedBeforeVerify c key adversary) ≤
      (ctxSecretPrefixQueriedProbabilityInner c key adversary).toReal := by
  rw [← ctxPrefixBadProbability_eq_secretPrefixQueriedProbabilityInner]
  exact tvDist_ctxReal_prefixIsolated_le_prefixBad c key adversary

/-- Fixed-key prefix-isolated transcript on the canonical pre-verification surface.

The projection deliberately retains the target, successful seals, nonce history, public inputs, and the resulting ROM cache so that all existing final-verifier continuations remain applicable. -/
noncomputable def ctxPrefixIsolatedBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × CtxRO.QueryCache) :=
  (fun result => trackedProjection key (result.1, result.2.1)) <$>
    ctxPrefixIsolatedFlaggedBeforeVerify c key adversary

/-- Fixed-key prefix isolation on exactly the tracked `ctxBeforeVerifyInner` proof surface. -/
theorem tvDist_ctxBeforeVerifyInner_prefixIsolated_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxBeforeVerifyInner c adversary key)
        (ctxPrefixIsolatedBeforeVerifyInner c adversary key) ≤
      (ctxSecretPrefixQueriedProbabilityInner c key adversary).toReal := by
  unfold ctxPrefixIsolatedBeforeVerifyInner
  rw [← trackedProjection_realWithPrefixFlag_eq_ctxBeforeVerifyInner]
  refine le_trans (tvDist_map_le
    (m := ProbComp)
    (fun result : CtxAliasTarget × (CtxHandlerState × Bool) =>
      trackedProjection key (result.1, result.2.1))
    (ctxRealWithPrefixFlagBeforeVerify c key adversary)
    (ctxPrefixIsolatedFlaggedBeforeVerify c key adversary)) ?_
  exact tvDist_ctxReal_prefixIsolated_le_secretPrefixQueried
    c key adversary

/-- Uniform-key prefix-isolated game with the complete canonical pre-verification output. -/
noncomputable def ctxPrefixIsolatedGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × CtxRO.QueryCache) := do
  let key ← $ᵗ CtxKey
  ctxPrefixIsolatedBeforeVerifyInner c adversary key

/-- Expand the tracked uniform-key prefix probability into its fixed-key average. -/
theorem ctxSecretPrefixQueriedProbability_toReal_eq_tsum
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    (ctxSecretPrefixQueriedProbability c adversary).toReal =
      ∑' key : CtxKey,
        Pr[= key | $ᵗ CtxKey].toReal *
          (ctxSecretPrefixQueriedProbabilityInner c key adversary).toReal := by
  unfold ctxSecretPrefixQueriedProbability ctxBeforeVerifyGame
  rw [probEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun key =>
    ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  refine tsum_congr fun key => ?_
  rw [ENNReal.toReal_mul]
  rfl

/-- Uniform-key prefix isolation, charged exactly to the tracked public-prefix event. -/
theorem tvDist_ctxBeforeVerifyGame_prefixIsolatedGame_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    tvDist (ctxBeforeVerifyGame c adversary)
        (ctxPrefixIsolatedGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
  rw [ctxSecretPrefixQueriedProbability_toReal_eq_tsum]
  unfold ctxBeforeVerifyGame ctxPrefixIsolatedGame
  refine (tvDist_bind_left_le ($ᵗ CtxKey) _ _).trans ?_
  refine Summable.tsum_le_tsum (fun key => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left
      (tvDist_ctxBeforeVerifyInner_prefixIsolated_le_secretPrefixQueried
        c key adversary) ENNReal.toReal_nonneg
  · refine Summable.of_nonneg_of_le
      (fun key => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun key => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (tvDist_le_one _ _)) ?_
    exact ENNReal.summable_toReal tsum_probOutput_ne_top
  · refine Summable.of_nonneg_of_le
      (fun key => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun key => mul_le_of_le_one_right ENNReal.toReal_nonneg ?_) ?_
    · exact ENNReal.toReal_mono one_ne_top probEvent_le_one
    · exact ENNReal.summable_toReal tsum_probOutput_ne_top

end BeaconcryptCore.Computational.CtxPrefixIsolation
