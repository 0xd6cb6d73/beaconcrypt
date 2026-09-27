import BeaconcryptCore.Computational.AdaptiveCtxPrefix

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxLogSimulation
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead

/-- An executable raw-reply simulator forwards ordinary encryption and randomness, retaining supplied plaintexts only from successful encryptions. -/
def runLogged {Result : Type} (decode : RawDecoder) (adversary : OracleComp AdaptiveSpec Result) :
    SealHistory → OracleComp ModifiedNonceAeadAdversarySpec (Result × SealHistory) :=
  OracleComp.recOn adversary
    (fun result history => pure (result, history))
    (fun query _ recurse history => match query with
      | .inl primitive => do
        let answer ← ModifiedNonceAeadAdversarySpec.query primitive
        recurse answer (recordPrimitiveAnswer primitive answer history)
      | .inr raw => recurse (simulatedOpen decode history raw) history)

@[simp] theorem runLogged_pure {Result : Type} (decode : RawDecoder) (result : Result) (history : SealHistory) :
    runLogged decode (pure result) history = pure (result, history) := rfl

@[simp] theorem runLogged_primitive {Result : Type} (decode : RawDecoder)
    (query : ModifiedNonceAeadAdversarySpec.Domain)
    (next : ModifiedNonceAeadAdversarySpec.Range query → OracleComp AdaptiveSpec Result) (history : SealHistory) :
    runLogged decode (AdaptiveSpec.query (.inl query) >>= next) history = (do
      let answer ← ModifiedNonceAeadAdversarySpec.query query
      runLogged decode (next answer) (recordPrimitiveAnswer query answer history)) := rfl

@[simp] theorem runLogged_raw {Result : Type} (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AdaptiveSpec Result) (history : SealHistory) :
    runLogged decode (AdaptiveSpec.query (.inr raw) >>= next) history =
      runLogged decode (next (simulatedOpen decode history raw)) history := rfl

/-- The logged simulator returns exactly the adaptive log/reject transcript under the real ordinary encryption interpreter. The extra opening monitor is projected, never executed by this simulator. -/
theorem runLogged_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp AdaptiveSpec Result) (state : ReceiveState × Bool) :
    Prod.fst <$> (simulateQ (adaptiveImpl false decode c key) adversary).run state =
      (fun result => result.1.1) <$>
        (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
          (runLogged decode adversary state.1.seals.successfulSeals)).run state.1.seals := by
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure result => simp
  | query_bind query rest ih =>
    cases query with
    | inr raw =>
      rw [runLogged_raw]
      simp only [simulateQ_query_bind, StateT.run_bind]
      exact ih (simulatedOpen decode state.1.seals.successfulSeals raw)
        (⟨state.1.seals, state.1.attempts + 1⟩,
          state.2 || decide (actualOpen decode c key raw ≠ simulatedOpen decode state.1.seals.successfulSeals raw))
    | inl primitive =>
      rw [runLogged_primitive]
      simp only [simulateQ_query_bind, StateT.run_bind, map_bind, OracleQuery.input_query]
      change (do
        let result ← (do
          let pair ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state.1.seals
          pure (pair.1, ((⟨pair.2, state.1.attempts⟩ : ReceiveState), state.2)))
        Prod.fst <$> (simulateQ (adaptiveImpl false decode c key) (rest result.1)).run result.2) = (do
        let result ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state.1.seals
        (fun final => final.1.1) <$>
          (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
            (runLogged decode (rest result.1)
              (recordPrimitiveAnswer primitive result.1 state.1.seals.successfulSeals))).run result.2)
      simp only [bind_assoc, pure_bind]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      rw [ih result.1 (⟨result.2, state.1.attempts⟩, state.2)]
      rw [primitiveAnswer_history c key primitive state.1.seals result supported]

/-- Raw replies require no primitive query. Every ordinary resource class is forwarded with its existing bound. -/
theorem runLogged_query_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp AdaptiveSpec Result) (history : SealHistory)
    (p : ModifiedNonceAeadAdversarySpec.Domain → Prop) [DecidablePred p] (bound : ℕ)
    (bounded : adversary.IsQueryBoundP (primitiveClass p) bound) :
    (runLogged decode adversary history).IsQueryBoundP p bound := by
  induction adversary using OracleComp.inductionOn generalizing bound history with
  | pure result => simp
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl primitive =>
      rw [runLogged_primitive, OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ _ (bounded.2 answer)⟩
    | inr raw =>
      rw [runLogged_raw]
      have continued := bounded.2 (simulatedOpen decode history raw)
      rw [if_neg (by simp only [primitiveClass, not_false_eq_true])] at continued
      exact ih _ history bound continued

/-- The returned simulator log equals the challenger's complete successful encryption log. -/
theorem runLogged_history (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp AdaptiveSpec Result)
    (state : ModifiedNonceAeadHandlerState)
    (result : (Result × SealHistory) × ModifiedNonceAeadHandlerState)
    (supported : result ∈ support ((simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (runLogged decode adversary state.successfulSeals)).run state)) :
    result.1.2 = result.2.successfulSeals := by
  induction adversary using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [runLogged_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at supported
    subst result
    rfl
  | query_bind query next ih =>
    cases query with
    | inr raw => exact ih _ state result supported
    | inl primitive =>
      rw [runLogged_primitive] at supported
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query] at supported
      change result ∈ support (do
        let pair ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state
        (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
          (runLogged decode (next pair.1)
            (recordPrimitiveAnswer primitive pair.1 state.successfulSeals))).run pair.2) at supported
      obtain ⟨pair, step, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
      rw [← primitiveAnswer_history c key primitive state pair step] at rest
      exact ih pair.1 pair.2 result rest

/-- Nonces in the primitive state are exactly the nonces recorded by successful encryptions. -/
def NonceHistory (state : ModifiedNonceAeadHandlerState) : Prop :=
  state.usedNonces = state.successfulSeals.map (fun entry => entry.input.nonce)

theorem primitive_preserves_nonceHistory (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (modifiedNonceAeadINTCTXTImpl c key) NonceHistory := by
  intro query state aligned result supported
  cases query with
  | inl coin =>
    change result ∈ support (do let answer ← liftM (unifSpec.query coin); pure (answer, state)) at supported
    obtain ⟨answer, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    exact aligned
  | inr input =>
    change result ∈ support ((modifiedNonceAeadSealOracle c key input).run state) at supported
    rw [modifiedNonceAeadSealOracle_run] at supported
    split at supported <;> obtain rfl := eq_of_mem_support_pure supported
    · exact aligned
    · simpa [NonceHistory, ModifiedNonceAeadHandlerState.addSeal, List.map_cons] using aligned

/-- At most one nonce is recorded by each ordinary sealing query; randomness records none. -/
theorem primitive_nonce_count (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ModifiedNonceAeadAdversarySpec.Domain) (state : ModifiedNonceAeadHandlerState)
    (result : ModifiedNonceAeadAdversarySpec.Range query × ModifiedNonceAeadHandlerState)
    (supported : result ∈ support ((modifiedNonceAeadINTCTXTImpl c key query).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length +
      if IsModifiedNonceAeadSealQuery query then 1 else 0 := by
  cases query with
  | inl coin =>
    change result ∈ support (do let answer ← liftM (unifSpec.query coin); pure (answer, state)) at supported
    obtain ⟨answer, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    simp [IsModifiedNonceAeadSealQuery]
  | inr input =>
    change result ∈ support ((modifiedNonceAeadSealOracle c key input).run state) at supported
    rw [modifiedNonceAeadSealOracle_run] at supported
    split at supported <;> obtain rfl := eq_of_mem_support_pure supported
    · simp [IsModifiedNonceAeadSealQuery]
    · simp [IsModifiedNonceAeadSealQuery, ModifiedNonceAeadHandlerState.addSeal]

/-- Ordinary real encryption records at most the supplied number of seal requests, including rejected nonce reuse. -/
theorem ordinary_run_nonce_count (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (adversary : OracleComp ModifiedNonceAeadAdversarySpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsModifiedNonceAeadSealQuery count)
    (state : ModifiedNonceAeadHandlerState) (result : Result × ModifiedNonceAeadHandlerState)
    (supported : result ∈ support ((simulateQ (modifiedNonceAeadINTCTXTImpl c key) adversary).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length + count := by
  induction adversary using OracleComp.inductionOn generalizing count state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨stepResult, step, rest⟩ := supported
    have first := primitive_nonce_count c key query state stepResult step
    have later := ih stepResult.1 _ (bounded.2 stepResult.1) stepResult.2 result rest
    by_cases isSeal : IsModifiedNonceAeadSealQuery query
    · simp only [isSeal, if_true] at first later
      have positive := bounded.1.resolve_left (not_not.mpr isSeal)
      omega
    · simp only [isSeal, if_false] at first later
      omega

/-- The executable ordinary primitive client retains the entire source CTX result and state as its output. -/
noncomputable def sourceClient {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    OracleComp ModifiedNonceAeadAdversarySpec ((Result × AdaptiveCtxReceive.ReceiveState) × SealHistory) :=
  runLogged (AdaptiveCtxReceive.baseDecoder decode) (AdaptiveCtxReceive.wrapped decode adversary) []

/-- The ordinary source client forwards exactly the established sealing budget. -/
theorem sourceClient_seal_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qSeal : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal) :
    (sourceClient decode adversary).IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal :=
  runLogged_query_bound _ _ [] _ qSeal
    (AdaptiveCtxQueryBounds.wrapped_seal_bound decode adversary qSeal bounded)

/-- All generated private cache misses, including rejected raw attempts, remain in the ordinary client's uniform-oracle budget. -/
theorem sourceClient_uniform_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    (sourceClient decode adversary).IsQueryBoundP IsPrimitiveUniformQuery
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  runLogged_query_bound _ _ [] _ _
    (AdaptiveCtxQueryBounds.wrapped_uniform_bound decode adversary qCoins qHash qSeal qRaw
      coinBound hashBound sealBound rawBound)

/-- The constructive validation nonce is fresh against the actual ordinary challenger state. This uses complete log equality and the source seal cap, not a new oracle assumption. -/
theorem sourceClient_validation_fresh {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qSeal : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (small : qSeal < 2 ^ 96)
    (result : ((Result × AdaptiveCtxReceive.ReceiveState) × SealHistory) × ModifiedNonceAeadHandlerState)
    (supported : result ∈ support ((simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (sourceClient decode adversary)).run emptyModifiedNonceAeadHandlerState)) :
    CtxNonceAeadIndDollarValidation.chooseFreshCtxNonce
      (result.1.2.map (fun entry => entry.input.nonce)) ∉ result.2.usedNonces := by
  have history := runLogged_history (AdaptiveCtxReceive.baseDecoder decode) c key
    (AdaptiveCtxReceive.wrapped decode adversary) emptyModifiedNonceAeadHandlerState result supported
  have aligned := simulateQ_run_preservesInv (modifiedNonceAeadINTCTXTImpl c key) NonceHistory
    (primitive_preserves_nonceHistory c key) (sourceClient decode adversary)
    emptyModifiedNonceAeadHandlerState (show NonceHistory emptyModifiedNonceAeadHandlerState from rfl)
    result supported
  have count := ordinary_run_nonce_count c key (sourceClient decode adversary) qSeal
    (sourceClient_seal_bound decode adversary qSeal bounded) emptyModifiedNonceAeadHandlerState
    result supported
  rw [history, ← aligned]
  apply CtxNonceAeadIndDollarValidation.chooseFreshCtxNonce_not_mem
  rw [CtxNonceAeadIndDollarValidation.ctxNonce_card]
  exact lt_of_le_of_lt (by simpa [emptyModifiedNonceAeadHandlerState] using count) small

/-- Terminal key retention is analysis only: the ordinary client never receives it. -/
noncomputable def retainedLoggedGame {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × AdaptiveCtxReceive.ReceiveState)) := do
  let key ← $ᵗ CtxKey
  let result ← (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
    (sourceClient decode adversary)).run emptyModifiedNonceAeadHandlerState
  pure (key, result.1.1)

/-- The executable ordinary client equals the complete source projection of the log/reject game, jointly with the same sampled key. -/
theorem retainedLoggedGame_eq {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    retainedLoggedGame decode c adversary =
      AdaptiveCtxRetainedKey.sourceProjection <$>
        AdaptiveCtxRetainedKey.retainedLinkedGame false decode c adversary := by
  rw [AdaptiveCtxRetainedKey.retainedLinkedGame_eq]
  simp only [retainedLoggedGame, AdaptiveCtxRetainedKey.retainedAdaptiveGame,
    map_bind, bind_pure_comp, Functor.map_map]
  congr 1
  funext key
  have projected := runLogged_projection (AdaptiveCtxReceive.baseDecoder decode) c key
    (AdaptiveCtxReceive.wrapped decode adversary) (initialState, false)
  have retained := congrArg (fun game => (Prod.mk key) <$> game) projected
  simpa only [Functor.map_map, Function.comp_def, adaptiveGame, sourceClient,
    initialState, emptyModifiedNonceAeadHandlerState, Prod.map_apply, id_eq,
    AdaptiveCtxRetainedKey.sourceProjection,
    AdaptiveCtxRetainedKey.retainKeyAndBoth, AdaptiveCtxReceive.retainBoth] using retained.symm

end BeaconcryptCore.Computational.AdaptiveCtxLogSimulation

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_projection' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_query_bound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_query_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.runLogged_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.primitive_preserves_nonceHistory' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.primitive_preserves_nonceHistory

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.ordinary_run_nonce_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.ordinary_run_nonce_count

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.sourceClient_validation_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.sourceClient_validation_fresh

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.retainedLoggedGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLogSimulation.retainedLoggedGame_eq
