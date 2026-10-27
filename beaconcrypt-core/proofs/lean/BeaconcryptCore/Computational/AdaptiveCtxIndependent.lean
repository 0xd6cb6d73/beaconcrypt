import BeaconcryptCore.Computational.AdaptiveCtxCanonical
import BeaconcryptCore.Computational.AdaptiveCtxQueryBounds

/-!
# Direct adaptive CTX receive and its key-free wrapper

The direct independent-public challenger returns the actual optional plaintext after each persistent private suffix lookup. The linked reduction retains a second ordinary AEAD nonce/history record. A checked invariant equates that complete base history to the source history projection, and exact query equations connect all raw, sealing, hash and randomness operations. The full arbitrary adaptive continuation therefore has the same source-state distribution. The ordinary indexed integrity family and its complete query ledger then apply to this direct game.

This is still the independent-public one-key experiment. The canonical routed-prefix hop, adaptive alias guessing, native decoding, ratchet consumption and global multi-key/reveal experiment remain separate obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxIndependent

open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical

abbrev BaseState := AdaptiveRawNonceAead.ReceiveState × Bool
abbrev JointState := AdaptiveCtxReceive.ReceiveState × BaseState

/-- Internal random-oracle sampling forwards its actual randomness without changing any base challenger state. -/
theorem simulate_uniform (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (work : ProbComp Result) (state : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
      (OracleComp.liftComp work AdaptiveRawNonceAead.AdaptiveSpec)).run state =
        (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (simulateQ (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
    (AdaptiveRawNonceAead.AdaptiveSpec.query (.inl (.inl coin)))).run before = _
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- Interpreting a private dictionary lookup retains every base history and instrument exactly. -/
theorem simulate_private (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (suffix : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
      (privateStep suffix state)).run base =
      (fun result => ((result.1,
        (⟨{ state.ctx with cache := result.2 }, state.rawAttempts,
          suffix :: state.privateInputs⟩ : AdaptiveCtxReceive.ReceiveState)), base)) <$>
        ctxKeyFreeSuffixStep suffix state.ctx.cache := by
  simp only [privateStep, bind_pure_comp, simulateQ_map, StateT.run_map,
    simulate_uniform, Functor.map_map]

/-- The direct independent-public challenger uses the same nonce-respecting CTX seal and exact suffix dictionary. -/
noncomputable def independentCtx (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ProbComp (CtxAdversarySpec.Range query × AdaptiveCtxReceive.ReceiveState) := do
  let (answer, ctx) ← (ctxIndependentTagImpl c key query).run state.ctx
  pure (answer, ⟨ctx, state.rawAttempts, sealPrivateInputs query answer state.privateInputs⟩)

/-- Interpreting an ordinary seal delegates to exactly the existing primitive challenger and retains receive instrumentation. -/
theorem simulate_seal (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (input : ModifiedNonceAeadSealInput) (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
      (AdaptiveRawNonceAead.AdaptiveSpec.query (.inl (.inr input)))).run base = (do
        let (answer, seals) ← (modifiedNonceAeadSealOracle c key input).run base.1.seals
        pure (answer, (⟨seals, base.1.attempts⟩, base.2))) := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

/-- Sealing preserves its full source state and response when the wrapper and primitive nonce histories are aligned. -/
theorem seal_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState)
    (aligned : base.1.seals.usedNonces = state.ctx.usedNonces) :
    Prod.fst <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
      (sealStep input state)).run base = independentCtx c key (.inr input) state := by
  simp only [sealStep, simulateQ_bind, StateT.run_bind, simulate_seal,
    modifiedNonceAeadSealOracle_run, CtxSealInput.toModifiedNonceAeadSealInput, aligned]
  by_cases used : input.nonce ∈ state.ctx.usedNonces
  · simp [used, independentCtx, ctxIndependentTagImpl, ctxKeyFreeSealOracle, sealPrivateInputs, StateT.run]
    change (Prod.fst <$> (pure ((none, state), base) : ProbComp _)) = _
    simp
  · simp only [used, ite_false, pure_bind, bind_pure_comp, bind_map_left, simulateQ_map,
      StateT.run_map, simulate_private]
    simp [independentCtx, ctxIndependentTagImpl, ctxKeyFreeSealOracle, StateT.run,
      used, sealPrivateInputs, ctxKeyFreeSuffixOracle, Functor.map_map]
    rfl

/-- Exact response of the actual opening challenger, retaining its discrepancy flag and delegated-attempt counter. -/
theorem simulate_raw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
      (AdaptiveRawNonceAead.AdaptiveSpec.query (.inr raw))).run base =
        AdaptiveRawNonceAead.receiveStep true (baseDecoder decode) c key raw base := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

/-- The source-shaped raw receive projection preserves actual optional plaintext and every failed private lookup. -/
theorem raw_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState) :
    Prod.fst <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
      (rawStep decode raw state)).run base = splitRaw decode c key raw state := by
  cases parsed : decode raw with
  | none => simp [rawStep, splitRaw, parsed]
  | some target =>
    simp only [rawStep, parsed, simulateQ_bind, StateT.run_bind, simulate_private,
      bind_map_left, map_bind, splitRaw]
    apply bind_congr
    rintro ⟨digest, cache⟩
    by_cases equal : target.record.commit = digest
    · simp only [equal, ite_true, bind_pure_comp, simulateQ_map, StateT.run_map, simulate_raw]
      simp [AdaptiveRawNonceAead.receiveStep, AdaptiveRawNonceAead.actualOpen,
        baseDecoder, baseTarget, parsed, targetOpen, equal,
        CtxRomRecord.toModifiedNonceAeadCiphertext]
    · simp [equal, targetOpen]

/-- The retained primitive history is exactly the base projection of the complete source CTX history. -/
def Aligned (state : JointState) : Prop :=
  state.2.1.seals = ctxIndependentTagStateToModifiedNonceAead state.1.ctx

/-- Initial nonce and successful sealing histories agree, without a target-honesty premise. -/
theorem initial_aligned : Aligned (AdaptiveCtxReceive.initialState,
    AdaptiveRawNonceAead.initialState, false) := rfl

/-- A private lookup, including a miss, preserves exact source/base history alignment. -/
theorem private_preserves_aligned (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (suffix : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) (aligned : Aligned (state, base))
    (result : (CtxDigest × AdaptiveCtxReceive.ReceiveState) × BaseState)
    (supported : result ∈ support ((simulateQ
      (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
        (privateStep suffix state)).run base)) : Aligned (result.1.2, result.2) := by
  rw [simulate_private] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  exact aligned

/-- Public hashing retains the complete source query history and leaves all base state unchanged. -/
theorem simulate_public (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
      (publicStep query state)).run base =
      (fun result => ((result.1, { state with ctx := result.2 }), base)) <$>
        (ctxIndependentPublicOracle query).run state.ctx := by
  simp only [publicStep, bind_pure_comp, simulateQ_map, StateT.run_map,
    simulate_uniform, Functor.map_map]

/-- Public hashing's source projection has the same complete cache and public-input log. -/
theorem public_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState) :
    Prod.fst <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
      (publicStep query state)).run base = independentCtx c key (.inl query) state := by
  rw [simulate_public]
  simp [independentCtx, ctxIndependentTagImpl, sealPrivateInputs, Functor.map_map]

/-- A public hash preserves both nonce history and every successful primitive ciphertext log entry. -/
theorem public_preserves_aligned (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) (aligned : Aligned (state, base))
    (result : (CtxDigest × AdaptiveCtxReceive.ReceiveState) × BaseState)
    (supported : result ∈ support ((simulateQ
      (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
        (publicStep query state)).run base)) : Aligned (result.1.2, result.2) := by
  rw [simulate_public] at supported
  simp only [StateT.run, ctxIndependentPublicOracle, bind_pure_comp,
    Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  exact aligned

/-- Every seal keeps the complete primitive log equal to the projection of the source CTX log, including nonce rejection. -/
theorem seal_preserves_aligned (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (input : CtxSealInput) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) (aligned : Aligned (state, base))
    (result : (Option CtxRomRecord × AdaptiveCtxReceive.ReceiveState) × BaseState)
    (supported : result ∈ support ((simulateQ
      (AdaptiveRawNonceAead.adaptiveImpl real (baseDecoder decode) c key)
        (sealStep input state)).run base)) : Aligned (result.1.2, result.2) := by
  have nonces : base.1.seals.usedNonces = state.ctx.usedNonces :=
    congrArg ModifiedNonceAeadHandlerState.usedNonces aligned
  simp only [sealStep, simulateQ_bind, StateT.run_bind, simulate_seal,
    modifiedNonceAeadSealOracle_run, CtxSealInput.toModifiedNonceAeadSealInput, nonces] at supported
  by_cases used : input.nonce ∈ state.ctx.usedNonces
  · simp only [used, ite_true, pure_bind, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at supported
    subst result
    exact aligned
  · simp only [used, ite_false, pure_bind, bind_pure_comp, map_pure, simulateQ_map,
      StateT.run_map, simulate_private, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    unfold Aligned at aligned ⊢
    rw [aligned]
    rfl

/-- Raw verification never changes either successful sealing history, even when it accepts and advances its counters. -/
theorem raw_preserves_aligned (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) (aligned : Aligned (state, base))
    (result : (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) × BaseState)
    (supported : result ∈ support ((simulateQ
      (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
        (rawStep decode raw state)).run base)) : Aligned (result.1.2, result.2) := by
  cases parsed : decode raw with
  | none =>
    simp only [rawStep, parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact aligned
  | some target =>
    simp only [rawStep, parsed, simulateQ_bind, StateT.run_bind, simulate_private,
      bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨⟨digest, cache⟩, _, supported⟩ := supported
    by_cases equal : target.record.commit = digest
    · simp only [equal, ite_true, bind_pure_comp, simulateQ_map, StateT.run_map,
        simulate_raw, AdaptiveRawNonceAead.receiveStep] at supported
      subst result
      exact aligned
    · simp only [equal, ite_false, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact aligned

/-- The full key-free wrapper linked to the real optional-opening challenger. -/
noncomputable def linkedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT JointState ProbComp) :=
  QueryImpl.Stateful.link (reductionImpl decode)
    (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)

/-- Explicit run shape of linking; both private states are retained. -/
theorem linkedImpl_run (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState) :
    (linkedImpl decode c key query).run (state, base) =
      retainBoth <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
        ((reductionImpl decode query).run state)).run base := by
  rfl

/-- Source randomness is forwarded with both states exactly unchanged. -/
theorem simulate_coin (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (coin : unifSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
      ((reductionImpl decode (.inl (.inl coin))).run state)).run base =
      (fun answer => ((answer, state), base)) <$> (unifSpec.query coin : ProbComp _) := by
  change (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
    ((fun answer => (answer, state)) <$> OracleComp.liftComp
      (unifSpec.query coin : ProbComp _) AdaptiveRawNonceAead.AdaptiveSpec)).run base = _
  simp only [simulateQ_map, StateT.run_map, simulate_uniform, Functor.map_map]

/-- Every source request preserves exact alignment of both complete sealing histories. -/
theorem linked_preserves_aligned (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (linkedImpl decode c key) Aligned := by
  rintro query ⟨state, base⟩ aligned result supported
  rw [linkedImpl_run] at supported
  obtain ⟨value, supportValue, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  clear supported
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      rw [simulate_coin] at supportValue
      obtain ⟨answer, _, hvalue⟩ := OracleComp.mem_support_map_peel _ _ supportValue
      subst value
      exact aligned
    | inr query =>
      cases query with
      | inl publicQuery =>
        exact public_preserves_aligned true decode c key publicQuery state base aligned value supportValue
      | inr input =>
        exact seal_preserves_aligned true decode c key input state base aligned value supportValue
  | inr raw =>
    exact raw_preserves_aligned decode c key raw state base aligned value supportValue

/-- Direct independent-public CTX interpretation with the actual optional opening and complete source state. -/
noncomputable def independentImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => match query with
  | .inl (.inl coin) => do
    let answer ← unifSpec.query coin
    pure (answer, state)
  | .inl (.inr query) => independentCtx c key query state
  | .inr raw => splitRaw decode c key raw state

/-- Each linked query returns the direct source answer and complete source state on the proved history invariant. -/
theorem linked_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : JointState) (aligned : Aligned state) :
    Prod.map id Prod.fst <$> (linkedImpl decode c key query).run state =
      (independentImpl decode c key query).run state.1 := by
  rcases state with ⟨state, base⟩
  rw [linkedImpl_run]
  simp only [Functor.map_map]
  change Prod.fst <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key)
    ((reductionImpl decode query).run state)).run base = _
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      rw [simulate_coin]
      simp [independentImpl, StateT.run, Functor.map_map]
    | inr query =>
      cases query with
      | inl publicQuery => exact public_projection decode c key publicQuery state base
      | inr input =>
        exact seal_projection decode c key input state base
          (congrArg ModifiedNonceAeadHandlerState.usedNonces aligned)
  | inr raw => exact raw_projection decode c key raw state base

/-- Direct independent-public game, retaining all source state after the arbitrary adaptive continuation. -/
noncomputable def independentGame (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × AdaptiveCtxReceive.ReceiveState) :=
  (simulateQ (independentImpl decode c key) adversary).run AdaptiveCtxReceive.initialState

/-- Every adaptive execution of the linked wrapper has the exact direct source projection; all source state is retained while extra primitive-game instrumentation is projected away. -/
theorem linkedGame_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Prod.map id Prod.fst <$> linkedGame true decode c key adversary =
      independentGame decode c key adversary := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (linkedImpl decode c key) (independentImpl decode c key) Aligned Prod.fst
    (linked_preserves_aligned decode c key) (linked_projection decode c key)
    adversary (AdaptiveCtxReceive.initialState, AdaptiveRawNonceAead.initialState, false)
    initial_aligned

/-- The complete duplicate base history remains aligned at the end of every adaptive execution. -/
theorem linkedGame_aligned (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ∀ result ∈ support (linkedGame true decode c key adversary), Aligned result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (linkedImpl decode c key) Aligned
    (linked_preserves_aligned decode c key) adversary
    (AdaptiveCtxReceive.initialState, AdaptiveRawNonceAead.initialState, false) initial_aligned

/-- The direct experiment samples the same single uniform primitive key. -/
noncomputable def uniformIndependentGame (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × AdaptiveCtxReceive.ReceiveState) := do
  let key ← $ᵗ CtxKey
  independentGame decode c key adversary

/-- Full source-state projection commutes with the same one-key sampling distribution. -/
theorem uniformLinkedGame_projection (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Prod.map id Prod.fst <$> uniformLinkedGame true decode c adversary =
      uniformIndependentGame decode c adversary := by
  simp only [uniformLinkedGame, uniformIndependentGame, map_bind, linkedGame_projection]

/-- The direct independent-public raw CTX game replaces its actual base plaintext replies by the executable log/reject wrapper at the explicit attempt-indexed ordinary integrity cost. -/
theorem uniformIndependentGame_distance_le_intctxt_sum (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    ENNReal.ofReal (discreteDistance (uniformIndependentGame decode c adversary)
      (Prod.map id Prod.fst <$> uniformLinkedGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) := by
  rw [← uniformLinkedGame_projection]
  exact (ENNReal.ofReal_le_ofReal (discreteDistance_map_le (Prod.map id Prod.fst) _ _)).trans
    (uniformLinkedGame_distance_le_intctxt_sum decode c fallback adversary count bounded)

/-- The direct-game integrity hop and every constructed reduction share the same explicit source budgets. -/
theorem uniformIndependentGame_bound_and_query_accounting (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    ENNReal.ofReal (discreteDistance (uniformIndependentGame decode c adversary)
      (Prod.map id Prod.fst <$> uniformLinkedGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range qRaw,
        modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) ∧
    ∀ index,
      (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qCoins + 64 * (qHash + qSeal + qRaw)) ∧
      (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index).MakesAtMostSealQueries qSeal :=
  ⟨uniformIndependentGame_distance_le_intctxt_sum decode c fallback adversary qRaw rawBound,
    fun index => AdaptiveCtxQueryBounds.indexedReduction_bounds decode fallback adversary
      qCoins qHash qSeal qRaw index coinBound hashBound sealBound rawBound⟩

/-- The interpreted ordinary challenger additionally pays for its 32-byte key sample; that work is outside the reduction's main-query cap. -/
theorem indexedReduction_challenger_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw index : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (modifiedNonceAeadINTCTXTGame c
      (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index)).IsTotalQueryBound
        (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  apply CtxComputationalSecurity.modifiedNonceAeadINTCTXTGame_total_of_uniform_query_bound
  exact (AdaptiveCtxQueryBounds.indexedReduction_bounds decode fallback adversary
    qCoins qHash qSeal qRaw index coinBound hashBound sealBound rawBound).1

end BeaconcryptCore.Computational.AdaptiveCtxIndependent

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxIndependent.linked_preserves_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxIndependent.linked_preserves_aligned

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxIndependent.linkedGame_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxIndependent.linkedGame_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxIndependent.linkedGame_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxIndependent.linkedGame_aligned

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxIndependent.uniformIndependentGame_bound_and_query_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxIndependent.uniformIndependentGame_bound_and_query_accounting

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxIndependent.indexedReduction_challenger_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxIndependent.indexedReduction_challenger_uniform_bound
