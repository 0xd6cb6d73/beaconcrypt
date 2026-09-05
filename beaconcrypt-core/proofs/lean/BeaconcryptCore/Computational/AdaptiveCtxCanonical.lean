import BeaconcryptCore.Computational.AdaptiveCtxReceive

/-!
# Shared-ROM semantics for adaptive raw CTX receive

The canonical experiment shares one exact-input hash cache across public calls, honest seals, and every well-formed raw verification attempt. Failed commitment checks retain their hash lookup. The split experiment routes public secret-prefix queries to the same suffix cache, so this projection requires no hidden-prefix assumption and loses no statistical term.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxCanonical

open CtxRomAuth CtxSplitCache CtxIndependentTags AdaptiveCtxReceive

/-- Complete canonical state, including failed raw requests and every private hash address suffix. -/
structure CanonicalState where
  ctx : CtxHandlerState
  rawAttempts : ℕ
  privateInputs : List Pqxdh.Bytes

/-- Only the cache representation changes; all histories and counters are retained. -/
def splitState (key : CtxKey) (state : CanonicalState) : ReceiveState :=
  ⟨splitHandlerState key state.ctx, state.rawAttempts, state.privateInputs⟩

def canonicalInitial : CanonicalState := ⟨emptyCtxHandlerState, 0, []⟩

@[simp] theorem splitState_initial (key : CtxKey) : splitState key canonicalInitial = initialState := by
  simp [splitState, canonicalInitial, initialState]

/-- Honest sealing records exactly its successful private hash lookup; nonce rejection records none. -/
def sealPrivateInputs (query : CtxAdversarySpec.Domain)
    (answer : CtxAdversarySpec.Range query) (previous : List Pqxdh.Bytes) : List Pqxdh.Bytes :=
  match query with
  | .inl _ => previous
  | .inr input => match answer with
    | none => previous
    | some record => outerSuffix input.nonce input.context record.tag :: previous

/-- The actual challenger supplies the plaintext; no claimed-plaintext field enters verification. -/
def targetOpen (c : Pqxdh.Crypto) (key : CtxKey)
    (target : CtxUnclaimedAcceptance.Target) (expected : CtxDigest) : Option Pqxdh.Bytes :=
  if target.record.commit = expected then
    c.aeadOpen key.toList target.nonce.toList target.context.ad.bytes target.record.body target.record.tag
  else none

noncomputable def canonicalRaw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : CanonicalState) : ProbComp (Option Pqxdh.Bytes × CanonicalState) := do
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let (digest, cache) ← (ctxRandomOracle ((), outerInput key target.nonce target.context target.record.tag)).run state.ctx.cache
    pure (targetOpen c key target digest,
      ⟨{ state.ctx with cache := cache }, state.rawAttempts + 1,
        outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩)

noncomputable def splitRaw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : ReceiveState) : ProbComp (Option Pqxdh.Bytes × ReceiveState) := do
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let (digest, cache) ← ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache
    pure (targetOpen c key target digest,
      ⟨{ state.ctx with cache := cache }, state.rawAttempts + 1,
        outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩)

/-- Every raw attempt preserves its optional result and complete post-cache under exact splitting, including malformed and rejected candidates. -/
theorem canonicalRaw_split (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : CanonicalState) :
    Prod.map id (splitState key) <$> canonicalRaw decode c key raw state =
      splitRaw decode c key raw (splitState key state) := by
  cases parsed : decode raw with
  | none => simp [canonicalRaw, splitRaw, parsed, splitState]
  | some target =>
    have step := ctxRandomOracle_split_projection key
      ((), outerInput key target.nonce target.context target.record.tag) state.ctx.cache
    rw [ctxSplitRandomOracle_outerInput_eq_keyFreeSuffix] at step
    have observed := congrArg (fun computation => do
      let result ← computation
      pure (targetOpen c key target result.1,
        (⟨{ (splitHandlerState key state.ctx) with cache := result.2 }, state.rawAttempts + 1,
          outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩ : ReceiveState))) step
    simpa only [canonicalRaw, splitRaw, parsed, splitState, splitHandlerState,
      ctxKeyFreeSuffixOracle, StateT.run, map_bind, map_pure, bind_map_left,
      Function.comp_def, Prod.map, id_eq] using observed

/-- The source-shaped public-hash/seal step retains the existing histories and its private hash log. -/
noncomputable def canonicalCtx (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CanonicalState) :
    ProbComp (CtxAdversarySpec.Range query × CanonicalState) := do
  let (answer, ctx) ← (ctxAdversaryImpl c key query).run state.ctx
  pure (answer, ⟨ctx, state.rawAttempts, sealPrivateInputs query answer state.privateInputs⟩)

/-- Routed public-prefix queries share the same private dictionary as seals and failed raw attempts. -/
noncomputable def splitCtx (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : ReceiveState) :
    ProbComp (CtxAdversarySpec.Range query × ReceiveState) := do
  let (answer, ctx) ← (ctxSplitRoutedImpl c key query).run state.ctx
  pure (answer, ⟨ctx, state.rawAttempts, sealPrivateInputs query answer state.privateInputs⟩)

/-- Sealing/public queries retain their complete returned record, nonce history and cache under splitting. -/
theorem canonicalCtx_split (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CanonicalState) :
    Prod.map id (splitState key) <$> canonicalCtx c key query state =
      splitCtx c key query (splitState key state) := by
  have step := ctxAdversaryImpl_split_projection_step c key query state.ctx
  have observed := congrArg (fun computation => do
    let result ← computation
    pure (result.1, (⟨result.2, state.rawAttempts,
      sealPrivateInputs query result.1 state.privateInputs⟩ : ReceiveState))) step
  simpa only [canonicalCtx, splitCtx, splitState, StateT.run, map_bind, map_pure,
    bind_map_left, Function.comp_def, Prod.map, id_eq] using observed

/-- Canonical adaptive raw receive; the hidden key occurs only in the challenger interpretation. -/
noncomputable def canonicalImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT CanonicalState ProbComp) := fun query state =>
  match query with
  | .inl (.inl coin) => do
    let answer ← unifSpec.query coin
    pure (answer, state)
  | .inl (.inr query) => canonicalCtx c key query state
  | .inr raw => canonicalRaw decode c key raw state

/-- Exact split-cache interpretation; this has not yet replaced public secret-prefix access. -/
noncomputable def splitImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT ReceiveState ProbComp) := fun query state =>
  match query with
  | .inl (.inl coin) => do
    let answer ← unifSpec.query coin
    pure (answer, state)
  | .inl (.inr query) => splitCtx c key query state
  | .inr raw => splitRaw decode c key raw state

/-- One arbitrary source call preserves the exact optional reply and all retained state. -/
theorem canonicalImpl_split (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : CanonicalState) :
    Prod.map id (splitState key) <$> (canonicalImpl decode c key query).run state =
      (splitImpl decode c key query).run (splitState key state) := by
  cases query with
  | inl query =>
    cases query with
    | inl coin => simp only [StateT.run, canonicalImpl, splitImpl, map_bind, map_pure, Prod.map, id_eq]
    | inr query => exact canonicalCtx_split c key query state
  | inr raw => exact canonicalRaw_split decode c key raw state

/-- Full source-shaped canonical shared-ROM experiment, parameterized by any adaptive continuation. -/
noncomputable def canonicalGame (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) : ProbComp (Result × CanonicalState) :=
  (simulateQ (canonicalImpl decode c key) adversary).run canonicalInitial

noncomputable def splitGame (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) : ProbComp (Result × ReceiveState) :=
  (simulateQ (splitImpl decode c key) adversary).run initialState

/-- Exact complete-execution equality, including arbitrary malformed deliveries, repeated failed private hashes and successful optional openings. No key/nonce/ciphertext injectivity or prefix-isolation premise is needed. -/
theorem canonicalGame_split (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Prod.map id (splitState key) <$> canonicalGame decode c key adversary =
      splitGame decode c key adversary := by
  simpa only [canonicalGame, splitGame, splitState_initial] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (canonicalImpl decode c key) (splitImpl decode c key) (splitState key)
      (canonicalImpl_split decode c key) adversary canonicalInitial

/-- Every raw delivery occupies exactly one source attempt slot, including malformed input and all rejection paths. -/
theorem canonicalRaw_attempts (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : CanonicalState)
    (result : Option Pqxdh.Bytes × CanonicalState)
    (h : result ∈ support (canonicalRaw decode c key raw state)) :
    result.2.rawAttempts = state.rawAttempts + 1 := by
  cases parsed : decode raw with
  | none =>
    simp only [canonicalRaw, parsed, mem_support_pure_iff] at h
    subst result
    rfl
  | some target =>
    simp only [canonicalRaw, parsed, mem_support_bind_iff] at h
    obtain ⟨⟨digest, cache⟩, _, h⟩ := h
    simp only [mem_support_pure_iff] at h
    subst result
    rfl

/-- A seal or public hash call does not count as a raw delivery. -/
theorem canonicalCtx_attempts (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CanonicalState)
    (result : CtxAdversarySpec.Range query × CanonicalState)
    (h : result ∈ support (canonicalCtx c key query state)) :
    result.2.rawAttempts = state.rawAttempts := by
  simp only [canonicalCtx, mem_support_bind_iff] at h
  obtain ⟨⟨answer, ctx⟩, _, h⟩ := h
  simp only [mem_support_pure_iff] at h
  subst result
  rfl

/-- The raw counter follows the complete source query schedule exactly. -/
theorem canonicalImpl_attempts (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : CanonicalState)
    (result : ReceiveSpec.Range query × CanonicalState)
    (h : result ∈ support ((canonicalImpl decode c key query).run state)) :
    result.2.rawAttempts = state.rawAttempts + if IsRawQuery query then 1 else 0 := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      simp only [StateT.run, canonicalImpl, mem_support_bind_iff] at h
      obtain ⟨answer, _, h⟩ := h
      simp only [mem_support_pure_iff] at h
      subst result
      simp [IsRawQuery]
    | inr query => simpa [IsRawQuery] using canonicalCtx_attempts c key query state result h
  | inr raw => exact canonicalRaw_attempts decode c key raw state result h

/-- Every supported adaptive run counts all raw deliveries against the source bound, including attempts that never reach base opening. -/
theorem canonicalRun_attempt_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count) (state : CanonicalState)
    (result : Result × CanonicalState)
    (h : result ∈ support ((simulateQ (canonicalImpl decode c key) adversary).run state)) :
    result.2.rawAttempts ≤ state.rawAttempts + count := by
  induction adversary using OracleComp.inductionOn generalizing count state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at h
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at h
    simp only [mem_support_bind_iff] at h
    obtain ⟨⟨answer, next⟩, hstep, hrest⟩ := h
    have stepCount := canonicalImpl_attempts decode c key query state (answer, next)
      (by exact hstep)
    have remaining := ih answer _ (bounded.2 answer) next result hrest
    by_cases hraw : IsRawQuery query
    · have positive : 0 < count := bounded.1.resolve_left (not_not.mpr hraw)
      simp only [hraw, if_pos] at stepCount remaining
      omega
    · simp only [hraw, if_false] at stepCount remaining
      omega

/-- Canonical receive exposes at most qRaw source attempts; malformed and commitment-rejected inputs have not been dropped from this count. -/
theorem canonicalGame_attempt_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count)
    (result : Result × CanonicalState)
    (h : result ∈ support (canonicalGame decode c key adversary)) :
    result.2.rawAttempts ≤ count := by
  simpa only [canonicalInitial, Nat.zero_add] using
    canonicalRun_attempt_bound decode c key adversary count bounded canonicalInitial result h

end BeaconcryptCore.Computational.AdaptiveCtxCanonical

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxCanonical.canonicalGame_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxCanonical.canonicalGame_split

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxCanonical.canonicalGame_attempt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxCanonical.canonicalGame_attempt_bound
