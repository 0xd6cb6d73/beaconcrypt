import BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds

/-!
# Independent ordinary replay source

The complete guarded CTX source equals this separately specified key-free source before any ordinary encryption interpretation is selected. The direct random experiment retains all source/cache/history effects and exposes only the final adversary decision. It remains a one-key chosen-plaintext component with an external typed raw decoder; native codec, consuming ratchet, correlated-key and global reveal composition remain separate.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxDirectReplay
open CtxRomAuth CtxNonceAeadIntCtxt CtxSplitCache CtxIndependentTags
open AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation

/-- Explicit ordinary interface for issued-plaintext raw simulation. Its state records actual successful encryption replies only. -/
def loggedAdapter (decode : AdaptiveRawNonceAead.RawDecoder) :
    QueryImpl AdaptiveRawNonceAead.AdaptiveSpec
      (StateT AdaptiveRawNonceAead.SealHistory (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun request history => match request with
  | .inl primitive => do
      let answer ← ModifiedNonceAeadAdversarySpec.query primitive
      pure (answer, AdaptiveRawNonceAead.recordPrimitiveAnswer primitive answer history)
  | .inr raw => pure (AdaptiveRawNonceAead.simulatedOpen decode history raw, history)

/-- The recursive issued-log simulator equals its explicit stateful ordinary oracle on the complete result and history. -/
theorem runLogged_eq_adapter {Result : Type} (decode : AdaptiveRawNonceAead.RawDecoder)
    (client : OracleComp AdaptiveRawNonceAead.AdaptiveSpec Result)
    (history : AdaptiveRawNonceAead.SealHistory) :
    runLogged decode client history = ((simulateQ (loggedAdapter decode) client).run history) := by
  induction client using OracleComp.inductionOn generalizing history with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl primitive =>
      change (do
        let answer ← (ModifiedNonceAeadAdversarySpec.query primitive : OracleComp ModifiedNonceAeadAdversarySpec _)
        runLogged decode (next answer) (AdaptiveRawNonceAead.recordPrimitiveAnswer primitive answer history)) = (do
        let answer ← (ModifiedNonceAeadAdversarySpec.query primitive : OracleComp ModifiedNonceAeadAdversarySpec _)
        (simulateQ (loggedAdapter decode) (next answer)).run
          (AdaptiveRawNonceAead.recordPrimitiveAnswer primitive answer history))
      apply OracleComp.bind_congr_of_forall_mem_support
      exact fun answer _ => ih answer _
    | inr raw =>
      exact ih _ history

/-- Direct ordinary source public-hash query, preserving complete receive state. -/
noncomputable def directPublic (input : CtxRO.Domain) (state : ReceiveState) :
    OracleComp ModifiedNonceAeadAdversarySpec (CtxDigest × ReceiveState) := do
  let answer ← OracleComp.liftComp ((ctxIndependentPublicOracle input).run state.ctx)
    ModifiedNonceAeadAdversarySpec
  pure (answer.1, { state with ctx := answer.2 })

/-- Direct ordinary source suffix lookup; even failed raw input retains its cache miss or hit and private input history. -/
noncomputable def directPrivate (suffix : Pqxdh.Bytes) (state : ReceiveState) :
    OracleComp ModifiedNonceAeadAdversarySpec (CtxDigest × ReceiveState) := do
  let answer ← OracleComp.liftComp (ctxKeyFreeSuffixStep suffix state.ctx.cache)
    ModifiedNonceAeadAdversarySpec
  pure (answer.1, ⟨{ state.ctx with cache := answer.2 }, state.rawAttempts, suffix :: state.privateInputs⟩)

/-- Direct CTX sealing asks the unchanged ordinary seal oracle and commits its actual returned body/tag. -/
noncomputable def directSeal (input : CtxSealInput) (state : ReceiveState) :
    OracleComp ModifiedNonceAeadAdversarySpec (Option CtxRomRecord × ReceiveState) := do
  let answer ← ModifiedNonceAeadAdversarySpec.query (.inr (CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input))
  match answer with
  | none => pure (none, state)
  | some ciphertext =>
    let commitment ← directPrivate (outerSuffix input.nonce input.context ciphertext.tag) state
    let record : CtxRomRecord := ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, commitment.1⟩
    pure (some record, { commitment.2 with ctx := commitment.2.ctx.addSeal ⟨input, record⟩ commitment.2.ctx.cache })

/-- The direct replay source performs the original private lookup before replying from its complete issued CTX tuple log. It has no base-opening request or hidden key. -/
noncomputable def directRaw (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : ReceiveState) :
    OracleComp ModifiedNonceAeadAdversarySpec (Option Pqxdh.Bytes × ReceiveState) := do
  let counted := { state with rawAttempts := state.rawAttempts + 1 }
  match decode raw with
  | none => pure (none, counted)
  | some target =>
    let commitment ← directPrivate (outerSuffix target.nonce target.context target.record.tag) counted
    pure (publicReply decode state.ctx.successfulSeals raw, commitment.2)

/-- An independently specified ordinary replay source uses only public hashes, actual sealing replies, private suffixes and the complete issued log. -/
noncomputable def directImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT ReceiveState (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun query state => match query with
  | .inl (.inl coin) => do
      let answer ← ModifiedNonceAeadAdversarySpec.query (.inl coin)
      pure (answer, state)
  | .inl (.inr (.inl input)) => directPublic input state
  | .inl (.inr (.inr input)) => directSeal input state
  | .inr raw => directRaw decode raw state

/-- Source-internal randomness forwards the same request before its complete continuation and leaves the ordinary issued log unchanged. -/
theorem adapter_uniform {Result : Type} (decode : AdaptiveRawNonceAead.RawDecoder)
    (work : ProbComp Result) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter decode) (OracleComp.liftComp work AdaptiveRawNonceAead.AdaptiveSpec)).run history =
      (fun answer => (answer, history)) <$> OracleComp.liftComp work ModifiedNonceAeadAdversarySpec := by
  induction work using OracleComp.inductionOn generalizing history with
  | pure value => simp
  | query_bind coin next ih =>
    simp only [OracleComp.liftComp_bind, simulateQ_bind, StateT.run_bind, map_bind]
    change (do
      let answer ← (ModifiedNonceAeadAdversarySpec.query (.inl coin) : OracleComp ModifiedNonceAeadAdversarySpec _)
      (simulateQ (loggedAdapter decode) ((next answer).liftComp AdaptiveRawNonceAead.AdaptiveSpec)).run history) = (do
      let answer ← (ModifiedNonceAeadAdversarySpec.query (.inl coin) : OracleComp ModifiedNonceAeadAdversarySpec _)
      (fun value => (value, history)) <$> (next answer).liftComp ModifiedNonceAeadAdversarySpec)
    apply OracleComp.bind_congr_of_forall_mem_support
    exact fun answer _ => ih answer history

/-- The complete private cache transition is the same ordinary source program and preserves every prior issued base record. -/
theorem adapter_private (decode : AdaptiveRawNonceAead.RawDecoder) (suffix : Pqxdh.Bytes)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter decode) (privateStep suffix state)).run history =
      (fun result => (result, history)) <$> directPrivate suffix state := by
  simp only [privateStep, directPrivate, bind_pure_comp, simulateQ_map, StateT.run_map,
    adapter_uniform, Functor.map_map]

/-- Public hash queries forward identical random draws and retain the entire ordinary issued log. -/
theorem adapter_public (decode : AdaptiveRawNonceAead.RawDecoder) (input : CtxRO.Domain)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter decode) (publicStep input state)).run history =
      (fun result => (result, history)) <$> directPublic input state := by
  simp only [publicStep, directPublic, bind_pure_comp, simulateQ_map, StateT.run_map,
    adapter_uniform, Functor.map_map]

/-- Base history records exactly the ordinary portion of each actual successful source sealing reply. -/
def recordBase (query : ReceiveSpec.Domain) (answer : ReceiveSpec.Range query)
    (history : AdaptiveRawNonceAead.SealHistory) : AdaptiveRawNonceAead.SealHistory :=
  match query with
  | .inl (.inr (.inr input)) => match answer with
    | none => history
    | some record => ⟨CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input,
        CtxNonceAeadIntCtxt.CtxRomRecord.toModifiedNonceAeadCiphertext record⟩ :: history
  | _ => history

/-- Every ordinary request forwards its unchanged input and records only the actual returned seal. -/
theorem adapter_primitive (decode : AdaptiveRawNonceAead.RawDecoder)
    (request : ModifiedNonceAeadAdversarySpec.Domain) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter decode)
      (AdaptiveRawNonceAead.AdaptiveSpec.query (.inl request))).run history = (do
        let answer ← ModifiedNonceAeadAdversarySpec.query request
        pure (answer, AdaptiveRawNonceAead.recordPrimitiveAnswer request answer history)) := rfl

/-- Arbitrary ordinary sealing replies drive the exact same complete CTX and base histories; no primitive correctness premise appears. -/
theorem adapter_seal (decode : AdaptiveRawNonceAead.RawDecoder) (input : CtxSealInput)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter decode) (sealStep input state)).run history =
      (fun result => (result, recordBase (.inl (.inr (.inr input))) result.1 history)) <$>
        directSeal input state := by
  simp only [sealStep, directSeal, simulateQ_bind, StateT.run_bind, map_bind,
    adapter_primitive, bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro answer _
  cases answer with
  | none => rfl
  | some ciphertext =>
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, adapter_private,
      Functor.map_map, recordBase, AdaptiveRawNonceAead.recordPrimitiveAnswer]
    rfl

/-- Discarding only the old optional raw reply retains the exact source cache/counters and prior ordinary history under arbitrary primitive replies. -/
theorem adapter_raw (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (fun result => ((publicReply decode state.ctx.successfulSeals raw, result.1.2), result.2)) <$>
      (simulateQ (loggedAdapter (baseDecoder decode)) (rawStep decode raw state)).run history =
      (fun result => (result, history)) <$> directRaw decode raw state := by
  cases parsed : decode raw with
  | none => simp [rawStep, directRaw, publicReply, parsed]
  | some target =>
    simp only [rawStep, directRaw, parsed, simulateQ_bind, StateT.run_bind,
      adapter_private, bind_map_left, map_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro lookup _
    by_cases accepted : target.record.commit = lookup.1
    · simp only [accepted, ite_true, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run, map_pure]
      rfl
    · simp [accepted]

/-- Only raw replies are guarded; the guard reads the original successful full-record history. -/
def guardedAnswer (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (answer : ReceiveSpec.Range query) (state : ReceiveState) : ReceiveSpec.Range query :=
  match query with
  | .inl _ => answer
  | .inr raw => publicReply decode state.ctx.successfulSeals raw

/-- Every guarded source query agrees with the independently specified ordinary replay source and complete updated base history. -/
theorem adapter_query (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (fun result => ((guardedAnswer decode query result.1.1 state, result.1.2), result.2)) <$>
      (simulateQ (loggedAdapter (baseDecoder decode)) ((reductionImpl decode query).run state)).run history =
      (fun result => (result, recordBase query result.1 history)) <$> ((directImpl decode query).run state) := by
  cases query with
  | inr raw => exact adapter_raw decode raw state history
  | inl request =>
    cases request with
    | inl coin => rfl
    | inr request =>
      cases request with
      | inl input =>
        change id <$>
            (simulateQ (loggedAdapter (baseDecoder decode)) (publicStep input state)).run history = _
        rw [id_map]
        exact adapter_public (baseDecoder decode) input state history
      | inr input =>
        change id <$>
            (simulateQ (loggedAdapter (baseDecoder decode)) (sealStep input state)).run history = _
        rw [id_map]
        exact adapter_seal (baseDecoder decode) input state history

/-- Direct private lookups preserve the whole successful sealing history, including misses on rejected raw requests. -/
theorem directPrivate_history (suffix : Pqxdh.Bytes) (state : ReceiveState)
    (result : CtxDigest × ReceiveState) (supported : result ∈ support (directPrivate suffix state)) :
    result.2.ctx.successfulSeals = state.ctx.successfulSeals := by
  simp only [directPrivate, mem_support_bind_iff] at supported
  obtain ⟨answer, _, supported⟩ := supported
  obtain rfl := eq_of_mem_support_pure supported
  rfl

/-- Direct public hashing preserves every issued full record while retaining its actual cache update. -/
theorem directPublic_history (input : CtxRO.Domain) (state : ReceiveState)
    (result : CtxDigest × ReceiveState) (supported : result ∈ support (directPublic input state)) :
    result.2.ctx.successfulSeals = state.ctx.successfulSeals := by
  simp only [directPublic, ctxIndependentPublicOracle, StateT.run, OracleComp.liftComp_bind,
    OracleComp.liftComp_pure, bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨answer, _, supported⟩ := supported
  obtain rfl := eq_of_mem_support_pure supported
  rfl

/-- The direct sealing branch records exactly its returned full tuple, even if the ordinary oracle returns an arbitrary ciphertext. -/
theorem directSeal_history (input : CtxSealInput) (state : ReceiveState)
    (result : Option CtxRomRecord × ReceiveState)
    (supported : result ∈ support (directSeal input state)) :
    recordReply (.inl (.inr (.inr input))) result.1 state.ctx.successfulSeals =
      result.2.ctx.successfulSeals := by
  simp only [directSeal, mem_support_bind_iff] at supported
  obtain ⟨answer, _, supported⟩ := supported
  cases answer with
  | none =>
    obtain rfl := eq_of_mem_support_pure supported
    rfl
  | some ciphertext =>
    simp only [mem_support_bind_iff] at supported
    obtain ⟨lookup, lookup_supported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    change _ :: state.ctx.successfulSeals = _ :: lookup.2.ctx.successfulSeals
    rw [directPrivate_history _ _ _ lookup_supported]

/-- Every direct raw lookup retains the entire issued tuple log. -/
theorem directRaw_history (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : ReceiveState)
    (result : Option Pqxdh.Bytes × ReceiveState)
    (supported : result ∈ support (directRaw decode raw state)) :
    result.2.ctx.successfulSeals = state.ctx.successfulSeals := by
  cases parsed : decode raw with
  | none =>
    simp only [directRaw, parsed] at supported
    obtain rfl := eq_of_mem_support_pure supported
    rfl
  | some target =>
    simp only [directRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, lookup_supported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    exact directPrivate_history _ { state with rawAttempts := state.rawAttempts + 1 } _ lookup_supported

/-- Complete source sealing history is reconstructed from every actual direct reply, without real-world correctness assumptions. -/
theorem directImpl_history (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (state : ReceiveState) (result : ReceiveSpec.Range query × ReceiveState)
    (supported : result ∈ support ((directImpl decode query).run state)) :
    recordReply query result.1 state.ctx.successfulSeals = result.2.ctx.successfulSeals := by
  cases query with
  | inr raw => exact (directRaw_history decode raw state result supported).symm
  | inl request =>
    cases request with
    | inl coin =>
      simp only [directImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _, supported⟩ := supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl
    | inr request =>
      cases request with
      | inl input => exact (directPublic_history input state result supported).symm
      | inr input => exact directSeal_history input state result supported

/-- The complete ordinary source keeps the redundant base log explicitly, with no consistency premise on its prior contents. -/
noncomputable def directWithBase (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT (ReceiveState × AdaptiveRawNonceAead.SealHistory)
      (OracleComp ModifiedNonceAeadAdversarySpec)) := fun query state => do
  let answer ← (directImpl decode query).run state.1
  pure (answer.1, (answer.2, recordBase query answer.1 state.2))

/-- Guard bookkeeping depends on the actual full tuple only for a successful seal; replacing a raw reply does not change that bookkeeping. -/
theorem recordReply_guarded (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (answer : ReceiveSpec.Range query) (state : ReceiveState) :
    recordReply query (guardedAnswer decode query answer state) state.ctx.successfulSeals =
      recordReply query answer state.ctx.successfulSeals := by
  cases query <;> rfl

/-- Nested guard, source and ordinary-log interpretation preserves each query's full result before source-history normalization. -/
theorem guarded_query_expand (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter (baseDecoder decode))
      ((simulateQ (reductionImpl decode)
        ((AdaptiveCtxPrivacyGuard.guard decode query).run state.ctx.successfulSeals)).run state)).run history =
      (fun result => (((result.1.1, recordReply query result.1.1 state.ctx.successfulSeals), result.1.2), result.2)) <$>
        ((fun result => ((guardedAnswer decode query result.1.1 state, result.1.2), result.2)) <$>
          (simulateQ (loggedAdapter (baseDecoder decode))
            ((reductionImpl decode query).run state)).run history) := by
  cases query with
  | inl request =>
    rw [show ((AdaptiveCtxPrivacyGuard.guard decode (.inl request)).run state.ctx.successfulSeals) =
      (fun answer => (answer, recordReply (.inl request) answer state.ctx.successfulSeals)) <$>
        (ReceiveSpec.query (.inl request) : OracleComp ReceiveSpec _) from rfl]
    simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, Functor.map_map,
      guardedAnswer]
  | inr raw =>
    rw [show ((AdaptiveCtxPrivacyGuard.guard decode (.inr raw)).run state.ctx.successfulSeals) =
      (fun _ : ReceiveSpec.Range (.inr raw) => ((publicReply decode state.ctx.successfulSeals raw, state.ctx.successfulSeals) : ReceiveSpec.Range (.inr raw) × PublicHistory)) <$>
        (ReceiveSpec.query (.inr raw) : OracleComp ReceiveSpec (ReceiveSpec.Range (.inr raw))) from rfl]
    rw [simulateQ_map]
    simp only [StateT.run_map, simulateQ_map, simulateQ_spec_query, Functor.map_map,
      guardedAnswer, recordReply]

/-- One complete guarded source query equals the independent direct source, including both histories and every source effect. -/
theorem guarded_query_complete (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (state : ReceiveState) (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter (baseDecoder decode))
      ((simulateQ (reductionImpl decode)
        ((AdaptiveCtxPrivacyGuard.guard decode query).run state.ctx.successfulSeals)).run state)).run history =
      (fun result => (((result.1, result.2.1.ctx.successfulSeals), result.2.1), result.2.2)) <$>
        ((directWithBase decode query).run (state, history)) := by
  rw [guarded_query_expand, adapter_query]
  simp only [directWithBase, StateT.run, bind_pure_comp, Functor.map_map]
  simp only [← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  rw [directImpl_history decode query state result supported]

/-- The complete adaptive guarded source equals the independently specified ordinary replay source before any primitive interpretation is chosen. -/
theorem guarded_run_complete {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (state : ReceiveState)
    (history : AdaptiveRawNonceAead.SealHistory) :
    (simulateQ (loggedAdapter (baseDecoder decode))
      ((simulateQ (reductionImpl decode)
        ((simulateQ (AdaptiveCtxPrivacyGuard.guard decode) adversary).run state.ctx.successfulSeals)).run state)).run history =
      (fun result => (((result.1, result.2.1.ctx.successfulSeals), result.2.1), result.2.2)) <$>
        ((simulateQ (directWithBase decode) adversary).run (state, history)) := by
  induction adversary using OracleComp.inductionOn generalizing state history with
  | pure value => simp
  | query_bind query next ih =>
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [guarded_query_complete, bind_map_left, map_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    exact fun result _ => ih result.1 result.2.1 result.2.2

/-- The direct replay experiment's complete ordinary program includes its source cache, nonce history, private inputs, attempts and redundant issued base log. -/
noncomputable def directClient {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) :
    OracleComp ModifiedNonceAeadAdversarySpec (Result × (ReceiveState × AdaptiveRawNonceAead.SealHistory)) :=
  (simulateQ (directWithBase decode) adversary).run (initialState, [])

/-- Only the duplicate guard history and tuple association differ between the reviewed reduction and the independent direct source. All private source and base history state remains in the output. -/
theorem sourceClient_direct {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) :
    (fun result => (result.1.1.1, (result.1.2, result.2))) <$>
      sourceClient decode (guardedClient decode adversary) = directClient decode adversary := by
  simp only [sourceClient, guardedClient, runLogged_eq_adapter, wrapped]
  rw [show ([] : PublicHistory) = initialState.ctx.successfulSeals from rfl,
    guarded_run_complete]
  simp only [Functor.map_map, Prod.eta]
  change id <$> _ = _
  exact id_map _

/-- Any ordinary interpreter preserves the complete direct-source equality jointly with all of its own retained state. -/
theorem interpreted_complete {PrimitiveState Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result)
    (impl : QueryImpl ModifiedNonceAeadAdversarySpec (StateT PrimitiveState ProbComp))
    (state : PrimitiveState) :
    (fun result => ((result.1.1.1.1, (result.1.1.2, result.1.2)), result.2)) <$>
      ((simulateQ impl (sourceClient decode (guardedClient decode adversary))).run state) =
      ((simulateQ impl (directClient decode adversary)).run state) := by
  rw [← sourceClient_direct decode adversary]
  simp only [simulateQ_map, StateT.run_map]

open CtxNonceAeadIndDollarValidation CtxNonceAeadIndDollar

/-- The independently specified random-source experiment samples no record key. It retains the full direct source and ordinary random-sealing state. -/
noncomputable def directRandomGame {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) :
    ProbComp ((Result × (ReceiveState × AdaptiveRawNonceAead.SealHistory)) × ModifiedNonceAeadHandlerState) :=
  (simulateQ modifiedNonceAeadINDDollarRandomImpl
    (directClient decode adversary)).run emptyModifiedNonceAeadHandlerState

/-- Only the final adversary decision is public; caches and source/challenger histories remain retained analysis state. -/
noncomputable def directRandomView (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  (fun result => result.1.1) <$> directRandomGame decode adversary

/-- The reviewed Boolean reduction is exactly the public decision of the independent direct source at the ordinary interface. -/
theorem viewReduction_direct (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool) :
    (viewReduction decode adversary).main = Prod.fst <$> directClient decode adversary := by
  rw [← sourceClient_direct decode adversary]
  simp only [Functor.map_map]
  rfl

/-- The existing random privacy endpoint equals the independent key-free source on the entire adaptive public decision, after complete-state equality has been established. -/
theorem randomView_direct (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool) :
    randomView decode adversary = directRandomView decode adversary := by
  simp only [randomView, modifiedNonceAeadINDDollarRandomExp, viewReduction_direct,
    simulateQ_map, StateT.run_map, bind_pure_comp, directRandomView,
    directRandomGame, Functor.map_map]

/-- The one-key canonical public view is bounded against the independent random source with the unchanged concrete reduction family and explicit prefix/alias losses. -/
theorem canonical_directRandom_advantage_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp ReceiveSpec Bool)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((canonicalView decode c adversary).boolDistAdvantage (directRandomView decode adversary)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c adversary qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (viewReduction decode adversary)) := by
  rw [← randomView_direct]
  exact canonical_random_advantage_bound decode c fallback adversary qHash qSeal qRaw
    hashBound sealBound rawBound small

end BeaconcryptCore.Computational.AdaptiveCtxDirectReplay

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.runLogged_eq_adapter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.runLogged_eq_adapter

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_uniform

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_private

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_public

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_primitive' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_primitive

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_seal

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_raw

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.adapter_query

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directPrivate_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directPrivate_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directPublic_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directPublic_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directSeal_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directSeal_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directRaw_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directRaw_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directImpl_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.directImpl_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.recordReply_guarded' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.recordReply_guarded

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_query_expand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_query_expand

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_query_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_query_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_run_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.guarded_run_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.sourceClient_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.sourceClient_direct

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.interpreted_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.interpreted_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.viewReduction_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.viewReduction_direct

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.randomView_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.randomView_direct

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.canonical_directRandom_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplay.canonical_directRandom_advantage_bound
