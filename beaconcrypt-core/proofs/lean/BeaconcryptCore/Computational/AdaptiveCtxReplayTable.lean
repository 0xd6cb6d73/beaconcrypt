import BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary
import BeaconcryptCore.Computational.JointEagerTable

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxReplayTable
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary JointEagerTable

/-- Restrict the actual source cache to the exact fixed-width private interface. This retains every reachable cell, including cells first installed by rejected raw requests. -/
def sourceDictionary (state : AdaptiveCtxReceive.ReceiveState) : PrivateSpec.QueryCache :=
  fun address => state.ctx.cache.suffixCache address.toList

/-- Source/dictionary alignment determines the entire external private dictionary. -/
theorem aligned_dictionary_eq (state : AdaptiveCtxReceive.ReceiveState)
    (dictionary : PrivateSpec.QueryCache) (aligned : DictionaryAligned state.ctx.cache dictionary) :
    dictionary = sourceDictionary state := by
  funext address
  exact (aligned address).symm

/-- The duplicate private dictionary stays exactly equal to the full source cache restriction throughout an arbitrary adaptive continuation. -/
theorem abstractRun_dictionary (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary)
    (result : (Result × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ lazyDictionary
      ((simulateQ (abstractImpl decode c key) adversary).run state)).run dictionary)) :
    result.2 = sourceDictionary result.1.2 := by
  have linkedSupport : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (dictionaryLinked decode c key) adversary).run (state, dictionary)) := by
    unfold dictionaryLinked
    rw [QueryImpl.Stateful.simulateQ_link_run]
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  have kept := OracleComp.simulateQ_run_preservesInv (dictionaryLinked decode c key)
    SourceDictionaryAligned (dictionaryLinked_preserves decode c key) adversary
    (state, dictionary) aligned (result.1.1, (result.1.2, result.2)) linkedSupport
  exact aligned_dictionary_eq result.1.2 result.2 kept

/-- Complete the actual replay-only source cache with an independent finite tail and retain that same table jointly with the complete source result. The tail is an analysis device, never a reduction's runtime table. -/
noncomputable def completedSource {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) : ProbComp ((Suffix → CtxDigest) × (Result × AdaptiveCtxReceive.ReceiveState)) := do
  let result ← (simulateQ (replayImpl decode c key) adversary).run state
  let tail ← $ᵗ (Suffix → CtxDigest)
  pure (tableExtending (sourceDictionary result.2) tail, result)

theorem lazyDictionary_eq_mixed : lazyDictionary = (mixedLazyImpl (D := Suffix) (R := CtxDigest)) := by
  funext query dictionary
  cases query <;> rfl

/-- The source completion is exactly the mixed lazy dictionary completion, including the entire final source cache and every explicit source coin. -/
theorem completedSource_eq_mixed {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary) :
    𝒮[completedSource decode c key adversary state] =
      𝒮[mixedCompletedLazy ((simulateQ (abstractImpl decode c key) adversary).run state) dictionary] := by
  unfold completedSource mixedCompletedLazy
  rw [← abstractRun_projection decode c key adversary state dictionary aligned]
  simp only [bind_map_left]
  rw [← lazyDictionary_eq_mixed]
  apply evalSPMF_bind_congr
  intro result supported
  have same := abstractRun_dictionary decode c key adversary state dictionary aligned result supported
  rw [same]

/-- The complete replay-only source run with one fixed private answer table. Explicit source and public-hash randomness remain actual probabilistic queries. -/
noncomputable def tableRun {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (table : Suffix → CtxDigest) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) : ProbComp (Result × AdaptiveCtxReceive.ReceiveState) :=
  simulateQ (mixedEagerImpl table) ((simulateQ (abstractImpl decode c key) adversary).run state)

/-- Deferred private-table sampling preserves the SAME total table jointly with the complete actual replay-only source result, from every source cache. -/
theorem completedSource_eq_eager {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) :
    𝒮[completedSource decode c key adversary state] =
      𝒮[do
        let tail ← $ᵗ (Suffix → CtxDigest)
        let table := tableExtending (sourceDictionary state) tail
        let result ← tableRun decode c key table adversary state
        pure (table, result)] := by
  rw [completedSource_eq_mixed decode c key adversary state (sourceDictionary state) (fun _ => rfl)]
  let : MeasurableSpace Result := ⊤
  let : DiscreteMeasurableSpace Result := ⟨fun _ => by simp⟩
  let : MeasurableSpace CtxDigest := ⊤
  let : DiscreteMeasurableSpace CtxDigest := ⟨fun _ => by simp⟩
  let : MeasurableSpace AdaptiveCtxReceive.ReceiveState := ⊤
  let : DiscreteMeasurableSpace AdaptiveCtxReceive.ReceiveState := ⟨fun _ => by simp⟩
  exact evalSPMF_eq_of_evalDist_eq _ _ (mixedCompletedLazy_eq_eager _ _)

/-- Fresh-source specialization: one uniformly reserved private table retains its joint law with all actual source state, adaptive replies, logs and explicit coins. -/
theorem completedSource_initial_eq_uniform {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) :
    𝒮[completedSource decode c key adversary AdaptiveCtxReceive.initialState] =
      𝒮[do
        let table ← $ᵗ (Suffix → CtxDigest)
        let result ← tableRun decode c key table adversary AdaptiveCtxReceive.initialState
        pure (table, result)] := by
  rw [completedSource_eq_eager]
  have empty : sourceDictionary AdaptiveCtxReceive.initialState = (∅ : PrivateSpec.QueryCache) := rfl
  simp only [empty, tableExtending_empty]

/-- Reconstruct every private cache entry from its actual query history and the same fixed table. Repeated addresses remain the same sampled cell. Invalid-width entries are absent from the fresh-source interface. -/
def tracedSuffixCache (table : Suffix → CtxDigest) : List Pqxdh.Bytes → CtxSuffixRO.QueryCache
  | [] => ∅
  | input :: prior =>
    if width : input.length = 197 then
      (tracedSuffixCache table prior).cacheQuery input (table ⟨input, width⟩)
    else tracedSuffixCache table prior

/-- One actual typed private lookup installs exactly the same table value in the reconstructed persistent cache. -/
theorem tracedSuffixCache_cons (table : Suffix → CtxDigest) (address : Suffix)
    (prior : List Pqxdh.Bytes) :
    tracedSuffixCache table (address.toList :: prior) =
      (tracedSuffixCache table prior).cacheQuery address.toList (table address) := by
  simp only [tracedSuffixCache, address.toList_length, dite_eq_left]
  rfl

/-- Restore all private lookups, including rejected raw requests, in the terminal source state. Every other cache, transcript, nonce, seal and counter field is retained verbatim. -/
def restorePrivate (table : Suffix → CtxDigest) (state : AdaptiveCtxReceive.ReceiveState) : AdaptiveCtxReceive.ReceiveState :=
  { state with ctx := { state.ctx with cache := { state.ctx.cache with
    suffixCache := tracedSuffixCache table state.privateInputs } } }

/-- Initial full-source state is exactly reconstructed from the empty private history. -/
theorem restorePrivate_initial (table : Suffix → CtxDigest) :
    restorePrivate table AdaptiveCtxReceive.initialState = AdaptiveCtxReceive.initialState := rfl

/-- Raw replay replies depend only on previously public successful full tuples. This interpreter records every private address but leaves dictionary evaluation to the final source reconstruction. -/
def honestOnlyRaw (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    OracleComp DictionarySpec (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) :=
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let address := typedSuffix target.nonce target.context target.record.tag target.record.tagLength
    pure (replayPlaintext state.ctx target, ⟨state.ctx, state.rawAttempts + 1,
      address.toList :: state.privateInputs⟩)

/-- The comparison client queries the private dictionary only for honest seal outputs. Raw attempts still preserve their input history and exact public replay replies. -/
noncomputable def honestOnlyImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState (OracleComp DictionarySpec)) :=
  fun query state => match query with
  | .inl (.inl coin) => do
    let answer ← DictionarySpec.query (.inl coin)
    pure (answer, state)
  | .inl (.inr (.inl hash)) => OracleComp.liftComp (independentCtx c key (.inl hash) state) DictionarySpec
  | .inl (.inr (.inr input)) => abstractSeal c key input state
  | .inr raw => honestOnlyRaw decode raw state

/-- Interpret one source query against the fixed analysis table while keeping all explicit coins real. -/
noncomputable def fixedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (table : Suffix → CtxDigest) : QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => simulateQ (mixedEagerImpl table) (abstractImpl decode c key query state)

/-- The same fixed-table interpreter for the client that does not privately query raw replay attempts. -/
noncomputable def honestFixedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (table : Suffix → CtxDigest) : QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => simulateQ (mixedEagerImpl table) (honestOnlyImpl decode c key query state)

/-- Under each fixed private table, removing a raw request's private query preserves its actual replay reply and reconstructs the same complete persistent source cache. -/
theorem honestRaw_restore (decode : RawDecoder) (raw : Pqxdh.Bytes) (table : Suffix → CtxDigest)
    (state : AdaptiveCtxReceive.ReceiveState) :
    Prod.map id (restorePrivate table) <$> simulateQ (mixedEagerImpl table) (honestOnlyRaw decode raw state) =
      simulateQ (mixedEagerImpl table) (abstractRaw decode raw (restorePrivate table state)) := by
  cases parsed : decode raw with
  | none => simp [honestOnlyRaw, abstractRaw, parsed, restorePrivate]
  | some target =>
    simp only [honestOnlyRaw, abstractRaw, parsed, abstractSuffix, bind_pure_comp,
      simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      simulateQ_pure, map_pure, mixedEagerImpl]
    simp only [Prod.map, id_eq, restorePrivate, tracedSuffixCache_cons]
    rfl

/-- Honest seal outputs are unchanged by reconstructing the actual full private cache from the same fixed table, including earlier raw lookup cells. -/
theorem honestSeal_restore (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (table : Suffix → CtxDigest) (state : AdaptiveCtxReceive.ReceiveState) :
    Prod.map id (restorePrivate table) <$> simulateQ (mixedEagerImpl table) (abstractSeal c key input state) =
      simulateQ (mixedEagerImpl table) (abstractSeal c key input (restorePrivate table state)) := by
  by_cases used : input.nonce ∈ state.ctx.usedNonces
  · simp [abstractSeal, used, restorePrivate]
  · simp only [abstractSeal, restorePrivate, used, ite_false, abstractSuffix, bind_pure_comp,
      simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      mixedEagerImpl, map_pure]
    simp only [Prod.map, id_eq, restorePrivate, CtxIndependentTagState.addSeal, tracedSuffixCache_cons]
    rfl

/-- Reserving the private table leaves all explicit source/public-hash randomness exactly real. -/
theorem eager_coins (table : Suffix → CtxDigest) {Result : Type} (work : ProbComp Result) :
    simulateQ (mixedEagerImpl table) (OracleComp.liftComp work DictionarySpec) = work := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (mixedEagerImpl table)
    (QueryImpl.id' unifSpec) (fun _ => rfl), simulateQ_id']

/-- Independent public-hash queries retain their full actual public cache and commute with restoration of the untouched private cache. -/
theorem publicHash_restore (c : Pqxdh.Crypto) (key : CtxKey) (hash : CtxRO.Domain)
    (table : Suffix → CtxDigest) (state : AdaptiveCtxReceive.ReceiveState) :
    Prod.map id (restorePrivate table) <$> independentCtx c key (.inl hash) state =
      independentCtx c key (.inl hash) (restorePrivate table state) := by
  simp [independentCtx, ctxIndependentTagImpl, ctxIndependentPublicOracle,
    StateT.run, restorePrivate, CtxIndependentTagState.addPublic, sealPrivateInputs,
    bind_pure_comp, Functor.map_map]

/-- Every exact query result and source poststate is recovered from the honest-only dictionary client; no raw private lookup is silently dropped from the reconstructed state. -/
theorem honestFixed_restore (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (table : Suffix → CtxDigest) (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    Prod.map id (restorePrivate table) <$> honestFixedImpl decode c key table query state =
      fixedImpl decode c key table query (restorePrivate table state) := by
  cases query with
  | inr raw => exact honestRaw_restore decode raw table state
  | inl request =>
    cases request with
    | inl coin =>
      simp [honestFixedImpl, fixedImpl, honestOnlyImpl, abstractImpl, mixedEagerImpl,
        bind_pure_comp, Functor.map_map]
    | inr operation =>
      cases operation with
      | inl hash =>
        simp only [honestFixedImpl, fixedImpl, honestOnlyImpl, abstractImpl]
        exact (congrArg (fun work => Prod.map id (restorePrivate table) <$> work)
          (eager_coins table (independentCtx c key (.inl hash) state))).trans
          ((publicHash_restore c key hash table state).trans
            (eager_coins table (independentCtx c key (.inl hash) (restorePrivate table state))).symm)
      | inr input => exact honestSeal_restore c key input table state

/-- The entire fixed-table source run is the complete reconstructed honest-only run, for every adaptive continuation and every prior public state. -/
theorem honestRun_restore {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (table : Suffix → CtxDigest) (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) :
    Prod.map id (restorePrivate table) <$>
      simulateQ (mixedEagerImpl table) ((simulateQ (honestOnlyImpl decode c key) adversary).run state) =
      tableRun decode c key table adversary (restorePrivate table state) := by
  unfold tableRun
  rw [QueryImpl.simulateQ_mapStateTBase_run, QueryImpl.simulateQ_mapStateTBase_run]
  exact map_run_simulateQ_eq_of_query_map_eq (honestFixedImpl decode c key table)
    (fixedImpl decode c key table) (restorePrivate table) (honestFixed_restore decode c key table)
    adversary state

/-- The honest-only mixed client starts in the same complete source state and retains its complete result. -/
noncomputable def honestClient {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) : OracleComp DictionarySpec (Result × AdaptiveCtxReceive.ReceiveState) :=
  (simulateQ (honestOnlyImpl decode c key) adversary).run AdaptiveCtxReceive.initialState

/-- Restore the complete source cache from the retained table without exposing that table to the network adversary. -/
def restoreTerminal {Result : Type} (terminal : (Suffix → CtxDigest) × (Result × AdaptiveCtxReceive.ReceiveState)) :
    (Suffix → CtxDigest) × (Result × AdaptiveCtxReceive.ReceiveState) :=
  (terminal.1, Prod.map id (restorePrivate terminal.1) terminal.2)

/-- The actual completed replay-only source is exactly the completed honest-sealing dictionary client followed by full-cache reconstruction, including every failed raw lookup. -/
theorem completedSource_eq_honestCompletion {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) :
    𝒮[completedSource decode c key adversary AdaptiveCtxReceive.initialState] =
      𝒮[restoreTerminal <$> mixedCompletedLazy (honestClient decode c key adversary) ∅] := by
  rw [completedSource_initial_eq_uniform]
  let : MeasurableSpace Result := ⊤
  let : DiscreteMeasurableSpace Result := ⟨fun _ => by simp⟩
  let : MeasurableSpace CtxDigest := ⊤
  let : DiscreteMeasurableSpace CtxDigest := ⟨fun _ => by simp⟩
  let : MeasurableSpace AdaptiveCtxReceive.ReceiveState := ⊤
  let : DiscreteMeasurableSpace AdaptiveCtxReceive.ReceiveState := ⟨fun _ => by simp⟩
  have reserved := evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_eq_of_evalDist_eq _ _
      (mixedCompletedLazy_empty_eq_uniform (honestClient decode c key adversary))) restoreTerminal
  rw [reserved]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  apply evalSPMF_bind_congr'
  intro table
  have reconstructed := honestRun_restore decode c key table adversary AdaptiveCtxReceive.initialState
  rw [restorePrivate_initial] at reconstructed
  rw [← reconstructed]
  simp only [Functor.map_map, honestClient, restoreTerminal]

end BeaconcryptCore.Computational.AdaptiveCtxReplayTable

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_eq_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_eq_eager

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_initial_eq_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_initial_eq_uniform

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestRaw_restore' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestRaw_restore

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestSeal_restore' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestSeal_restore

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestRun_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.honestRun_restore

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_eq_honestCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayTable.completedSource_eq_honestCompletion
