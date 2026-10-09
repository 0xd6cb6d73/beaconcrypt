-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo

/-! Hidden opening and ideal lookup branches of the combined digest compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed)
open PqxdhRecordFactsDigestCache (cacheOf)
variable {n : Nat}

private theorem apply_map {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]; rfl

/-- Literal erased raw reply and local history update; neither cache is queried or changed. -/
noncomputable def rawResult (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhRecordFactsPrivateCache.State) : Option Pqxdh.Bytes × PqxdhRecordFactsPrivateCache.State :=
  let counted := { state.1.1 with rawAttempts := state.1.1.rawAttempts + 1 }
  match decode raw with
  | none => (none, ((counted, state.1.2), state.2))
  | some target =>
      let suffix := outerSuffix target.nonce target.context target.record.tag
      (AdaptiveCtxReplayDictionary.replayPlaintext (AdaptiveCtxSharedReplay.install state.1 ∅).ctx target,
        (({ counted with privateInputs := suffix :: counted.privateInputs }, state.1.2), state.2))

/-- The actual erased raw endpoint is this deterministic result, including its original optional plaintext. -/
theorem raw_exact (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (raw : Pqxdh.Bytes) (state : PqxdhRecordFactsPrivateCache.State) :
    (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr raw)).run state =
      pure (rawResult decode raw state) := by
  cases parsed : decode raw <;>
    simp only [PqxdhRecordFactsPrivateCacheRandom.erased,
      PqxdhRecordFactsPrivateCacheRandom.modePointed, StateT.run, apply_map,
      PqxdhRecordFactsPrivateCache.rawBase, parsed, map_pure,
      rawResult, Prod.map, id_eq]

/-- Reinstall the raw endpoint's exact local state at its selected coordinate. -/
noncomputable def keyedRawResult (decode : RawDecoder) (label : Label n) (raw : Pqxdh.Bytes)
    (state : CtxPrivate n) : Option Pqxdh.Bytes × CtxPrivate n :=
  let result := rawResult decode raw (state.keys label, state.base.primitive.2)
  (result.1, (PqxdhRecordFactsPrivateCacheFamily.localLens label).set state result.2)

/-- The erased keyed raw endpoint returns exactly the deterministic reply and complete state. -/
theorem keyedRaw_exact (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (raw : Pqxdh.Bytes) (state : CtxPrivate n) :
    (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto (label, .inr raw)).run state =
      pure (keyedRawResult decode label raw state) := by
  rw [PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run, raw_exact]
  simp only [map_pure, keyedRawResult, PqxdhRecordFactsPrivateCacheFamily.localLens]

/-- Every rejected or accepted erased raw query preserves the entire combined digest cache. -/
theorem keyedRaw_cache (decode : RawDecoder) (label : Label n) (raw : Pqxdh.Bytes) (state : CtxPrivate n) :
    cacheOf (keyedRawResult decode label raw state).2 = cacheOf state := by
  funext query
  cases parsed : decode raw <;>
    simp only [keyedRawResult, rawResult, parsed, PqxdhRecordFactsPrivateCacheFamily.localLens]
  all_goals
    cases query with
    | inr bytes => rfl
    | inl address =>
        rcases address with ⟨other, suffix⟩
        by_cases same : other = label
        · subst other; simp [cacheOf]
        · simp [cacheOf, Function.update_of_ne same]

/-- The actual hidden opening parser, argument and width gates, followed by its exact erased raw reply. -/
noncomputable def openingResult (frameRead : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    CoreModels.core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n :=
  match RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none => (.None, state)
  | some _ =>
    match RawCtxInterpretedArguments.openArguments
        (RawCtxChainInterpretation.mapOpeningChains
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain)
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain) pending) with
    | none => (.None, state)
    | some input =>
      if width : input.context.associatedData.length = 153 then
        let result := keyedRawResult (RawCtxUniversalDecoder.decoder frameRead) input.material
          (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
            (PqxdhRecordLiftIdeal.materialAt state.base.chain input.material).2 input.context width)) state
        (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context result.1, result.2)
      else (.None, state)

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The complete erased hidden opening executes exactly the original parser/gates and returns the deterministic result above. -/
theorem opening_source (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.opening pending)).run state =
      pure (openingResult codec.frameRead pending state) := by
  change (simulateQ
    (PqxdhRecordFactsPrivateCacheServices.erased modes _ setup.source.crypto
      (PqxdhRecordFactsPrivateCacheCompiler.base
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.opening pending))).run state = _
  rw [PqxdhRecordFactsPrivateCacheSource.erased_opening]
  unfold PqxdhRecordLiftIdeal.hiddenOpening openingResult
  split
  · simp_all only [simulateQ_pure, StateT.run_pure]
  · split
    · simp_all only [simulateQ_pure, StateT.run_pure]
    · split
      · simp_all only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
        rw [keyedRaw_exact modes _ _ _ _ state]
        simp only [map_pure, dite_true]
      · simp_all only [simulateQ_pure, StateT.run_pure, dite_false]

/-- Every actual hidden-opening rejection and accepted replay reply preserves both digest caches completely. -/
theorem opening_cache (frameRead : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    cacheOf (openingResult frameRead pending state).2 = cacheOf state := by
  unfold openingResult
  split
  · rfl
  · split
    · rfl
    · split
      · exact keyedRaw_cache _ _ _ _
      · rfl

/-- The hidden opening compiler performs no random or hash query, returning its actual optional plaintext and all updated raw-history fields. -/
noncomputable def opening (frameRead : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    OracleComp (Spec n) (CoreModels.core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n) :=
  pure (openingResult frameRead pending state)

/-- Exact complementary compiler equation for the hidden opening constructor, with complete source state and combined cache. -/
theorem opening_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (simulateQ plain (opening codec.frameRead pending state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.opening pending)).run state := by
  rw [opening_source]
  simp only [opening, simulateQ_pure, StateT.run_pure, map_pure, packed, opening_cache]

/-- All hidden opening work here is deterministic: the explicit compiler has zero oracle queries. -/
theorem opening_queries (frameRead : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (opening frameRead pending state).IsTotalQueryBound 0 := trivial

/-- The all-ideal lookup retains its source KDF charge on both hits and misses and samples one complete correlated output only on a miss. -/
noncomputable def lookupWork (coordinate : Label n) (state : CtxPrivate n) : ProbComp (Unit × CtxPrivate n) :=
  let charged := { state with base := { state.base with
    primitive := PqxdhRecordLiftChainOracle.charge state.base.primitive } }
  match state.base.chain coordinate with
  | some _ => pure ((), charged)
  | none => do
      let output ← $ᵗ PqxdhFullSecretInputKdf.FullOutput
      pure ((), { charged with base := { charged.base with chain := state.base.chain.cacheQuery coordinate output } })

/-- Exact source all-ideal lookup equation: no hidden native call, seed change or digest query is replaced by finite coins. -/
theorem lookup_source (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (coordinate : Label n) (state : CtxPrivate n) :
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.lookup coordinate)).run state =
      lookupWork coordinate state := by
  change (simulateQ
    (PqxdhRecordFactsPrivateCacheServices.erased modes _ setup.source.crypto
      (PqxdhRecordFactsPrivateCacheCompiler.base
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.lookup coordinate))).run state = _
  simp only [PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter,
    PqxdhRecordFactsCounterProtocol.interpreter, PqxdhRecordLiftIdeal.onBase,
    PqxdhRecordLiftProtocol.withRecord, PqxdhRecordFactsCounter.localInterpreter,
    PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run, apply_map,
    PqxdhRecordLiftLoggedAdapters.liftLookup, PqxdhRecordFactsCounter.lookup,
    PqxdhRecordLiftProtocol.recordState, ↓reduceIte]
  cases cached : state.base.chain coordinate <;>
    simp only [cached, lookupWork, map_pure, bind_pure_comp,
      Functor.map_map, PqxdhRecordLiftProtocol.putRecord, Prod.map, id_eq]

/-- The actual lookup's finite-coin program is lifted without changing its outputs, cache behavior or source instrumentation. -/
noncomputable def lookup (coordinate : Label n) (state : CtxPrivate n) :
    OracleComp (Spec n) (Unit × CtxPrivate n) := OracleComp.liftComp (lookupWork coordinate state) (Spec n)

/-- Every supported all-ideal lookup reply retains the full private and ordinary digest cache. -/
theorem lookup_cache (coordinate : Label n) (state : CtxPrivate n) (result : Unit × CtxPrivate n)
    (supported : result ∈ support (lookupWork coordinate state)) : cacheOf result.2 = cacheOf state := by
  unfold lookupWork at supported
  cases cached : state.base.chain coordinate <;>
    simp only [cached, support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported
  · obtain ⟨output, _, rfl⟩ := supported
    rfl
  · subst result; rfl

/-- Exact complementary lookup compiler equation, retaining the whole source reply/state and canonical combined cache. -/
theorem lookup_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (coordinate : Label n) (state : CtxPrivate n) :
    (simulateQ plain (lookup coordinate state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.lookup coordinate)).run state := by
  rw [lookup_source]
  change (simulateQ plain (OracleComp.liftComp (lookupWork coordinate state) (Spec n))) (cacheOf state) = _
  rw [PqxdhRecordFactsPrivateCacheSourceDrawMemo.coins_exact]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  simp only [packed, lookup_cache coordinate state result supported]

/-- The explicit local compilers may use finite coins but no private or ordinary digest request. -/
def CoinsOnly : (Spec n).Domain → Prop
  | .inl _ => False
  | .inr _ => True

private theorem lifted_coins {X : Type} (work : ProbComp X) :
    (OracleComp.liftComp work (Spec n)).AllQueriesSatisfy CoinsOnly := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).AllQueriesSatisfy _
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨True.intro, ih⟩

/-- The hidden opening compiler makes no digest requests, including on parser/validation rejection. -/
theorem opening_coins (frameRead : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (opening frameRead pending state).AllQueriesSatisfy CoinsOnly := allQueriesSatisfy_pure _ _

/-- Every lookup compiler query is a literal finite coin; it contains no private or ordinary hash request. -/
theorem lookup_coins (coordinate : Label n) (state : CtxPrivate n) :
    (lookup coordinate state).AllQueriesSatisfy CoinsOnly := lifted_coins _

private theorem lifted_bound {X : Type} (work : ProbComp X) (cap : Nat)
    (bounded : work.IsTotalQueryBound cap) :
    (OracleComp.liftComp work (Spec n)).IsTotalQueryBound cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsTotalQueryBound cap
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

set_option maxRecDepth 2048 in
/-- All 76 correlated output bytes are sampled on a lookup miss; the finite-coin cap counts the complete vector. -/
theorem lookup_queries (coordinate : Label n) (state : CtxPrivate n) :
    (lookup coordinate state).IsTotalQueryBound 76 := by
  apply lifted_bound
  cases cached : state.base.chain coordinate with
  | none =>
      simp only [lookupWork, cached, bind_pure_comp]
      rw [IsTotalQueryBound, isQueryBound_map_iff]
      exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76
  | some output =>
      simp only [lookupWork, cached]
      trivial

/-- A cached lookup makes no finite-coin or digest query while still retaining its source KDF charge. -/
theorem lookup_hit_queries (coordinate : Label n) (state : CtxPrivate n)
    (output : PqxdhFullSecretInputKdf.FullOutput) (hit : state.base.chain coordinate = some output) :
    (lookup coordinate state).IsTotalQueryBound 0 := by
  unfold lookup lookupWork
  rw [hit, OracleComp.liftComp_pure]
  trivial

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.raw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.keyedRaw_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms keyedRaw_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.keyedRaw_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms keyedRaw_cache
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.opening_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms opening_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.opening_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms opening_cache
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.opening_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms opening_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.opening_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms opening_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_cache
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.opening_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms opening_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal.lookup_hit_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lookup_hit_queries

end BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal
