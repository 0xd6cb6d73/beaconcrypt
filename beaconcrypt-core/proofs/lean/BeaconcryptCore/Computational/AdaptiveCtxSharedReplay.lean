import BeaconcryptCore.Computational.AdaptiveCtxSharedHash
import BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary

/-!
The existing replay receiver is compiled into one external public hash cache plus its complete local state and consistent private suffix dictionary. Actual raw parsing, optional replies, lookup order and failed effects are retained through the whole adaptive continuation.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedReplay
open CtxRomAuth CtxSplitCache CtxIndependentTags AdaptiveCtxReceive AdaptiveCtxSharedHash
open AdaptiveCtxReplayDictionary

abbrev Local := AdaptiveCtxSharedHash.Local × CtxSuffixRO.QueryCache

def install (entry : Local) (cache : CtxRO.QueryCache) : ReceiveState :=
  ⟨⟨⟨cache, entry.2⟩, entry.1.usedNonces, entry.1.successfulSeals, entry.1.publicInputs⟩,
    entry.1.rawAttempts, entry.1.privateInputs⟩

def separate (state : ReceiveState) : Local × CtxRO.QueryCache :=
  ((⟨state.ctx.usedNonces, state.ctx.successfulSeals, state.ctx.publicInputs,
    state.rawAttempts, state.privateInputs⟩, state.ctx.cache.suffixCache), state.ctx.cache.publicCache)

theorem install_separate (state : ReceiveState) : install (separate state).1 (separate state).2 = state := rfl

theorem separate_install (entry : Local) (cache : CtxRO.QueryCache) : separate (install entry cache) = (entry, cache) := rfl

noncomputable def privateLookup (suffix : Pqxdh.Bytes) (cache : CtxSuffixRO.QueryCache) :
    ProbComp (CtxDigest × CtxSuffixRO.QueryCache) := do
  match cache suffix with
  | some digest => pure (digest, cache)
  | none =>
      let digest ← $ᵗ CtxDigest
      pure (digest, cache.cacheQuery suffix digest)

theorem private_lookup_exact (suffix : Pqxdh.Bytes) (cache : SplitCache) :
    ctxKeyFreeSuffixStep suffix cache =
      (fun result => (result.1, { cache with suffixCache := result.2 })) <$> privateLookup suffix cache.suffixCache := by
  cases lookup : cache.suffixCache suffix <;>
    simp only [ctxKeyFreeSuffixStep, privateLookup, lookup, map_pure, map_bind, cacheSuffix]

theorem hash_uniform {Result : Type} (work : ProbComp Result) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (OracleComp.liftComp work HashSpec)).run cache =
      (fun answer => (answer, cache)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

noncomputable def localPrivate (suffix : Pqxdh.Bytes) (entry : Local) :
    OracleComp HashSpec (CtxDigest × Local) := do
  let result ← OracleComp.liftComp (privateLookup suffix entry.2) HashSpec
  pure (result.1, { entry.1 with privateInputs := suffix :: entry.1.privateInputs }, result.2)

noncomputable def localSeal (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (entry : Local) : OracleComp HashSpec (Option CtxRomRecord × Local) := do
  if input.nonce ∈ entry.1.usedNonces then pure (none, entry)
  else
    let base := c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let commitment ← localPrivate (outerSuffix input.nonce input.context base.2) entry
    let record : CtxRomRecord := ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commitment.1⟩
    pure (some record, { commitment.2.1 with
      usedNonces := input.nonce :: commitment.2.1.usedNonces,
      successfulSeals := ⟨input, record⟩ :: commitment.2.1.successfulSeals }, commitment.2.2)

noncomputable def localRaw (decode : RawDecoder) (raw : Pqxdh.Bytes) (entry : Local) :
    OracleComp HashSpec (Option Pqxdh.Bytes × Local) := do
  let counted : Local := ({ entry.1 with rawAttempts := entry.1.rawAttempts + 1 }, entry.2)
  match decode raw with
  | none => pure (none, counted)
  | some target =>
      let commitment ← localPrivate (outerSuffix target.nonce target.context target.record.tag) counted
      pure (replayPlaintext (install entry ∅).ctx target, commitment.2)

noncomputable def localImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT Local (OracleComp HashSpec)) := fun query entry =>
  match query with
  | .inl (.inl coin) => do
      let answer ← HashSpec.query (.inl coin)
      pure (answer, entry)
  | .inl (.inr (.inl hash)) => do
      let answer ← HashSpec.query (.inr hash)
      pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2)
  | .inl (.inr (.inr input)) => localSeal c key input entry
  | .inr raw => localRaw decode raw entry

def reassemble {Result : Type} (result : (Result × Local) × CtxRO.QueryCache) : Result × ReceiveState :=
  (result.1.1, install result.1.2 result.2)

theorem private_interpretation (suffix : Pqxdh.Bytes) (entry : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl (localPrivate suffix entry)).run cache =
      (fun result => (result.1, ⟨{ (install entry cache).ctx with cache := result.2 },
        entry.1.rawAttempts, suffix :: entry.1.privateInputs⟩)) <$>
          ctxKeyFreeSuffixStep suffix (install entry cache).ctx.cache := by
  rw [private_lookup_exact]
  simp only [localPrivate, bind_pure_comp, simulateQ_map, StateT.run_map, hash_uniform, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem seal_interpretation (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (entry : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl (localSeal c key input entry)).run cache =
      AdaptiveCtxIndependent.independentCtx c key (.inr input) (install entry cache) := by
  by_cases used : input.nonce ∈ entry.1.usedNonces
  · simp only [localSeal, used, if_true, simulateQ_pure, StateT.run_pure, map_pure]
    simp [AdaptiveCtxIndependent.independentCtx, ctxIndependentTagImpl,
      ctxKeyFreeSealOracle, StateT.run, install, AdaptiveCtxCanonical.sealPrivateInputs, reassemble, used]
  · simp only [localSeal, used, if_false, bind_pure_comp, simulateQ_map, StateT.run_map,
      localPrivate, hash_uniform, Functor.map_map]
    simp only [AdaptiveCtxIndependent.independentCtx, ctxIndependentTagImpl, QueryImpl.add_apply_inr,
      StateT.run, ctxKeyFreeSealOracle, install, used, if_false, ctxKeyFreeSuffixOracle,
      private_lookup_exact, bind_pure_comp]
    simp only [Functor.map_map]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem raw_interpretation (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (entry : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl (localRaw decode raw entry)).run cache =
      replayRaw decode raw (install entry cache) := by
  cases parsed : decode raw with
  | none =>
      simp only [localRaw, parsed, simulateQ_pure, StateT.run_pure, map_pure, replayRaw]
      rfl
  | some target =>
      simp only [localRaw, parsed, bind_pure_comp, simulateQ_map, StateT.run_map,
        localPrivate, hash_uniform, Functor.map_map, replayRaw, private_lookup_exact]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem local_interpretation (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl ((localImpl decode c key query).run entry)).run cache =
      (replayImpl decode c key query).run (install entry cache) := by
  cases query with
  | inl request =>
      cases request with
      | inl coin =>
          change reassemble <$> (simulateQ hashImpl (do
            let answer ← HashSpec.query (.inl coin)
            pure (answer, entry))).run cache = _
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rw [StateT.run_bind]
          simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
          rfl
      | inr operation =>
          cases operation with
          | inl hash =>
              change reassemble <$> (simulateQ hashImpl (do
                let answer ← HashSpec.query (.inr hash)
                pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2))).run cache = _
              simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
              rw [StateT.run_bind]
              simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
              simp only [replayImpl, AdaptiveCtxIndependent.independentCtx, ctxIndependentTagImpl,
                QueryImpl.add_apply_inl, ctxIndependentPublicOracle, StateT.run,
                bind_pure_comp, Functor.map_map]
              rfl
          | inr input => exact seal_interpretation c key input entry cache
  | inr raw => exact raw_interpretation decode raw entry cache

noncomputable def linkedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT (Local × CtxRO.QueryCache) ProbComp) :=
  (hashImpl.mapStateTBase (localImpl decode c key)).flattenStateT

theorem linked_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local × CtxRO.QueryCache) :
    Prod.map id (fun pair => install pair.1 pair.2) <$> (linkedImpl decode c key query).run state =
      (replayImpl decode c key query).run (install state.1 state.2) := by
  simp only [linkedImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq]
  exact local_interpretation decode c key query state.1 state.2

theorem linked_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : Local × CtxRO.QueryCache) :
    Prod.map id (fun pair => install pair.1 pair.2) <$>
      (simulateQ (linkedImpl decode c key) client).run state =
      (simulateQ (replayImpl decode c key) client).run (install state.1 state.2) :=
  map_run_simulateQ_eq_of_query_map_eq (linkedImpl decode c key) (replayImpl decode c key)
    (fun pair => install pair.1 pair.2) (linked_step decode c key) client state

def dismantle {Result : Type} (result : Result × ReceiveState) : (Result × Local) × CtxRO.QueryCache :=
  ((result.1, (separate result.2).1), result.2.ctx.cache.publicCache)

theorem local_from_replay (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl ((localImpl decode c key query).run state)).run cache =
      dismantle <$> (replayImpl decode c key query).run (install state cache) := by
  have mapped := congrArg (fun computation => dismantle <$> computation)
    (local_interpretation decode c key query state cache)
  simp only [Functor.map_map] at mapped
  change id <$> (simulateQ hashImpl ((localImpl decode c key query).run state)).run cache = _ at mapped
  simpa only [id_map] using mapped


end BeaconcryptCore.Computational.AdaptiveCtxSharedReplay

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.install_separate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.install_separate

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.separate_install' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.separate_install

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.private_lookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.private_lookup_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.hash_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.hash_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.private_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.private_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.seal_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.seal_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.raw_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.raw_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.local_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.local_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.linked_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.local_from_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplay.local_from_replay
