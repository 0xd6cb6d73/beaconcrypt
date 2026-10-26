import BeaconcryptCore.Computational.AdaptiveCtxCanonical
import BeaconcryptCore.Computational.AdaptiveCtxQueryBounds
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
Twelve statements separate each complete local CTX history from the common random-oracle cache and compile actual sealing and raw opening into a shared hash interface. Installing the same cache recovers the original canonical source program, including malformed input, nonce rejection, optional plaintext and failed private lookups. The equality holds for every complete adaptive continuation. Uniform and hash requests are charged on the actual compiler.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedHash
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical

abbrev HashSpec := unifSpec + CtxRO

structure Local where
  usedNonces : List CtxNonce
  successfulSeals : List CtxSuccessfulSeal
  publicInputs : List Pqxdh.Bytes
  rawAttempts : Nat
  privateInputs : List Pqxdh.Bytes

def install (entry : Local) (cache : CtxRO.QueryCache) : CanonicalState :=
  ⟨⟨cache, entry.usedNonces, entry.successfulSeals, entry.publicInputs⟩,
    entry.rawAttempts, entry.privateInputs⟩

def separate (state : CanonicalState) : Local × CtxRO.QueryCache :=
  (⟨state.ctx.usedNonces, state.ctx.successfulSeals, state.ctx.publicInputs,
    state.rawAttempts, state.privateInputs⟩, state.ctx.cache)

/-- Recombining every local field with its original cache recovers the complete canonical state. -/
theorem install_separate (state : CanonicalState) : install (separate state).1 (separate state).2 = state := rfl

/-- Separating an installed local history and shared cache preserves both exactly. -/
theorem separate_install (entry : Local) (cache : CtxRO.QueryCache) : separate (install entry cache) = (entry, cache) := rfl

noncomputable def hashImpl : QueryImpl HashSpec (StateT CtxRO.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT CtxRO.QueryCache ProbComp) + ctxRandomOracle

noncomputable def localSeal (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : Local) : OracleComp HashSpec (Option CtxRomRecord × Local) :=
  if input.nonce ∈ state.usedNonces then pure (none, state)
  else do
    let base := c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let commit ← HashSpec.query (.inr ((), outerInput key input.nonce input.context base.2))
    let record : CtxRomRecord := ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
    pure (some record, { state with
      usedNonces := input.nonce :: state.usedNonces
      successfulSeals := ⟨input, record⟩ :: state.successfulSeals
      privateInputs := CtxSplitCache.outerSuffix input.nonce input.context record.tag :: state.privateInputs })

noncomputable def localRaw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : Local) : OracleComp HashSpec (Option Pqxdh.Bytes × Local) :=
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target => do
      let expected ← HashSpec.query (.inr ((), outerInput key target.nonce target.context target.record.tag))
      pure (targetOpen c key target expected, { state with
        rawAttempts := state.rawAttempts + 1
        privateInputs := CtxSplitCache.outerSuffix target.nonce target.context target.record.tag :: state.privateInputs })

noncomputable def localImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT Local (OracleComp HashSpec)) := fun query state =>
  match query with
  | .inl (.inl coin) => do
      let answer ← HashSpec.query (.inl coin)
      pure (answer, state)
  | .inl (.inr (.inl query)) => do
      let answer ← HashSpec.query (.inr query)
      pure (answer, { state with publicInputs := query.2 :: state.publicInputs })
  | .inl (.inr (.inr input)) => localSeal c key input state
  | .inr raw => localRaw decode c key raw state

def reassemble {Result : Type} (result : (Result × Local) × CtxRO.QueryCache) : Result × CanonicalState :=
  (result.1.1, install result.1.2 result.2)

set_option backward.isDefEq.respectTransparency false in
/-- The known-key seal compiler equals actual canonical sealing with the same common cache. -/
theorem seal_interpretation (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl (localSeal c key input state)).run cache =
      canonicalCtx c key (.inr input) (install state cache) := by
  by_cases used : input.nonce ∈ state.usedNonces
  · simp only [localSeal, used, ite_true, simulateQ_pure]
    rw [StateT.run_pure]
    simp [map_pure, reassemble, canonicalCtx, ctxAdversaryImpl, ctxSealOracle,
      install, used, StateT.run, sealPrivateInputs]
  · simp only [localSeal, used, ite_false, simulateQ_bind, simulateQ_spec_query, hashImpl,
      QueryImpl.add_apply_inr, simulateQ_pure]
    rw [StateT.run_bind]
    simp only [StateT.run_pure, map_bind, map_pure, reassemble, install]
    simp [canonicalCtx, ctxAdversaryImpl, ctxSealOracle, used, StateT.run,
      sealPrivateInputs, CtxHandlerState.addSeal]

set_option backward.isDefEq.respectTransparency false in
/-- The raw compiler preserves parsing, private lookup, actual optional plaintext and failed-query effects. -/
theorem raw_interpretation (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl (localRaw decode c key raw state)).run cache =
      canonicalRaw decode c key raw (install state cache) := by
  cases parsed : decode raw with
  | none =>
      simp only [localRaw, parsed, simulateQ_pure]
      rw [StateT.run_pure]
      simp [reassemble, canonicalRaw, parsed, install]
  | some target =>
      simp only [localRaw, parsed, simulateQ_bind, simulateQ_spec_query, hashImpl,
        QueryImpl.add_apply_inr, simulateQ_pure]
      rw [StateT.run_bind]
      simp [StateT.run_pure, reassemble, install, canonicalRaw, parsed]

set_option backward.isDefEq.respectTransparency false in
/-- Every local source request has the exact canonical shared-cache interpretation. -/
theorem local_interpretation (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local) (cache : CtxRO.QueryCache) :
    reassemble <$> (simulateQ hashImpl ((localImpl decode c key query).run state)).run cache =
      (canonicalImpl decode c key query).run (install state cache) := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
        change reassemble <$> (do
          let answer ← unifSpec.query coin
          pure ((answer, state), cache) : ProbComp _) = _
        simp [reassemble, canonicalImpl, StateT.run, install]
    | inr query =>
      cases query with
      | inl publicQuery =>
          change reassemble <$> (simulateQ hashImpl
            (do let answer ← HashSpec.query (.inr publicQuery)
                pure (answer, { state with publicInputs := publicQuery.2 :: state.publicInputs }))).run cache = _
          simp only [simulateQ_bind, simulateQ_spec_query, hashImpl, QueryImpl.add_apply_inr,
            simulateQ_pure]
          rw [StateT.run_bind]
          simp only [StateT.run_pure, map_bind, map_pure, reassemble, install]
          simp [canonicalImpl, canonicalCtx, ctxAdversaryImpl,
            ctxPublicOracle, StateT.run, sealPrivateInputs, CtxHandlerState.addPublic]
      | inr input => exact seal_interpretation c key input state cache
  | inr raw => exact raw_interpretation decode c key raw state cache

noncomputable def linkedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT (Local × CtxRO.QueryCache) ProbComp) :=
  (hashImpl.mapStateTBase (localImpl decode c key)).flattenStateT

/-- Each linked request preserves its reply and the complete source-state projection. -/
theorem linked_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local × CtxRO.QueryCache) :
    Prod.map id (fun pair => install pair.1 pair.2) <$> (linkedImpl decode c key query).run state =
      (canonicalImpl decode c key query).run (install state.1 state.2) := by
  simp only [linkedImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq]
  exact local_interpretation decode c key query state.1 state.2

/-- The per-request equality extends to the entire adaptive execution and final state. -/
theorem linked_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : Local × CtxRO.QueryCache) :
    Prod.map id (fun pair => install pair.1 pair.2) <$>
      (simulateQ (linkedImpl decode c key) client).run state =
      (simulateQ (canonicalImpl decode c key) client).run (install state.1 state.2) :=
  map_run_simulateQ_eq_of_query_map_eq (linkedImpl decode c key) (canonicalImpl decode c key)
    (fun pair => install pair.1 pair.2) (linked_step decode c key) client state

def HashClass (hash : Bool) : HashSpec.Domain → Prop
  | .inl _ => hash = false
  | .inr _ => hash = true

instance (hash : Bool) : DecidablePred (HashClass hash) := fun query => by
  cases query <;> unfold HashClass <;> infer_instance

def SourceClass (hash : Bool) (query : ReceiveSpec.Domain) : Prop :=
  if hash then AdaptiveCtxQueryBounds.SourceWork query else AdaptiveCtxQueryBounds.SourceUniform query

instance (hash : Bool) : DecidablePred (SourceClass hash) := fun query => by
  unfold SourceClass
  split <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- One local request contributes at most one query in its indicated uniform or hash class. -/
theorem local_step_bound (hash : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local) :
    ((localImpl decode c key query).run state).IsQueryBoundP (HashClass hash)
      (if SourceClass hash query then 1 else 0) := by
  rcases query with (coin | (publicQuery | input)) | raw
  · simp only [localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff]
    apply (isQueryBoundP_query_iff (HashClass hash) _ _).mpr
    cases hash <;> simp [HashClass, SourceClass, AdaptiveCtxQueryBounds.SourceWork,
      AdaptiveCtxQueryBounds.SourceUniform]
  · simp only [localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff]
    apply (isQueryBoundP_query_iff (HashClass hash) _ _).mpr
    cases hash <;> simp [HashClass, SourceClass, AdaptiveCtxQueryBounds.SourceWork,
      AdaptiveCtxQueryBounds.SourceUniform]
  · simp only [localImpl, StateT.run, localSeal]
    split
    · trivial
    · simp only [bind_pure_comp, isQueryBoundP_map_iff]
      apply (isQueryBoundP_query_iff (HashClass hash) _ _).mpr
      cases hash <;> simp [HashClass, SourceClass, AdaptiveCtxQueryBounds.SourceWork,
        AdaptiveCtxQueryBounds.SourceUniform]
  · simp only [localImpl, StateT.run, localRaw]
    split
    · trivial
    · simp only [bind_pure_comp, isQueryBoundP_map_iff]
      apply (isQueryBoundP_query_iff (HashClass hash) _ _).mpr
      cases hash <;> simp [HashClass, SourceClass, AdaptiveCtxQueryBounds.SourceWork,
        AdaptiveCtxQueryBounds.SourceUniform]

/-- Every complete local continuation inherits its source query-class bound. -/
theorem local_schedule_bound (hash : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (SourceClass hash) bound) (state : Local) :
    ((simulateQ (localImpl decode c key) client).run state).IsQueryBoundP (HashClass hash) bound :=
  bounded.simulateQ_run_StateT_of_step (local_step_bound hash decode c key) state

/-- All public hashing, sealing and raw attempts contribute to the local hash cap. -/
theorem local_hash_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) (state : Local) :
    ((simulateQ (localImpl decode c key) client).run state).IsQueryBoundP (HashClass true) (qHash + qSeal + qRaw) :=
  local_schedule_bound true decode c key client (qHash + qSeal + qRaw)
    (AdaptiveCtxQueryBounds.sourceWork_bound client qHash qSeal qRaw hashBound sealBound rawBound) state

/-- Each source uniform request is forwarded exactly within its original cap. -/
theorem local_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform bound) (state : Local) :
    ((simulateQ (localImpl decode c key) client).run state).IsQueryBoundP (HashClass false) bound :=
  local_schedule_bound false decode c key client bound bounded state

def dismantle {Result : Type} (result : Result × CanonicalState) : (Result × Local) × CtxRO.QueryCache :=
  ((result.1, (separate result.2).1), result.2.ctx.cache)

/-- The inverse full-state projection is an equality of actual oracle programs. -/
theorem local_from_canonical (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : Local) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl ((localImpl decode c key query).run state)).run cache =
      dismantle <$> (canonicalImpl decode c key query).run (install state cache) := by
  have mapped := congrArg (fun computation => dismantle <$> computation)
    (local_interpretation decode c key query state cache)
  simp only [Functor.map_map] at mapped
  change id <$> (simulateQ hashImpl ((localImpl decode c key query).run state)).run cache = _ at mapped
  simpa only [id_map] using mapped

end BeaconcryptCore.Computational.AdaptiveCtxSharedHash

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.install_separate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.install_separate

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.separate_install' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.separate_install

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.seal_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.seal_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.raw_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.raw_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.linked_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_schedule_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_hash_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_from_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedHash.local_from_canonical
