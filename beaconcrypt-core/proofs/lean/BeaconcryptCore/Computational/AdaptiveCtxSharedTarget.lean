import BeaconcryptCore.Computational.AdaptiveCtxSharedHash

/-!
Twelve statements route known-key CTX hash work through the selected ordinary challenger's public hash interface. The target key is absent from this forwarding program. Every other-key private lookup uses the same complete common cache. Extra challenger hash-observation instrumentation is separated from the original source public history by an exact full-state law; target nonce, seal, raw and private histories remain unchanged. This is not an independent public cache for each key.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedTarget
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxSharedHash

abbrev SharedState := CtxRO.QueryCache × List Pqxdh.Bytes

noncomputable def forward : QueryImpl HashSpec (OracleComp ReceiveSpec)
  | .inl coin => ReceiveSpec.query (.inl (.inl coin))
  | .inr hash => ReceiveSpec.query (.inl (.inr (.inl hash)))

noncomputable def sharedImpl : QueryImpl HashSpec (StateT SharedState ProbComp) :=
  fun query state => match query with
  | .inl coin => do
      let answer ← unifSpec.query coin
      pure (answer, state)
  | .inr hash => do
      let result ← (ctxRandomOracle hash).run state.1
      pure (result.1, (result.2, hash.2 :: state.2))

def replaceShared (before : CanonicalState) (shared : SharedState) : CanonicalState :=
  { before with ctx := { before.ctx with cache := shared.1, publicInputs := shared.2 } }

set_option backward.isDefEq.respectTransparency false in
/-- Forwarded hash work has the exact selected-challenger cache and observation effect. -/
theorem forward_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : CanonicalState) (query : HashSpec.Domain) (shared : SharedState) :
    Prod.map id (replaceShared before) <$> (sharedImpl query).run shared =
      (simulateQ (canonicalImpl decode c key) (forward query)).run (replaceShared before shared) := by
  cases query with
  | inl coin =>
      simp only [forward, simulateQ_spec_query]
      change Prod.map id (replaceShared before) <$>
        (do let answer ← unifSpec.query coin; pure (answer, shared) : ProbComp _) = _
      simp [canonicalImpl, replaceShared, StateT.run]
  | inr hash =>
      simp only [forward, simulateQ_spec_query]
      simp [sharedImpl, canonicalImpl, canonicalCtx, ctxAdversaryImpl, ctxPublicOracle,
        StateT.run, replaceShared, CtxHandlerState.addPublic, sealPrivateInputs]

/-- All forwarded hash work retains the complete shared cache through an arbitrary continuation. -/
theorem forward_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : CanonicalState) {Result : Type} (work : OracleComp HashSpec Result) (shared : SharedState) :
    Prod.map id (replaceShared before) <$> (simulateQ sharedImpl work).run shared =
      (simulateQ (canonicalImpl decode c key) (simulateQ forward work)).run (replaceShared before shared) := by
  simpa only [QueryImpl.simulateQ_compose] using
    map_run_simulateQ_eq_of_query_map_eq sharedImpl (canonicalImpl decode c key ∘ₛ forward)
      (replaceShared before) (forward_step decode c key before) work shared

/-- The full target state is reconstructed with only the exact shared cache and hash-history updates. -/
theorem forward_complete (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : CanonicalState) {Result : Type} (work : OracleComp HashSpec Result) :
    (simulateQ (canonicalImpl decode c key) (simulateQ forward work)).run before =
      Prod.map id (replaceShared before) <$>
        (simulateQ sharedImpl work).run (before.ctx.cache, before.ctx.publicInputs) :=
  (forward_schedule decode c key before work (before.ctx.cache, before.ctx.publicInputs)).symm

def ForwardClass (p : ReceiveSpec.Domain → Prop) : HashSpec.Domain → Prop
  | .inl coin => p (.inl (.inl coin))
  | .inr hash => p (.inl (.inr (.inl hash)))

instance (p : ReceiveSpec.Domain → Prop) [DecidablePred p] : DecidablePred (ForwardClass p) :=
  fun query => by cases query <;> unfold ForwardClass <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Renaming a hash query preserves its predicate budget over every possible reply. -/
theorem forward_bound (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    {Result : Type} (work : OracleComp HashSpec Result) (bound : Nat)
    (bounded : work.IsQueryBoundP (ForwardClass p) bound) :
    (simulateQ forward work).IsQueryBoundP p bound := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure result => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      cases query <;> simp only [forward, isQueryBoundP_query_bind_iff]
      all_goals refine ⟨by simpa only [ForwardClass] using bounded.1, fun answer => ?_⟩
      all_goals apply ih
      all_goals simpa only [ForwardClass] using bounded.2 _

/-- Forwarded hash queries are exactly selected public-hash requests. -/
theorem forward_hash_class : ForwardClass AdaptiveCtxQueryBounds.SourceHash = HashClass true := by
  funext query
  cases query <;> simp [ForwardClass, AdaptiveCtxQueryBounds.SourceHash, HashClass]

/-- Forwarded uniform queries are exactly selected uniform requests. -/
theorem forward_uniform_class : ForwardClass AdaptiveCtxQueryBounds.SourceUniform = HashClass false := by
  funext query
  cases query <;> simp [ForwardClass, AdaptiveCtxQueryBounds.SourceUniform, HashClass]

/-- Known-key hash forwarding makes no selected encryption request. -/
theorem forward_seal_class : ForwardClass AdaptiveCtxQueryBounds.SourceSeal = fun _ => False := by
  funext query
  cases query <;> rfl

/-- Known-key hash forwarding makes no selected raw-opening request. -/
theorem forward_raw_class : ForwardClass AdaptiveCtxReceive.IsRawQuery = fun _ => False := by
  funext query
  cases query <;> rfl

/-- Known-key local work charges its forwarded hashes and coins without target seal or raw calls. -/
theorem forwarded_local_bounds (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (qHash qSeal qRaw qUniform : Nat)
    (hashBound : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (uniformBound : client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qUniform) (state : Local) :
    (simulateQ forward ((simulateQ (localImpl decode c key) client).run state)).IsQueryBoundP
        AdaptiveCtxQueryBounds.SourceHash (qHash + qSeal + qRaw) ∧
      (simulateQ forward ((simulateQ (localImpl decode c key) client).run state)).IsQueryBoundP
        AdaptiveCtxQueryBounds.SourceUniform qUniform ∧
      (simulateQ forward ((simulateQ (localImpl decode c key) client).run state)).IsQueryBoundP
        AdaptiveCtxQueryBounds.SourceSeal 0 ∧
      (simulateQ forward ((simulateQ (localImpl decode c key) client).run state)).IsQueryBoundP
        AdaptiveCtxReceive.IsRawQuery 0 := by
  refine ⟨forward_bound _ _ _ ?_, forward_bound _ _ _ ?_, forward_bound _ _ _ ?_, forward_bound _ _ _ ?_⟩
  · simpa only [forward_hash_class] using
      local_hash_bound decode c key client qHash qSeal qRaw hashBound sealBound rawBound state
  · simpa only [forward_uniform_class] using local_uniform_bound decode c key client qUniform uniformBound state
  · simp only [forward_seal_class]
    exact isQueryBoundP_false _ 0
  · simp only [forward_raw_class]
    exact isQueryBoundP_false _ 0

set_option backward.isDefEq.respectTransparency false in
/-- Dropping the additional instrumentation log preserves the actual common cache and reply. -/
theorem cache_step (query : HashSpec.Domain) (state : SharedState) :
    Prod.map id Prod.fst <$> (sharedImpl query).run state =
      (hashImpl query).run state.1 := by
  cases query with
  | inl coin =>
      change Prod.map id Prod.fst <$> (do
        let answer ← unifSpec.query coin
        pure (answer, state) : ProbComp _) = (do
        let answer ← unifSpec.query coin
        pure (answer, state.1) : ProbComp _)
      simp
  | inr hash =>
      simp only [sharedImpl, StateT.run, bind_pure_comp, Functor.map_map,
        hashImpl, QueryImpl.add_apply_inr, Prod.map_def, id_eq]
      simp

/-- The common-cache projection preserves an entire adaptive hash computation. -/
theorem cache_schedule {Result : Type} (work : OracleComp HashSpec Result) (state : SharedState) :
    Prod.map id Prod.fst <$> (simulateQ sharedImpl work).run state =
      (simulateQ hashImpl work).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq sharedImpl hashImpl Prod.fst cache_step work state

def replacePublic (before : CanonicalState) (history : List Pqxdh.Bytes) : CanonicalState :=
  { before with ctx := { before.ctx with publicInputs := history } }

def nextPublic (query : ReceiveSpec.Domain) (history : List Pqxdh.Bytes) : List Pqxdh.Bytes :=
  match query with
  | .inl (.inr (.inl hash)) => hash.2 :: history
  | _ => history

set_option backward.isDefEq.respectTransparency false in
/-- An original public history can be retained separately without changing any other target state or reply. -/
theorem public_history_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (before : CanonicalState) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => replacePublic after (nextPublic query history)) <$>
      (canonicalImpl decode c key query).run before =
      (canonicalImpl decode c key query).run (replacePublic before history) := by
  rcases query with (coin | (hash | input)) | raw
  · simp [canonicalImpl, StateT.run, replacePublic, nextPublic]
  · simp [canonicalImpl, canonicalCtx, ctxAdversaryImpl, ctxPublicOracle, StateT.run,
      replacePublic, nextPublic, CtxHandlerState.addPublic, sealPrivateInputs]
  · simp only [canonicalImpl, canonicalCtx, ctxAdversaryImpl, QueryImpl.add_apply_inr,
      StateT.run, ctxSealOracle, replacePublic]
    split <;> simp [nextPublic, CtxHandlerState.addSeal, sealPrivateInputs]
  · cases parsed : decode raw <;>
      simp [canonicalImpl, canonicalRaw, parsed, StateT.run, replacePublic, nextPublic]

end BeaconcryptCore.Computational.AdaptiveCtxSharedTarget

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_complete

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_hash_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_hash_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_uniform_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_uniform_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_seal_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_seal_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_raw_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forward_raw_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forwarded_local_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.forwarded_local_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.cache_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.cache_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.cache_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.cache_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.public_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.public_history_step
