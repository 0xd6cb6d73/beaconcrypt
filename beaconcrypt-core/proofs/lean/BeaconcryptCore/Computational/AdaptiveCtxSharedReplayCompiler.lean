import BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal
import BeaconcryptCore.Computational.AdaptiveSealKeyFamily
import BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy
import BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection

/-!
The key-free indexed replay compiler preserves one common public cache and every per-key private dictionary and history. Complete sampled-source equality precedes the Boolean view projection and the constructed all-key ordinary privacy bound.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler
open CtxRomAuth CtxSplitCache CtxNonceAeadIntCtxt AdaptiveCtxReceive
open AdaptiveCtxSharedHash (HashSpec hashImpl)

abbrev SourceSpec (count : Nat) := RawCtxRoleFamily.FamilySpec ReceiveSpec count
abbrev State (count : Nat) := (Fin count → AdaptiveCtxSharedReplay.Local) × CtxRO.QueryCache

def coinForward {count : Nat} (index : Fin count) :
    QueryImpl unifSpec (OracleComp (AdaptiveSealKeyFamily.Spec count)) :=
  fun coin => (AdaptiveSealKeyFamily.Spec count).query ⟨index, .inl coin⟩

noncomputable def backend {count : Nat} (index : Fin count) :
    QueryImpl AdaptiveCtxSharedReplaySeal.SealSpec
      (StateT CtxRO.QueryCache (OracleComp (AdaptiveSealKeyFamily.Spec count))) :=
  fun query cache => match query with
  | .inl hash => simulateQ (coinForward index) ((hashImpl hash).run cache)
  | .inr input => do
    let answer ← (AdaptiveSealKeyFamily.Spec count).query ⟨index, .inr input⟩
    pure (answer, cache)

noncomputable def compilerImpl {count : Nat} (decode : Fin count → RawDecoder) :
    QueryImpl (SourceSpec count) (StateT (State count) (OracleComp (AdaptiveSealKeyFamily.Spec count))) :=
  fun query state => do
    let result ← (simulateQ (backend query.1)
      ((AdaptiveCtxSharedReplaySeal.compiledImpl (decode query.1) query.2).run (state.1 query.1))).run state.2
    pure (result.1.1, Function.update state.1 query.1 result.1.2, result.2)

set_option backward.isDefEq.respectTransparency false in
theorem family_uniform_step {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (real : Fin count → Bool) (index : Fin count) (coin : Nat) (state : AdaptiveSealKeyFamily.State count) :
    (AdaptiveSealKeyFamily.familyImpl c keys real ⟨index, .inl coin⟩).run state =
      (fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _) := by
  cases selected : real index <;>
    simp only [AdaptiveSealKeyFamily.familyImpl, AdaptiveSealKeyFamily.localImpl,
      selected, Bool.false_eq_true, ite_false, ite_true, StateT.run]
  all_goals
    change (do
      let result ← (do let answer ← unifSpec.query coin; pure (answer, state index) : ProbComp _)
      pure (result.1, Function.update state index result.2)) = _
    simp only [bind_pure_comp, Functor.map_map, Function.update_eq_self]

set_option backward.isDefEq.respectTransparency false in
theorem family_uniform {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (real : Fin count → Bool) (index : Fin count) {Result : Type}
    (work : ProbComp Result) (state : AdaptiveSealKeyFamily.State count) :
    (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys real)
      (simulateQ (coinForward index) work)).run state =
      (fun answer => (answer, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind coin next ih =>
    simp only [coinForward, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [family_uniform_step c keys real index coin state]
    simp only [bind_map_left]
    exact bind_congr (fun answer => ih answer state)

noncomputable def localBackend (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl AdaptiveCtxSharedReplaySeal.SealSpec
      (StateT (ModifiedNonceAeadHandlerState × CtxRO.QueryCache) ProbComp) :=
  (hashImpl.mapStateTBase (AdaptiveCtxSharedReplaySeal.realImpl c key)).flattenStateT

noncomputable def indexedBackend {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (index : Fin count) : QueryImpl AdaptiveCtxSharedReplaySeal.SealSpec
      (StateT (CtxRO.QueryCache × AdaptiveSealKeyFamily.State count) ProbComp) :=
  ((AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true)).mapStateTBase (backend index)).flattenStateT

def place {count : Nat} (index : Fin count) (before : AdaptiveSealKeyFamily.State count)
    (state : ModifiedNonceAeadHandlerState × CtxRO.QueryCache) :
    CtxRO.QueryCache × AdaptiveSealKeyFamily.State count :=
  (state.2, Function.update before index state.1)

theorem family_seal_step {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (index : Fin count) (input : ModifiedNonceAeadSealInput) (state : AdaptiveSealKeyFamily.State count) :
    (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true) ⟨index, .inr input⟩).run state =
      (fun result => (result.1, Function.update state index result.2)) <$>
        (modifiedNonceAeadSealOracle c (keys index) input).run (state index) := by
  change (do
    let result ← (modifiedNonceAeadSealOracle c (keys index) input).run (state index)
    pure (result.1, Function.update state index result.2)) = _
  simp only [bind_pure_comp]

set_option backward.isDefEq.respectTransparency false in
theorem backend_step {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (index : Fin count) (before : AdaptiveSealKeyFamily.State count)
    (query : AdaptiveCtxSharedReplaySeal.SealSpec.Domain)
    (state : ModifiedNonceAeadHandlerState × CtxRO.QueryCache) :
    Prod.map id (place index before) <$> (localBackend c (keys index) query).run state =
      (indexedBackend c keys index query).run (place index before state) := by
  cases query with
  | inl hash =>
    change Prod.map id (place index before) <$>
      ((fun result : (HashSpec.Range hash × ModifiedNonceAeadHandlerState) × CtxRO.QueryCache =>
        (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl (do let answer ← HashSpec.query hash; pure (answer, state.1))).run state.2) =
      (fun result : (HashSpec.Range hash × CtxRO.QueryCache) × AdaptiveSealKeyFamily.State count =>
        (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true))
          (simulateQ (coinForward index) ((hashImpl hash).run state.2))).run
            (Function.update before index state.1)
    rw [family_uniform c keys (fun _ => true) index ((hashImpl hash).run state.2)
      (Function.update before index state.1)]
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_spec_query,
      Functor.map_map, Prod.map_def, id_eq, place]
  | inr input =>
    change Prod.map id (place index before) <$>
      ((fun result : (Option ModifiedNonceAeadCiphertext × ModifiedNonceAeadHandlerState) × CtxRO.QueryCache =>
        (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl (OracleComp.liftComp
          ((modifiedNonceAeadSealOracle c (keys index) input).run state.1) HashSpec)).run state.2) =
      (fun result : (Option ModifiedNonceAeadCiphertext × CtxRO.QueryCache) × AdaptiveSealKeyFamily.State count =>
        (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true)) (do
          let answer ← (AdaptiveSealKeyFamily.Spec count).query ⟨index, .inr input⟩
          pure (answer, state.2))).run (Function.update before index state.1)
    rw [AdaptiveCtxSharedReplay.hash_uniform]
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure]
    rw [family_seal_step c keys index input (Function.update before index state.1)]
    simp only [Function.update_self, bind_pure_comp, Functor.map_map,
      Function.update_idem, Prod.map_def, id_eq, place]

theorem backend_schedule {count : Nat} (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (index : Fin count) (before : AdaptiveSealKeyFamily.State count) {Result : Type}
    (work : OracleComp AdaptiveCtxSharedReplaySeal.SealSpec Result)
    (state : ModifiedNonceAeadHandlerState × CtxRO.QueryCache) :
    Prod.map id (place index before) <$> (simulateQ (localBackend c (keys index)) work).run state =
      (simulateQ (indexedBackend c keys index) work).run (place index before state) :=
  map_run_simulateQ_eq_of_query_map_eq (localBackend c (keys index)) (indexedBackend c keys index)
    (place index before) (backend_step c keys index before) work state

theorem local_backend_run (c : Pqxdh.Crypto) (key : CtxKey) {Result : Type}
    (work : OracleComp AdaptiveCtxSharedReplaySeal.SealSpec Result)
    (base : ModifiedNonceAeadHandlerState) (cache : CtxRO.QueryCache) :
    (simulateQ (localBackend c key) work).run (base, cache) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl ((simulateQ (AdaptiveCtxSharedReplaySeal.realImpl c key) work).run base)).run cache := by
  have equality := simulateQ_mapStateTBase_run_eq_map_flattenStateT hashImpl
    (AdaptiveCtxSharedReplaySeal.realImpl c key) work base cache
  have mapped := congrArg (fun computation =>
    (fun result : (Result × ModifiedNonceAeadHandlerState) × CtxRO.QueryCache =>
      (result.1.1, (result.1.2, result.2))) <$> computation) equality
  simp only [Functor.map_map] at mapped
  change _ = id <$> (simulateQ (localBackend c key) work).run (base, cache) at mapped
  simpa only [id_map] using mapped.symm

theorem local_query (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedReplay.Local) (cache : CtxRO.QueryCache) :
    (simulateQ (localBackend c key) ((AdaptiveCtxSharedReplaySeal.compiledImpl decode query).run entry)).run
      (AdaptiveCtxSharedReplaySeal.baseState entry, cache) =
      (fun result => (result.1, (AdaptiveCtxSharedReplaySeal.baseState result.1.2, result.2))) <$>
        (simulateQ hashImpl ((AdaptiveCtxSharedReplay.localImpl decode c key query).run entry)).run cache := by
  rw [local_backend_run, AdaptiveCtxSharedReplaySeal.local_complete]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

noncomputable def originalImpl {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (SourceSpec count) (StateT (State count) ProbComp) :=
  fun query state => do
    let result ← (AdaptiveCtxSharedModes.targetImpl false (decode query.1) c (keys query.1) query.2).run
      (state.1 query.1, state.2)
    pure (result.1, Function.update state.1 query.1 result.2.1, result.2.2)

def allBase {count : Nat} (state : State count) : AdaptiveSealKeyFamily.State count :=
  fun index => AdaptiveCtxSharedReplaySeal.baseState (state.1 index)

theorem allBase_update {count : Nat} (state : State count) (index : Fin count)
    (entry : AdaptiveCtxSharedReplay.Local) (cache : CtxRO.QueryCache) :
    allBase (Function.update state.1 index entry, cache) =
      Function.update (allBase state) index (AdaptiveCtxSharedReplaySeal.baseState entry) := by
  funext selected
  by_cases same : selected = index <;> simp [allBase, Function.update, same]

set_option backward.isDefEq.respectTransparency false in
theorem original_run {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (SourceSpec count).Domain) (state : State count) :
    (originalImpl decode c keys query).run state =
      (fun result => (result.1.1, Function.update state.1 query.1 result.1.2, result.2)) <$>
        (simulateQ hashImpl
          ((AdaptiveCtxSharedReplay.localImpl (decode query.1) c (keys query.1) query.2).run (state.1 query.1))).run state.2 := by
  simp only [originalImpl, AdaptiveCtxSharedModes.targetImpl, AdaptiveCtxSharedModes.localImpl,
    Bool.false_eq_true, ite_false, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
theorem family_query {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (SourceSpec count).Domain) (state : State count) :
    (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true))
      ((compilerImpl decode query).run state)).run (allBase state) =
      (fun result => (result, allBase result.2)) <$> (originalImpl decode c keys query).run state := by
  rw [original_run]
  change (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true)) (do
    let result ← (simulateQ (backend query.1)
      ((AdaptiveCtxSharedReplaySeal.compiledImpl (decode query.1) query.2).run (state.1 query.1))).run state.2
    pure (result.1.1, Function.update state.1 query.1 result.1.2, result.2))).run (allBase state) = _
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have start : place query.1 (allBase state)
      (AdaptiveCtxSharedReplaySeal.baseState (state.1 query.1), state.2) =
      (state.2, allBase state) := by
    change (state.2, Function.update (allBase state) query.1 ((allBase state) query.1)) = _
    rw [Function.update_eq_self]
  have located := backend_schedule c keys query.1 (allBase state)
    ((AdaptiveCtxSharedReplaySeal.compiledImpl (decode query.1) query.2).run (state.1 query.1))
    (AdaptiveCtxSharedReplaySeal.baseState (state.1 query.1), state.2)
  rw [start, local_query] at located
  simp only [Functor.map_map]
  change (fun result : (ReceiveSpec.Range query.2 × AdaptiveCtxSharedReplay.Local) ×
      (CtxRO.QueryCache × AdaptiveSealKeyFamily.State count) =>
      ((result.1.1, (Function.update state.1 query.1 result.1.2, result.2.1)), result.2.2)) <$>
      (simulateQ (indexedBackend c keys query.1)
        ((AdaptiveCtxSharedReplaySeal.compiledImpl (decode query.1) query.2).run (state.1 query.1))).run
          (state.2, allBase state) =
    (fun result : (ReceiveSpec.Range query.2 × AdaptiveCtxSharedReplay.Local) × CtxRO.QueryCache =>
      ((result.1.1, (Function.update state.1 query.1 result.1.2, result.2)),
        allBase (Function.update state.1 query.1 result.1.2, result.2))) <$>
      (simulateQ hashImpl
        ((AdaptiveCtxSharedReplay.localImpl (decode query.1) c (keys query.1) query.2).run (state.1 query.1))).run state.2
  rw [← located]
  simp only [Functor.map_map, Prod.map_def, id_eq, place, allBase_update]

def install {count : Nat} (state : State count) : State count × AdaptiveSealKeyFamily.State count :=
  (state, allBase state)

noncomputable def linkedCompiler {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (SourceSpec count) (StateT (State count × AdaptiveSealKeyFamily.State count) ProbComp) :=
  ((AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true)).mapStateTBase (compilerImpl decode)).flattenStateT

theorem family_step {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (SourceSpec count).Domain) (state : State count) :
    Prod.map id install <$> (originalImpl decode c keys query).run state =
      (linkedCompiler decode c keys query).run (install state) := by
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true))
      ((compilerImpl decode query).run state)).run (allBase state)
  rw [family_query]
  simp only [Functor.map_map, Prod.map_def, id_eq, install]

theorem family_schedule {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (state : State count) :
    Prod.map id install <$> (simulateQ (originalImpl decode c keys) client).run state =
      (simulateQ (linkedCompiler decode c keys) client).run (install state) :=
  map_run_simulateQ_eq_of_query_map_eq (originalImpl decode c keys) (linkedCompiler decode c keys)
    install (family_step decode c keys) client state

theorem compiled_schedule {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (state : State count) :
    (simulateQ (AdaptiveSealKeyFamily.familyImpl c keys (fun _ => true))
      ((simulateQ (compilerImpl decode) client).run state)).run (allBase state) =
      (fun result => (result, allBase result.2)) <$>
        (simulateQ (originalImpl decode c keys) client).run state := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result : Result × (State count × AdaptiveSealKeyFamily.State count) =>
      ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (linkedCompiler decode c keys) client).run (install state) = _
  rw [← family_schedule decode c keys client state]
  simp only [Functor.map_map, Prod.map_def, id_eq, install]

theorem original_source {count : Nat} (decode : Fin (count + 1) → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey) :
    originalImpl decode c keys = AdaptiveCtxSharedKeySelection.sourceImpl (fun _ => false) decode c keys := rfl

def initialState (count : Nat) : State count := (fun _ => AdaptiveCtxSharedModes.initialEntry, ∅)

theorem initial_base (count : Nat) : allBase (initialState count) = AdaptiveSealKeyFamily.initialState count := rfl

noncomputable def retainedClient {count : Nat} (decode : Fin count → RawDecoder) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) :
    OracleComp (AdaptiveSealKeyFamily.Spec count) (Result × State count) :=
  (simulateQ (compilerImpl decode) client).run (initialState count)

noncomputable def compiledClient {count : Nat} (decode : Fin count → RawDecoder) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) : OracleComp (AdaptiveSealKeyFamily.Spec count) Result :=
  Prod.fst <$> retainedClient decode client

set_option backward.isDefEq.respectTransparency false in
theorem source_game {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp (SourceSpec (count + 1)) Result) :
    AdaptiveSealKeySelection.sourceGame (fun _ => true) c (retainedClient decode client) =
      (fun result => (result, allBase result.2)) <$>
        AdaptiveCtxSharedKeySelection.sourceGame (fun _ => false) decode c client := by
  simp only [AdaptiveSealKeySelection.sourceGame, AdaptiveCtxSharedKeySelection.sourceGame,
    retainedClient, map_bind]
  apply bind_congr
  intro keys
  have equality := compiled_schedule decode c keys client (initialState (count + 1))
  rw [initial_base, original_source] at equality
  simpa only [initialState] using equality

set_option backward.isDefEq.respectTransparency false in
theorem source_view {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp (SourceSpec (count + 1)) Result) :
    Prod.fst <$> AdaptiveSealKeySelection.sourceGame (fun _ => true) c (compiledClient decode client) =
      Prod.fst <$> AdaptiveCtxSharedKeySelection.sourceGame (fun _ => false) decode c client := by
  have equality := congrArg (fun work => (fun result => result.1.1) <$> work)
    (source_game decode c client)
  simpa only [AdaptiveSealKeySelection.sourceGame, compiledClient, simulateQ_map,
    StateT.run_map, map_bind, Functor.map_map] using equality

noncomputable def randomView {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec (count + 1)) Bool) : ProbComp Bool :=
  Prod.fst <$> AdaptiveSealKeySelection.sourceGame (fun _ => false) c (compiledClient decode client)

theorem replay_privacy_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec (count + 1)) Bool) :
    (Prod.fst <$> AdaptiveCtxSharedKeySelection.sourceGame (fun _ => false) decode c client).boolDistAdvantage
      (randomView decode c client) ≤
        ∑ target : Fin (count + 1), CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage c
          (AdaptiveSealMultiKeyPrivacy.reduction target (AdaptiveRawMultiKeyIntegrity.otherReal target) c
            (compiledClient decode client)) := by
  rw [← source_view]
  exact AdaptiveSealMultiKeyPrivacy.all_keys_bound c (compiledClient decode client)

end BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_seal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_seal_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.backend_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.backend_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.backend_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.local_backend_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.local_backend_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.local_query

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.allBase_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.allBase_update

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.original_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.original_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_query

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.family_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.compiled_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.compiled_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.original_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.original_source

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.initial_base' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.initial_base

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.source_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.source_game

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.source_view

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.replay_privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler.replay_privacy_bound
