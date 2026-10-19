import BeaconcryptCore.Computational.AdaptiveCtxSharedReplay
import BeaconcryptCore.Computational.AdaptiveCtxSharedFamily

/-!
Real and replay CTX operations share a single complete state representation. Full-state forwarding laws retain the same common cache while separately restoring the original selected public history after reduction instrumentation. The selected key is absent from the forwarding program.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedModes
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive AdaptiveCtxSharedHash

abbrev Entry := AdaptiveCtxSharedReplay.Local
abbrev State := Entry × CtxRO.QueryCache

noncomputable def localImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT Entry (OracleComp HashSpec)) := fun query entry =>
  if real then do
    let result ← (AdaptiveCtxSharedHash.localImpl decode c key query).run entry.1
    pure (result.1, (result.2, entry.2))
  else AdaptiveCtxSharedReplay.localImpl decode c key query entry

noncomputable def targetImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT State ProbComp) :=
  (hashImpl.mapStateTBase (localImpl real decode c key)).flattenStateT

def canonicalProjection (state : State) : AdaptiveCtxCanonical.CanonicalState :=
  AdaptiveCtxSharedHash.install state.1.1 state.2

def replayProjection (state : State) : ReceiveState :=
  AdaptiveCtxSharedReplay.install state.1 state.2

set_option backward.isDefEq.respectTransparency false in
theorem real_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : State) :
    Prod.map id canonicalProjection <$> (targetImpl true decode c key query).run state =
      (AdaptiveCtxCanonical.canonicalImpl decode c key query).run (canonicalProjection state) := by
  change Prod.map id canonicalProjection <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ hashImpl (do
      let result ← (AdaptiveCtxSharedHash.localImpl decode c key query).run state.1.1
      pure (result.1, (result.2, state.1.2)))).run state.2) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  exact AdaptiveCtxSharedHash.local_interpretation decode c key query state.1.1 state.2

theorem replay_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : State) :
    Prod.map id replayProjection <$> (targetImpl false decode c key query).run state =
      (AdaptiveCtxReplayDictionary.replayImpl decode c key query).run (replayProjection state) :=
  AdaptiveCtxSharedReplay.linked_step decode c key query state

theorem real_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : State) :
    Prod.map id canonicalProjection <$> (simulateQ (targetImpl true decode c key) client).run state =
      (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key) client).run (canonicalProjection state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (real_step decode c key) client state

theorem replay_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : State) :
    Prod.map id replayProjection <$> (simulateQ (targetImpl false decode c key) client).run state =
      (simulateQ (AdaptiveCtxReplayDictionary.replayImpl decode c key) client).run (replayProjection state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (replay_step decode c key) client state

def initialEntry : Entry := (AdaptiveCtxSharedFamily.initialLocal, ∅)
def initialState : State := (initialEntry, ∅)

theorem canonical_initial : canonicalProjection initialState = AdaptiveCtxCanonical.canonicalInitial := rfl

theorem replay_initial : replayProjection initialState = AdaptiveCtxReceive.initialState := rfl

noncomputable def targetGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp ReceiveSpec Result) : ProbComp (Result × State) := do
  let key ← $ᵗ CtxKey
  (simulateQ (targetImpl real decode c key) client).run initialState

noncomputable def targetView (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec Bool) : ProbComp Bool := Prod.fst <$> targetGame real decode c client

set_option backward.isDefEq.respectTransparency false in
theorem real_view_eq (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    targetView true decode c client = AdaptiveCtxPrivacyGuard.canonicalView decode c client := by
  simp only [targetView, targetGame, AdaptiveCtxPrivacyGuard.canonicalView,
    AdaptiveCtxPrefixValidation.retainedCanonicalGame, map_bind]
  apply bind_congr
  intro key
  have projected := congrArg (fun work => Prod.fst <$> work) (real_schedule decode c key client initialState)
  simpa only [Functor.map_map, Prod.map_fst, id_eq, canonical_initial, AdaptiveCtxCanonical.canonicalGame, map_pure, bind_pure_comp] using projected

theorem replay_view_eq (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    targetView false decode c client = AdaptiveCtxPrivacyGuard.replayView decode c client := by
  simp only [targetView, targetGame, AdaptiveCtxPrivacyGuard.replayView,
    AdaptiveCtxAliasCoupling.retainedReplayGame, map_bind, bind_pure_comp, Functor.map_map]
  apply bind_congr
  intro key
  have projected := congrArg (fun work => Prod.fst <$> work) (replay_schedule decode c key client initialState)
  simpa only [Functor.map_map, Prod.map_fst, id_eq, replay_initial] using projected

open AdaptiveCtxSharedTarget

def replaceShared (state : State) (shared : SharedState) : State :=
  (({ state.1.1 with publicInputs := shared.2 }, state.1.2), shared.1)

def forwardIndex : HashSpec.Domain → ReceiveSpec.Domain
  | .inl coin => .inl (.inl coin)
  | .inr hash => .inl (.inr (.inl hash))

def forwardReply (query : HashSpec.Domain) : HashSpec.Range query → ReceiveSpec.Range (forwardIndex query) :=
  match query with
  | .inl _ => id
  | .inr _ => id

def afterHash (query : HashSpec.Domain) (entry : Entry) : Entry :=
  match query with
  | .inl _ => entry
  | .inr hash => ({ entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2)

set_option backward.isDefEq.respectTransparency false in
theorem local_forward (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : HashSpec.Domain) (entry : Entry) :
    (localImpl real decode c key (forwardIndex query)).run entry = (do
      let answer ← HashSpec.query query
      pure (forwardReply query answer, afterHash query entry)) := by
  cases real <;> cases query <;>
    simp [localImpl, forwardIndex, forwardReply, afterHash, AdaptiveCtxSharedHash.localImpl,
      AdaptiveCtxSharedReplay.localImpl, StateT.run]

theorem target_run (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : State) :
    (targetImpl real decode c key query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl ((localImpl real decode c key query).run state.1)).run state.2 := rfl

theorem hash_uniform_step (coin : Nat) (cache : CtxRO.QueryCache) :
    (hashImpl (.inl coin)).run cache =
      (fun answer => (answer, cache)) <$> (unifSpec.query coin : ProbComp _) := by
  change (do let answer ← unifSpec.query coin; pure (answer, cache) : ProbComp _) = _
  simp only [bind_pure_comp]

set_option backward.isDefEq.respectTransparency false in
theorem forward_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : State) (query : HashSpec.Domain) (shared : SharedState) :
    Prod.map id (replaceShared before) <$> (sharedImpl query).run shared =
      (simulateQ (targetImpl real decode c key) (forward query)).run (replaceShared before shared) := by
  cases query with
  | inl coin =>
      rw [forward, simulateQ_spec_query, target_run]
      have linked := local_forward real decode c key (.inl coin) (replaceShared before shared).1
      simp only [forwardIndex, forwardReply] at linked
      rw [linked]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
      rw [hash_uniform_step]
      simp [sharedImpl, StateT.run, replaceShared, afterHash]
  | inr hash =>
      rw [forward, simulateQ_spec_query, target_run]
      have linked := local_forward real decode c key (.inr hash) (replaceShared before shared).1
      simp only [forwardIndex, forwardReply] at linked
      rw [linked]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
      simp [sharedImpl, hashImpl, StateT.run, replaceShared, afterHash]

theorem forward_schedule (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : State) {Result : Type} (work : OracleComp HashSpec Result) (shared : SharedState) :
    Prod.map id (replaceShared before) <$> (simulateQ sharedImpl work).run shared =
      (simulateQ (targetImpl real decode c key) (simulateQ forward work)).run (replaceShared before shared) := by
  simpa only [QueryImpl.simulateQ_compose] using
    map_run_simulateQ_eq_of_query_map_eq sharedImpl (targetImpl real decode c key ∘ₛ forward)
      (replaceShared before) (forward_step real decode c key before) work shared

theorem forward_complete (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : State) {Result : Type} (work : OracleComp HashSpec Result) :
    (simulateQ (targetImpl real decode c key) (simulateQ forward work)).run before =
      Prod.map id (replaceShared before) <$>
        (simulateQ sharedImpl work).run (before.2, before.1.1.publicInputs) :=
  (forward_schedule real decode c key before work (before.2, before.1.1.publicInputs)).symm

def replaceEntryPublic (entry : Entry) (history : List Pqxdh.Bytes) : Entry :=
  ({ entry.1 with publicInputs := history }, entry.2)

set_option backward.isDefEq.respectTransparency false in
theorem local_public_history (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : Entry) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => replaceEntryPublic after (nextPublic query history)) <$>
      (localImpl real decode c key query).run entry =
      (localImpl real decode c key query).run (replaceEntryPublic entry history) := by
  cases real <;> rcases query with (coin | (hash | input)) | raw
  all_goals simp only [StateT.run, localImpl, Bool.false_eq_true, ite_false, ite_true,
    AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedReplay.localImpl]
  all_goals simp [replaceEntryPublic, nextPublic, AdaptiveCtxSharedHash.localSeal,
    AdaptiveCtxSharedReplay.localSeal, AdaptiveCtxSharedHash.localRaw, AdaptiveCtxSharedReplay.localRaw,
    AdaptiveCtxSharedReplay.localPrivate, AdaptiveCtxReplayDictionary.replayPlaintext,
    AdaptiveCtxSharedReplay.install]
  all_goals split <;> simp_all [Functor.map_map, Prod.map_def]

def replacePublic (state : State) (history : List Pqxdh.Bytes) : State :=
  (replaceEntryPublic state.1 history, state.2)

set_option backward.isDefEq.respectTransparency false in
theorem public_history_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (before : State) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => replacePublic after (nextPublic query history)) <$>
      (targetImpl real decode c key query).run before =
      (targetImpl real decode c key query).run (replacePublic before history) := by
  have full := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ hashImpl work).run before.2) (local_public_history real decode c key query before.1 history)
  simp only [simulateQ_map, StateT.run_map, Functor.map_map] at full
  rw [target_run, target_run]
  simpa only [replacePublic, replaceEntryPublic, Prod.map_def, id_eq, Functor.map_map] using full

def dismantle {Result : Type} (result : Result × State) : (Result × Entry) × CtxRO.QueryCache :=
  ((result.1, result.2.1), result.2.2)

theorem local_from_target (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : Entry) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl ((localImpl real decode c key query).run entry)).run cache =
      dismantle <$> (targetImpl real decode c key query).run (entry, cache) := by
  rw [target_run]
  simp only [Functor.map_map, dismantle]
  exact (id_map _).symm

end BeaconcryptCore.Computational.AdaptiveCtxSharedModes

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.canonical_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.canonical_initial

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_initial

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.real_view_eq

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.replay_view_eq

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_forward

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.target_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.hash_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.hash_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.forward_complete

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_public_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_public_history

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.public_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.public_history_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_from_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModes.local_from_target
