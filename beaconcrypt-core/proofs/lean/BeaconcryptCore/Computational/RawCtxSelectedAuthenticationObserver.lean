import BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift

/-!
The selected record-authentication observer sees only actual selected oracle requests and their replies. It retains each raw attempt's unchanged component request bytes, challenger-produced optional plaintext and preceding honest-seal history. Its winning decision checks accepted full-tuple freshness using that attempt-time history; it never supplies a recovered plaintext in a forgery target or receives a selected-key argument.
-/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver
open CtxRomAuth AdaptiveCtxReceive
open AdaptiveCtxDynamicKnownKeys (Spec)

structure Attempt where
  raw : Pqxdh.Bytes
  plaintext : Option Pqxdh.Bytes
  sealsBefore : List CtxSuccessfulSeal

structure State where
  seals : List CtxSuccessfulSeal
  attempts : List Attempt

def initialState : State := ⟨[], []⟩

def replayed (history : List CtxSuccessfulSeal) (target : CtxUnclaimedAcceptance.Target) : Option Pqxdh.Bytes :=
  (history.find? (fun entry => decide (target.nonce = entry.input.nonce ∧ target.context.ad = entry.input.context.ad ∧ target.record.encode = entry.record.encode))).map
    (fun entry => entry.input.plaintext)

def accepted (decode : RawDecoder) (attempt : Attempt) : Bool :=
  match decode attempt.raw with
  | none => false
  | some target => attempt.plaintext.isSome && (replayed attempt.sealsBefore target).isNone

def won (decode : RawDecoder) (state : State) : Bool := state.attempts.any (accepted decode)

def step (query : Spec.Domain) (reply : Spec.Range query) (state : State) : State :=
  match query with
  | .inl (.inl (.inr (.inr input))) => match reply with
      | none => state
      | some record => { state with seals := ⟨input, record⟩ :: state.seals }
  | .inl (.inr raw) => { state with attempts := ⟨raw, reply, state.seals⟩ :: state.attempts }
  | _ => state

def handler : QueryImpl Spec (StateT State (OracleComp Spec)) := fun query state => do
  let reply ← Spec.query query
  pure (reply, step query reply state)

noncomputable def monitor {Result : Type} (client : OracleComp Spec Result) (state : State) : OracleComp Spec (Result × State) :=
  (simulateQ handler client).run state

noncomputable def decision {Result : Type} (decode : RawDecoder) (client : OracleComp Spec Result) : OracleComp Spec Bool :=
  (fun result => won decode result.2) <$> monitor client initialState

/-- The computed replay lookup uses precisely the full CTX authentication tuple of the existing integrity endpoint. -/
theorem replayed_none (history : List CtxSuccessfulSeal) (target : CtxUnclaimedAcceptance.Target) :
    replayed history target = none ↔ ∀ entry ∈ history, ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  simp [replayed, CtxAliasTarget.sameFullTupleAsSuccessfulSeal, CtxUnclaimedAcceptance.Target.toLegacy]

/-- Every raw attempt keeps the original input and actual optional reply before the adaptive continuation is resumed. -/
theorem raw_step (raw : Pqxdh.Bytes) (plaintext : Option Pqxdh.Bytes) (state : State) :
    step (.inl (.inr raw)) plaintext state =
      { state with attempts := ⟨raw, plaintext, state.seals⟩ :: state.attempts } := rfl

/-- The final observer checks only parsed ciphertext fields, the actual present optional reply, and the honest sealing history before that attempt. -/
theorem accepted_iff (decode : RawDecoder) (attempt : Attempt) :
    accepted decode attempt = true ↔ ∃ target, decode attempt.raw = some target ∧
      attempt.plaintext ≠ none ∧ ∀ entry ∈ attempt.sealsBefore, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  cases parsed : decode attempt.raw with
  | none => simp [accepted, parsed]
  | some target =>
    cases plaintext : attempt.plaintext <;> simp [accepted, parsed, plaintext, replayed_none]

/-- The observer wins exactly when its actual accepted-attempt history contains a full-tuple-fresh selected opening. -/
theorem won_iff (decode : RawDecoder) (state : State) :
    won decode state = true ↔ ∃ attempt ∈ state.attempts, ∃ target, decode attempt.raw = some target ∧
      attempt.plaintext ≠ none ∧ ∀ entry ∈ attempt.sealsBefore, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  simp only [won, List.any_eq_true, accepted_iff]

/-- Erasing only the observer returns the exact original executable program, before choosing any component game. -/
theorem monitor_erase {Result : Type} (client : OracleComp Spec Result) (state : State) :
    Prod.fst <$> monitor client state = client := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [monitor, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [handler, StateT.run, map_bind, pure_bind, bind_assoc]
    exact bind_congr fun reply => ih reply (step query reply state)

/-- The only executable effect added at a request is its deterministic observation after the actual reply. -/
theorem monitor_query {Result : Type} (query : Spec.Domain) (continuation : Spec.Range query → OracleComp Spec Result) (state : State) :
    monitor (liftM (Spec.query query) >>= continuation) state =
      (do let reply ← Spec.query query; monitor (continuation reply) (step query reply state)) := by
  simp only [monitor, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [handler, StateT.run, pure_bind, bind_assoc]

/-- Instrumentation preserves every explicit query predicate and cap exactly, including all attempted raw requests. -/
theorem monitor_queries {Result : Type} (predicate : Spec.Domain → Prop) [DecidablePred predicate]
    (client : OracleComp Spec Result) (state : State) (bound : Nat) :
    (monitor client state).IsQueryBoundP predicate bound ↔ client.IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [monitor_query, isQueryBoundP_query_bind_iff, ih]

/-- Computing the final forgery bit adds no oracle calls in any source resource class. -/
theorem decision_queries {Result : Type} (decode : RawDecoder) (predicate : Spec.Domain → Prop) [DecidablePred predicate]
    (client : OracleComp Spec Result) (bound : Nat) :
    (decision decode client).IsQueryBoundP predicate bound ↔ client.IsQueryBoundP predicate bound := by
  simp only [decision, isQueryBoundP_map_iff, monitor_queries]

/-- A replay-only reply cannot satisfy the observer's full-tuple-fresh acceptance test. -/
theorem replay_not_accepted (decode : RawDecoder) (raw : Pqxdh.Bytes) (history : List CtxSuccessfulSeal) :
    accepted decode ⟨raw, (decode raw).bind (replayed history), history⟩ = false := by
  cases parsed : decode raw with
  | none => simp [accepted, parsed]
  | some target =>
    cases found : replayed history target <;> simp [accepted, parsed, found]

noncomputable def observed (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT (State × AdaptiveCtxDynamicKnownKeys.SourceState) ProbComp) := fun query state => do
  let result ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key query).run state.2
  pure (result.1, (step query result.1 state.1, result.2))

def ReplayGood (decode : RawDecoder) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  state.1.seals = state.2.selected.1.successfulSeals ∧ won decode state.1 = false

/-- A concrete replay raw callback preserves the observed seal history and cannot add a fresh accepted attempt, including malformed inputs and all private-cache effects. -/
theorem replay_raw_good (decode : RawDecoder) (raw : Pqxdh.Bytes) (before : State)
    (entry : AdaptiveCtxSharedReplay.Local) (cache : CtxRO.QueryCache)
    (aligned : before.seals = entry.1.successfulSeals) (good : won decode before = false)
    (result : (Option Pqxdh.Bytes × AdaptiveCtxSharedReplay.Local) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      (AdaptiveCtxSharedReplay.localRaw decode raw entry)).run cache)) :
    (step (.inl (.inr raw)) result.1.1 before).seals = result.1.2.1.successfulSeals ∧
      won decode (step (.inl (.inr raw)) result.1.1 before) = false := by
  cases parsed : decode raw with
  | none =>
    simp only [AdaptiveCtxSharedReplay.localRaw, parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    constructor
    · exact aligned
    · change (accepted decode ⟨raw, none, before.seals⟩ || won decode before) = false
      rw [good]
      simp [accepted, parsed]
  | some target =>
    simp only [AdaptiveCtxSharedReplay.localRaw, parsed, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨commitment, reached, rfl⟩
    simp only [AdaptiveCtxSharedReplay.localPrivate, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨lookup, _, rfl⟩
    have rejected := replay_not_accepted decode raw entry.1.successfulSeals
    rw [parsed, Option.bind_some] at rejected
    constructor
    · exact aligned
    · change (accepted decode ⟨raw, replayed entry.1.successfulSeals target, before.seals⟩ || won decode before) = false
      rw [aligned, rejected, good]
      rfl

/-- Successful seals extend both actual and observed histories in the same order; nonce refusal changes neither history, and later seals cannot change an earlier attempt's stored freshness history. -/
theorem replay_seal_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) (before : State)
    (entry : AdaptiveCtxSharedReplay.Local) (cache : CtxRO.QueryCache)
    (aligned : before.seals = entry.1.successfulSeals) (good : won decode before = false)
    (result : (Option CtxRomRecord × AdaptiveCtxSharedReplay.Local) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      (AdaptiveCtxSharedReplay.localSeal c key input entry)).run cache)) :
    (step (.inl (.inl (.inr (.inr input)))) result.1.1 before).seals = result.1.2.1.successfulSeals ∧
      won decode (step (.inl (.inl (.inr (.inr input)))) result.1.1 before) = false := by
  by_cases used : input.nonce ∈ entry.1.usedNonces
  · simp only [AdaptiveCtxSharedReplay.localSeal, used, ite_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨aligned, good⟩
  · simp only [AdaptiveCtxSharedReplay.localSeal, used, ite_false, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨commitment, reached, rfl⟩
    simp only [AdaptiveCtxSharedReplay.localPrivate, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨lookup, _, rfl⟩
    constructor
    · simp only [step, aligned]
    · exact good

private theorem state_bind_apply {X Y σ : Type} {m : Type → Type} [Monad m]
    (head : StateT σ m X) (tail : X → StateT σ m Y) (state : σ) :
    (head >>= tail) state = (head state >>= fun result => tail result.1 result.2) := rfl

/-- Every concrete selected or known-key source operation preserves exact observer alignment and zero fresh acceptance in replay mode. -/
theorem replay_step_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : Spec.Domain) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : ReplayGood decode state) (result : Spec.Range query × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((observed false decode c key query).run state)) :
    ReplayGood decode result.2 := by
  simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨actual, reached, rfl⟩
  cases query with
  | inr known =>
    simp only [AdaptiveCtxDynamicKnownKeys.sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨localResult, _, rfl⟩
    exact good
  | inl request =>
    simp only [AdaptiveCtxDynamicKnownKeys.sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨localResult, localReached, rfl⟩
    simp only [AdaptiveCtxSharedModes.localImpl, Bool.false_eq_true, ite_false] at localReached
    cases request with
    | inr raw => exact replay_raw_good decode raw state.1 state.2.selected state.2.cache good.1 good.2 localResult localReached
    | inl primitive =>
      cases primitive with
      | inl coin =>
        simp only [AdaptiveCtxSharedReplay.localImpl, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
          state_bind_apply, mem_support_bind_iff] at localReached
        rcases localReached with ⟨answer, _, rfl⟩
        exact good
      | inr primitive =>
        cases primitive with
        | inl hash =>
          simp only [AdaptiveCtxSharedReplay.localImpl, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
            state_bind_apply, mem_support_bind_iff] at localReached
          rcases localReached with ⟨answer, _, rfl⟩
          exact good
        | inr input => exact replay_seal_good decode c key input state.1 state.2.selected state.2.cache good.1 good.2 localResult localReached

/-- The exact zero-forgery invariant holds through every adaptive replay-mode continuation, retaining the full observer, selected, known-key and cache states. -/
theorem replay_schedule_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp Spec Result) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : ReplayGood decode state) (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed false decode c key) client).run state)) :
    ReplayGood decode result.2 := by
  exact simulateQ_run_preservesInv (observed false decode c key) (ReplayGood decode)
    (replay_step_good decode c key) client state good result supported

/-- The published component endpoint starts with the same empty sealing and attempted-opening histories. -/
theorem initial_good (decode : RawDecoder) :
    ReplayGood decode (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) := by
  exact ⟨rfl, rfl⟩

/-- The observed full-state interpreter is exactly the executable monitor under the original component interpreter. -/
theorem monitored_program (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp Spec Result) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (monitor client state.1)).run state.2 =
      (simulateQ (observed real decode c key) client).run state := by
  have handlerLaw : (fun query => PqxdhSelectedStateInterpreter.evaluate
      (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (handler query)) = observed real decode c key := by
    funext query before
    simp only [PqxdhSelectedStateInterpreter.evaluate, observed]
    change PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key)
        (do let reply ← Spec.query query; pure (reply, step query reply before.1))).run before.2 = _
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, map_bind, map_pure, PqxdhSelectedStateInterpreter.pair]
  have law := congrFun (PqxdhSelectedStateInterpreter.program
    (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) handler client) state
  rw [handlerLaw] at law
  exact law

/-- The primitive-game Boolean is the same deterministic decision over the retained actual attempted-opening history. -/
theorem decision_interpreted (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp Spec Result) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (decision decode client)).run state =
      (fun result => won decode result.2.1) <$>
        (simulateQ (observed real decode c key) client).run (initialState, state) := by
  have law := congrArg (fun work => (fun result => won decode result.2.1) <$> work)
    (monitored_program real decode c key client (initialState, state))
  simpa only [decision, simulateQ_map, StateT.run_map, Functor.map_map, PqxdhSelectedStateInterpreter.pair] using law

/-- The concrete final observer never wins in the replay endpoint, for every sampled selected key and every adaptive client. -/
theorem replay_zero (decode : RawDecoder) (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp Spec Result) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame false decode c (decision decode client)] {true} = 0 := by
  rw [← prEvent_eq_evalDist_singleton]
  apply prEvent_eq_zero_of_not_mem_support
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, map_bind, decision_interpreted,
    mem_support_bind_iff, support_map, Set.mem_image]
  rintro ⟨key, _, result, reached, winning⟩
  have impossible := (replay_schedule_good decode c key client
    (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) (initial_good decode) result reached).2
  rw [impossible] at winning
  exact Bool.false_ne_true winning

open AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxSharedReplayBounds
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The concrete executable accepted-attempt observer has the existing ordinary validation, attempt-indexed modified INT-CTXT and explicit CTX guessing losses. No private-state winner or new simulation premise is introduced. -/
theorem authentication_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type} (client : OracleComp Spec Result)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c (decision decode client)] {true} ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c
          (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision decode client)) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
          (AdaptiveCtxReceive.wrapped decode (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision decode client))) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  have difference := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage
    (Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c (decision decode client))
    (Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame false decode c (decision decode client))
  have zero := replay_zero decode c client
  rw [zero, zero_add] at difference
  exact difference.trans (selected_integrity decode c fallback (decision decode client) qHash qSeal qRaw
    ((decision_queries decode HashRoute client qHash).mpr hashBound)
    ((decision_queries decode (TargetClass SourceSeal) client qSeal).mpr sealBound)
    ((decision_queries decode (TargetClass IsRawQuery) client qRaw).mpr rawBound) small)

end BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replayed_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replayed_none

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.raw_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.raw_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.accepted_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.accepted_iff

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.won_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.won_iff

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_query

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_queries' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitor_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.decision_queries' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.decision_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_not_accepted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_not_accepted

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_raw_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_raw_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_seal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_seal_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_step_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_schedule_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.initial_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.initial_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitored_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.monitored_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.decision_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.decision_interpreted

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.replay_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver.authentication_bound
