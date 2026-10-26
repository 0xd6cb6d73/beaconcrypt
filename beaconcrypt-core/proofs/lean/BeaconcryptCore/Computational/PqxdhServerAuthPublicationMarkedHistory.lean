import BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop

/-! Actual raw-attempt histories retain the publication flag at the request, independently of later publications. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory
open CtxRomAuth AdaptiveCtxReceive
open PqxdhServerAuthPublicationPrefixStop (Spec)
open PqxdhServerAuthPublicationGuess (Hit)
variable {Result : Type}

structure State where
  observer : RawCtxSelectedAuthenticationObserver.State
  published : Bool
  attempts : List (Bool × RawCtxSelectedAuthenticationObserver.Attempt)

def initialState : State := ⟨RawCtxSelectedAuthenticationObserver.initialState, false, []⟩

def step (query : Spec.Domain) (reply : Spec.Range query) (state : State) : State :=
  match query with
  | .inl (.inl (.inr raw)) =>
      { state with
        observer := RawCtxSelectedAuthenticationObserver.step (.inl (.inr raw)) reply state.observer
        attempts := (state.published, ⟨raw, reply, state.observer.seals⟩) :: state.attempts }
  | .inl query => { state with observer := RawCtxSelectedAuthenticationObserver.step query reply state.observer }
  | .inr flag => { state with published := state.published || flag }

noncomputable def observed (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT (State × AdaptiveCtxDynamicKnownKeys.SourceState) ProbComp) :=
  fun query state => match query with
  | .inl query => do
      let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key query).run state.2
      pure (reply.1, (step (.inl query) reply.1 state.1, reply.2))
  | .inr flag => pure ((), (step (.inr flag) () state.1, state.2))

def Raw (query : Spec.Domain) : Prop := match query with
  | .inl query => AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery query
  | .inr _ => False

def Seal (query : Spec.Domain) : Prop := match query with
  | .inl query => AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query
  | .inr _ => False

instance : DecidablePred Raw := by intro query; cases query <;> unfold Raw <;> infer_instance
instance : DecidablePred Seal := by intro query; cases query <;> unfold Seal <;> infer_instance

/-- A matching attempt records absence of publication at that request. Later markers do not alter this stored fact. -/
def Matched (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (state : State) : Prop :=
  ∃ attempt, (false, attempt) ∈ state.attempts ∧
    ∃ entry ∈ attempt.sealsBefore, Hit guess (some (entry.record, attempt.raw))

def Aligned (state : State) (saved : Option CtxRomRecord) : Prop :=
  state.attempts = [] ∧ PqxdhServerAuthPublicationCaptureHistory.Aligned state.observer saved

/-- A suffix with no selected raw request preserves every stored request-time marker, even if later markers become true. -/
theorem attempts_quiet (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp Spec Result) (quiet : work.IsQueryBoundP Raw 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run state)) :
    result.2.1.attempts = state.1.attempts := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
          simp only [observed, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
          obtain ⟨reply, _, supported⟩ := supported
          have tail := ih reply.1 (quiet.2 reply.1) _ result supported
          rw [tail]
          rcases query with ((coin | (input | request)) | raw) | known
          all_goals try rfl
          have bad := quiet.1
          simp only [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery,
            not_true_eq_false, Nat.lt_irrefl, or_self] at bad
      | inr flag =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
          simp only [observed, StateT.run, pure_bind] at supported
          simpa only [step] using ih () (quiet.2 ()) (step (.inr flag) () state.1, state.2) result supported

/-- No selected raw attempt is present in an aligned pre-capture state. -/
theorem matched_empty (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (state : State)
    (empty : state.attempts = []) : ¬ Matched guess state := by
  rintro ⟨attempt, member, _⟩
  simp only [empty, List.not_mem_nil] at member

/-- The marked matching event after the actual first raw request implies both a clean prefix and the exact saved tag hit. No optional plaintext condition is imposed. -/
theorem raw_match (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp Spec Result) (quiet : work.IsQueryBoundP Raw 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved) (raw : Pqxdh.Bytes) (plaintext : Option Pqxdh.Bytes)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run
      (step (.inl (.inl (.inr raw))) plaintext state.1, state.2)))
    (matched : Matched guess result.2.1) :
    state.1.published = false ∧ Hit guess (saved.map fun record => (record, raw)) := by
  have kept := attempts_quiet real decode crypto key work quiet _ result supported
  obtain ⟨attempt, member, entry, prior, hit⟩ := matched
  simp only [kept, step, aligned.1, List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨published, same⟩ := member
  subst attempt
  refine ⟨published.symm, ?_⟩
  rw [aligned.2.2 entry prior]
  exact hit

/-- The original selected seal response aligns the actual observer and saved record; its component effects and optional refusal remain unchanged. -/
theorem aligned_seal (state : State) (aligned : Aligned state none) (input : CtxSealInput)
    (reply : Option CtxRomRecord) :
    Aligned (step (.inl (.inl (.inl (.inr (.inr input))))) reply state) reply := by
  exact ⟨aligned.1, PqxdhServerAuthPublicationCaptureHistory.aligned_seal state.observer aligned.2 input reply⟩

/-- Full opening and its quiet continuation cannot increase the clean before-raw tag event. The probability is not conditioned on a writer or opening outcome. -/
theorem raw_probability (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp Spec Result)
    (quiet : ∀ reply, (next reply).IsQueryBoundP Raw 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved) :
    Pr{let result ← ((simulateQ (observed real decode crypto key)
        (do let reply ← Spec.query (.inl (.inl (.inr raw))); next reply)).run state)}[Matched guess result.2.1] ≤
    Pr{let result ← (pure ((state.1.published, saved.map fun record => (record, raw)), state.2) :
        ProbComp ((Bool × PqxdhServerAuthPublicationGuess.Candidate) × AdaptiveCtxDynamicKnownKeys.SourceState))}[result.1.1 = false ∧ Hit guess result.1.2] := by
  classical
  by_cases hit : state.1.published = false ∧ Hit guess (saved.map fun record => (record, raw))
  · simpa only [prEvent_pure, hit, and_self, ite_true] using
      ((prEvent_le_one _) : Pr{let result ← ((simulateQ (observed real decode crypto key)
          (do let reply ← Spec.query (.inl (.inl (.inr raw))); next reply)).run state)}[Matched guess result.2.1] ≤ 1)
  · simp only [prEvent_pure, hit, ite_false, nonpos_iff_eq_zero]
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported matched
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    simp only [observed, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, _, supported⟩ := supported
    exact hit (raw_match real decode crypto key guess (next reply.1) (quiet reply.1)
      (state.1, reply.2) saved aligned raw reply.1 result supported matched)

/-- The actual marked-attempt event is bounded by clean before-raw capture, retaining the publication flag at that exact request. The all-reply one-seal/one-raw caps supply first-occurrence uniqueness; no success or writer event is conditioned on. -/
theorem capture_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp Spec Result)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved)
    (sealBound : work.IsQueryBoundP Seal 1)
    (rawBound : work.IsQueryBoundP Raw 1)
    (noMore : saved ≠ none → work.IsQueryBoundP
      Seal 0) :
    Pr{let result ← (simulateQ (observed real decode crypto key) work).run state}[Matched guess result.2.1] ≤
    Pr{let result ← ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
        (PqxdhServerAuthPublicationPrefixStop.capture work saved state.1.published)).run state.2)}[result.1.1 = false ∧ Hit guess result.1.2] := by
  classical
  have prAssoc : ∀ {α β γ : Type} (x : ProbComp α) (f : α → ProbComp β) (g : β → ProbComp γ) (p : γ → Prop),
      Pr{let y ← (x >>= f >>= g)}[p y] = Pr{let y ← (x >>= fun a => f a >>= g)}[p y] := fun x f g p => by
    rw [bind_assoc x f g]
  induction work using OracleComp.inductionOn generalizing state saved with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, prEvent_pure, matched_empty guess state.1 aligned.1,
        ite_false] using (show (0 : ℝ≥0∞) ≤ _ from bot_le)
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff] at sealBound rawBound
      cases query with
      | inl query =>
          rcases query with ((coin | (input | request)) | raw) | known
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
            simp only [observed, StateT.run, prAssoc, pure_bind]
            change Pr{let result ← (do
              let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inl coin)))).run state.2
              (simulateQ (observed real decode crypto key) (next reply.1)).run (state.1, reply.2))}[Matched guess result.2.1] ≤
              Pr{let result ← (do
                let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inl coin)))).run state.2
                (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
                  (PqxdhServerAuthPublicationPrefixStop.capture (next reply.1) saved state.1.published)).run reply.2)}[result.1.1 = false ∧ Hit guess result.1.2]
            simp only [OracleComp.prEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            intro reply
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
            · simpa [Seal, AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
            · simpa [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
            · intro present
              have quiet := noMore present
              simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
              exact quiet.2 reply.1
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
            simp only [observed, StateT.run, prAssoc, pure_bind]
            change Pr{let result ← (do
              let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inr (.inl input))))).run state.2
              (simulateQ (observed real decode crypto key) (next reply.1)).run (state.1, reply.2))}[Matched guess result.2.1] ≤
              Pr{let result ← (do
                let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inr (.inl input))))).run state.2
                (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
                  (PqxdhServerAuthPublicationPrefixStop.capture (next reply.1) saved state.1.published)).run reply.2)}[result.1.1 = false ∧ Hit guess result.1.2]
            simp only [OracleComp.prEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            intro reply
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
            · simpa [Seal, AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
            · simpa [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
            · intro present
              have quiet := noMore present
              simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
              exact quiet.2 reply.1
          · have none : saved = none := by
              cases found : saved with
              | none => rfl
              | some record =>
                have quiet := noMore (by simp only [found, ne_eq, reduceCtorEq, not_false_eq_true])
                simp only [isQueryBoundP_query_bind_iff, Seal, AdaptiveCtxDynamicKnownBounds.TargetClass,
                  AdaptiveCtxQueryBounds.SourceSeal, Nat.lt_irrefl, not_true_eq_false, or_self, false_and] at quiet
            subst saved
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
            simp only [observed, StateT.run, prAssoc, pure_bind]
            change Pr{let result ← (do
              let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key
                (.inl (.inl (.inr (.inr request))))).run state.2
              (simulateQ (observed real decode crypto key) (next reply.1)).run
                (step (.inl (.inl (.inl (.inr (.inr request))))) reply.1 state.1, reply.2))}[Matched guess result.2.1] ≤
              Pr{let result ← (do
                let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key
                  (.inl (.inl (.inr (.inr request))))).run state.2
                (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
                  (PqxdhServerAuthPublicationPrefixStop.capture (next reply.1) reply.1 state.1.published)).run reply.2)}[result.1.1 = false ∧ Hit guess result.1.2]
            simp only [OracleComp.prEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            intro reply
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            have tailSeal : (next reply.1).IsQueryBoundP
                Seal 0 := by
              simpa only [Seal, AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal,
                ite_true, Nat.sub_self] using sealBound.2 reply.1
            refine ih reply.1 _ reply.1 (aligned_seal state.1 aligned request reply.1)
              (tailSeal.mono (by omega)) ?_ (fun _ => tailSeal)
            simpa [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
          · exact raw_probability real decode crypto key guess raw next
              (fun reply => by simpa only [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery, ite_true,
                Nat.sub_self] using rawBound.2 reply) state saved aligned
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
            simp only [observed, StateT.run, prAssoc, pure_bind]
            change Pr{let result ← (do
              let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inr known)).run state.2
              (simulateQ (observed real decode crypto key) (next reply.1)).run (state.1, reply.2))}[Matched guess result.2.1] ≤
              Pr{let result ← (do
                let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inr known)).run state.2
                (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
                  (PqxdhServerAuthPublicationPrefixStop.capture (next reply.1) saved state.1.published)).run reply.2)}[result.1.1 = false ∧ Hit guess result.1.2]
            simp only [OracleComp.prEvent_bind_eq_tsum]
            apply ENNReal.tsum_le_tsum
            intro reply
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
            · simpa [Seal, AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
            · simpa [Raw, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
            · intro present
              have quiet := noMore present
              simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
              exact quiet.2 reply.1


      | inr flag =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          simp only [observed, StateT.run, pure_bind]
          have tail := ih () (step (.inr flag) () state.1, state.2) saved
            ⟨aligned.1, aligned.2⟩
            (by simpa [Seal] using sealBound.2 ())
            (by simpa [Raw] using rawBound.2 ())
            (fun present => by
              have quiet := noMore present
              simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
              exact quiet.2 ())
          exact tail



/-- Erasing the extra request-time marker leaves exactly the original ordinary observer step. -/
theorem observer_step (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (reply : AdaptiveCtxDynamicKnownKeys.Spec.Range query) (state : State) :
    (step (.inl query) reply state).observer =
      RawCtxSelectedAuthenticationObserver.step query reply state.observer := by
  rcases query with ((coin | (input | request)) | raw) | known <;> rfl

/-- Full-state erasure retains every actual component reply and the entire ordinary record/attempt history. Private marker queries have no cryptographic effect. -/
theorem observer_erase (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp Spec Result) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, (result.2.1.observer, result.2.2))) <$>
      (simulateQ (observed real decode crypto key) work).run state =
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode crypto key)
      (simulateQ PqxdhServerAuthPublicationPrefixStop.erase work)).run (state.1.observer, state.2) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            PqxdhServerAuthPublicationPrefixStop.erase]
          simp only [observed, RawCtxSelectedAuthenticationObserver.observed, StateT.run,
            map_bind, bind_assoc, pure_bind]
          refine bind_congr fun reply => ?_
          simpa only [observer_step, StateT.run] using ih reply.1 (step (.inl query) reply.1 state.1, reply.2)
      | inr flag =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            PqxdhServerAuthPublicationPrefixStop.erase, pure_bind]
          simp only [observed, StateT.run, pure_bind]
          simpa only [step, StateT.run] using ih () (step (.inr flag) () state.1, state.2)

/-- The literal empty marked history discharges alignment, and the generic clean-prefix equality compares it to capture of the marker-killed program. -/
theorem initial_killed_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (work : OracleComp Spec Result)
    (sealBound : work.IsQueryBoundP Seal 1) (rawBound : work.IsQueryBoundP Raw 1) :
    Pr{let result ← (simulateQ (observed real decode crypto key) work).run (initialState, AdaptiveCtxDynamicKnownKeys.initialSource)}[Matched guess result.2.1] ≤
    Pr{let result ← ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
        (PqxdhServerAuthPublicationCaptureSource.dynamic
          (simulateQ PqxdhServerAuthPublicationPrefixStop.kill work).run none)).run
            AdaptiveCtxDynamicKnownKeys.initialSource)}[Hit guess result.1] := by
  have bound := capture_bound real decode crypto key guess work
    (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) none
    ⟨rfl, rfl, by simp [initialState, RawCtxSelectedAuthenticationObserver.initialState]⟩
    sealBound rawBound (fun impossible => (impossible rfl).elim)
  rw [show initialState.published = false from rfl,
    PqxdhServerAuthPublicationPrefixStop.clean_capture _ work none _
      (Hit guess) (by simp [Hit])] at bound
  exact bound

/-- The original uniformly sampled selected key and complete source state are shared by the marked observation. -/
noncomputable def sourceGame (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (work : OracleComp Spec Result) : ProbComp (Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState)) := do
  let key ← $ᵗ CtxKey
  (simulateQ (observed real decode crypto key) work).run (initialState, AdaptiveCtxDynamicKnownKeys.initialSource)

/-- Actual clean matching history is bounded by the marker-killed first-raw capture under the complete original selected-key experiment. Later publication is unrestricted. -/
theorem source_killed_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (work : OracleComp Spec Result)
    (sealBound : work.IsQueryBoundP Seal 1) (rawBound : work.IsQueryBoundP Raw 1) :
    Pr{let result ← sourceGame real decode crypto work}[Matched guess result.2.1] ≤
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic
          (simulateQ PqxdhServerAuthPublicationPrefixStop.kill work).run none))}[Hit guess result.1] := by
  simp only [sourceGame, AdaptiveCtxDynamicKnownKeys.sourceGame, OracleComp.prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro key
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact initial_killed_bound real decode crypto key guess work sealBound rawBound

def Target (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) : Spec.Domain → Prop
  | .inl query => predicate query
  | .inr _ => False

instance (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (Target predicate) := by
  intro query
  cases query <;> unfold Target <;> infer_instance

/-- Marker erasure preserves any original query-class cap exactly; deterministic annotations count as no component request. -/
theorem erase_bound (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop)
    [DecidablePred predicate] (work : OracleComp Spec Result) (bound : Nat) :
    work.IsQueryBoundP (Target predicate) bound ↔
      (simulateQ PqxdhServerAuthPublicationPrefixStop.erase work).IsQueryBoundP predicate bound := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationPrefixStop.erase,
            isQueryBoundP_query_bind_iff, Target, ih]
          rfl
      | inr flag =>
          simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationPrefixStop.erase,
            pure_bind, isQueryBoundP_query_bind_iff]
          change ((¬ False ∨ 0 < bound) ∧ ∀ u : Unit,
            (next u).IsQueryBoundP (Target predicate) (if False then bound - 1 else bound)) ↔ _
          simp only [not_false_eq_true, true_or, ite_false, true_and]
          constructor
          · intro bounded
            exact (ih () bound).mp (bounded ())
          · intro bounded u
            cases u
            exact (ih () bound).mpr bounded


/-- The marker history retains exactly the same actual attempts as the ordinary observer, in the same order. -/
def Coherent (state : State) : Prop := state.attempts.map Prod.snd = state.observer.attempts

/-- Every query retains the exact correspondence between the two actual attempt lists. -/
theorem coherent_step (query : Spec.Domain) (reply : Spec.Range query) (state : State)
    (coherent : Coherent state) : Coherent (step query reply state) := by
  cases query with
  | inl query =>
      rcases query with ((coin | (input | request)) | raw) | known
      · exact coherent
      · exact coherent
      · cases reply <;> exact coherent
      · simpa only [Coherent, step, RawCtxSelectedAuthenticationObserver.step, List.map_cons] using
          congrArg (List.cons (⟨raw, reply, state.observer.seals⟩ : RawCtxSelectedAuthenticationObserver.Attempt)) coherent
      · exact coherent
  | inr flag => exact coherent

/-- The complete adaptive interpretation preserves real attempt correspondence, with arbitrary initial marker histories allowed when aligned. -/
theorem coherent_program (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp Spec Result) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (coherent : Coherent state.1)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run state)) :
    Coherent result.2.1 := by
  apply simulateQ_run_preservesInv (observed real decode crypto key)
    (fun state => Coherent state.1) ?_ work state coherent result supported
  intro query state coherent result supported
  cases query with
  | inl query =>
      simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact coherent_step (.inl query) reply.1 state.1 coherent
  | inr flag =>
      simp only [observed, StateT.run, mem_support_pure_iff] at supported
      subst result
      exact coherent_step (.inr flag) () state.1 coherent

/-- All stored raw requests preceded publication; this constrains stored flags, not the current flag after later callbacks. -/
def Clean (state : State) : Prop := ∀ item ∈ state.attempts, item.1 = false

/-- A complete original component program contains no marker. From a clean unpublished state it retains clean stored attempts and the unchanged false publication flag. -/
theorem lifted_clean (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (clean : Clean state.1) (unpublished : state.1.published = false)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key)
      (simulateQ PqxdhServerAuthPublicationPrefixStop.liftDynamic work)).run state)) :
    Clean result.2.1 ∧ result.2.1.published = false := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨clean, unpublished⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationPrefixStop.liftDynamic,
        StateT.run_bind] at supported
      simp only [observed, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, supported⟩ := supported
      refine ih reply.1 (step (.inl query) reply.1 state.1, reply.2) ?_ ?_ result supported
      · rcases query with ((coin | (input | request)) | raw) | known
        all_goals try exact clean
        intro item member
        simp only [step, List.mem_cons] at member
        rcases member with rfl | member
        · exact unpublished
        · exact clean item member
      · rcases query with ((coin | (input | request)) | raw) | known <;> exact unpublished

/-- No-raw suffixes retain clean attempt-time flags through arbitrary later marker changes. -/
theorem quiet_clean (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp Spec Result) (quiet : work.IsQueryBoundP Raw 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (clean : Clean state.1)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run state)) :
    Clean result.2.1 := by
  have same := attempts_quiet real decode crypto key work quiet state result supported
  intro item member
  exact clean item (same ▸ member)

/-- Exact attempt correspondence and request-time cleanliness transfer the already proved ordinary matching receipt to the marked event. They make no claim about a later publication. -/
theorem matched_clean (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (state : State)
    (coherent : Coherent state) (clean : Clean state)
    (matched : PqxdhServerAuthPublicationCaptureHistory.Matched guess state.observer) :
    Matched guess state := by
  obtain ⟨attempt, member, entry, prior, hit⟩ := matched
  rw [← coherent, List.mem_map] at member
  obtain ⟨item, found, same⟩ := member
  have falseFlag := clean item found
  have itemEq : item = (false, attempt) := Prod.ext falseFlag same
  exact ⟨attempt, itemEq ▸ found, entry, prior, hit⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.attempts_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.attempts_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.matched_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.matched_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.raw_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.raw_match
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.aligned_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.aligned_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.raw_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.raw_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.capture_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.capture_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.observer_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.observer_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.observer_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.observer_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.initial_killed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.initial_killed_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.source_killed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.source_killed_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.erase_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.erase_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.coherent_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.coherent_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.coherent_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.coherent_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.lifted_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.lifted_clean
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.quiet_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.quiet_clean
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.matched_clean' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory.matched_clean
