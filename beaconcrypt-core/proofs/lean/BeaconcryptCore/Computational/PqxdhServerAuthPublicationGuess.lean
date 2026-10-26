import BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlindKnown
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag

/-! The concrete pre-raw observer retains the actual selected seal privately and extracts only the first requested raw bytes. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess
open CtxRomAuth AdaptiveCtxReceive
variable {Result : Type}

abbrev Candidate := Option (CtxRomRecord × Pqxdh.Bytes)

/-- Capture the exact latest selected record and first selected raw request. The latter is stopped before any decoder, lookup or opening query. The record is private observer state, never given to the source continuation. -/
noncomputable def capture (work : OracleComp ReceiveSpec Result) :
    Option CtxRomRecord → OracleComp ReceiveSpec Candidate :=
  OracleComp.recOn work
    (fun _ _ => pure none)
    (fun query _ recurse saved => match query with
      | .inr raw => pure (saved.map fun record => (record, raw))
      | .inl (.inr (.inr input)) => do
          let reply ← ReceiveSpec.query (.inl (.inr (.inr input)))
          recurse reply reply
      | query => do
          let reply ← ReceiveSpec.query query
          recurse reply saved)

/-- Stopping at a selected raw request retains only its exact bytes and the observer's actual earlier record. No challenger opening occurs. -/
theorem capture_raw (raw : Pqxdh.Bytes) (next : Option Pqxdh.Bytes → OracleComp ReceiveSpec Result)
    (saved : Option CtxRomRecord) :
    capture (liftM (ReceiveSpec.query (.inr raw)) >>= next) saved =
      pure (saved.map fun record => (record, raw)) := rfl

/-- Extract the first selected raw request without issuing it, forwarding every preceding actual query and reply. -/
noncomputable def raw (work : OracleComp ReceiveSpec Result) : OracleComp ReceiveSpec (Option Pqxdh.Bytes) :=
  OracleComp.recOn work
    (fun _ => pure none)
    (fun query _ recurse => match query with
      | .inr bytes => pure (some bytes)
      | query => do
          let reply ← ReceiveSpec.query query
          recurse reply)

/-- No selected raw request is forwarded by the actual request extractor. -/
theorem raw_no_raw (work : OracleComp ReceiveSpec Result) :
    (raw work).IsQueryBoundP IsRawQuery 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin)); raw (next reply) : OracleComp ReceiveSpec (Option Pqxdh.Bytes)).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); raw (next reply) : OracleComp ReceiveSpec (Option Pqxdh.Bytes)).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request))); raw (next reply) : OracleComp ReceiveSpec (Option Pqxdh.Bytes)).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · change (pure (some bytes) : OracleComp ReceiveSpec _).IsQueryBoundP IsRawQuery 0
      trivial

/-- The concrete raw-request extractor preserves every all-reply query certificate, including weighted plaintext and separate uniform/hash budgets. -/
theorem raw_budget {Budget : Type} (work : OracleComp ReceiveSpec Result)
    (canQuery : ReceiveSpec.Domain → Budget → Prop)
    (cost : ReceiveSpec.Domain → Budget → Budget) (budget : Budget)
    (bounded : work.IsQueryBound budget canQuery cost) :
    (raw work).IsQueryBound budget canQuery cost := by
  induction work using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [isQueryBound_query_bind_iff] at bounded
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin)); raw (next reply) : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); raw (next reply) : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request))); raw (next reply) : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
    · trivial

/-- Pair a private actual record with the actual first raw request, if both occurred. -/
def pair (saved : Option CtxRomRecord) (bytes : Option Pqxdh.Bytes) : Candidate :=
  saved.bind fun record => bytes.map fun value => (record, value)

/-- A suffix with no selected seals cannot change the private captured record. Its actual raw candidate is obtained by the query-preserving extractor. -/
theorem capture_quiet (work : OracleComp ReceiveSpec Result)
    (bounded : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0) (saved : Option CtxRomRecord) :
    capture work saved = pair saved <$> raw work := by
  induction work using OracleComp.inductionOn with
  | pure value => cases saved <;> rfl
  | query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at bounded
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin)); capture (next reply) saved : OracleComp ReceiveSpec Candidate) =
        pair saved <$> (do let reply ← ReceiveSpec.query (.inl (.inl coin)); raw (next reply) : OracleComp ReceiveSpec (Option Pqxdh.Bytes))
      rw [map_bind]
      exact bind_congr fun reply => ih reply (bounded.2 reply)
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); capture (next reply) saved : OracleComp ReceiveSpec Candidate) =
        pair saved <$> (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); raw (next reply) : OracleComp ReceiveSpec (Option Pqxdh.Bytes))
      rw [map_bind]
      exact bind_congr fun reply => ih reply (bounded.2 reply)
    · exact False.elim (bounded.1 trivial)
    · cases saved <;> rfl

open PqxdhServerAuthPublicationPrivateView

/-- The actual private captured record and first raw candidate are exactly the corresponding projection of the complete first-seal/suffix experiment. No writer or success event is conditioned upon. -/
theorem first_capture_source (decode : RawDecoder) (input : CtxSealInput) (state : State)
    (work : OracleComp ReceiveSpec Result) (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0) :
    (do let sealed ← step decode (.inl (.inr (.inr input))) state
        let final ← (simulateQ (impl decode) (capture work sealed.1)).run sealed.2
        pure final.1) =
      (fun result => pair result.1 result.2.1) <$>
        (do let sealed ← step decode (.inl (.inr (.inr input))) state
            let final ← Prod.map id project <$> (simulateQ (impl decode) (raw work)).run sealed.2
            pure (sealed.1, final)) := by
  simp only [map_bind, bind_pure_comp]
  apply bind_congr
  intro sealed
  rw [capture_quiet work noSeal, simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- The target event uses the actual private record and the tag parsed from the first raw candidate. Missing either value is not a hit. -/
def Hit (guess : Pqxdh.Bytes → Option (FixedBytes 16)) : Candidate → Prop
  | none => False
  | some (record, bytes) => guess bytes = some ⟨record.tag, record.tagLength⟩

/-- The capture observation is exactly the existing optional-record tag event, without a successful-writer predicate. -/
theorem hit_pair (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (saved : Option CtxRomRecord) (bytes : Option Pqxdh.Bytes) (state : State) :
    Hit guess (pair saved bytes) =
      PqxdhServerAuthPublicationTag.Hit (fun candidate : Option Pqxdh.Bytes => candidate.bind guess)
        (saved, (bytes, state)) := by
  cases saved <;> cases bytes <;> simp [Hit, pair, PqxdhServerAuthPublicationTag.Hit]

/-- The actual captured first-seal record and pre-raw candidate have the unconditional tag bound in the ordinary random game. Every source/public draw in the quiet suffix is retained. -/
theorem first_capture_bound (decode : RawDecoder) (input : CtxSealInput) (state : State)
    (unused : Unused state) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) :
    Pr{let x ← (do
      let sealed ← step decode (.inl (.inr (.inr input))) state
      let final ← (simulateQ (impl decode) (capture work sealed.1)).run sealed.2
      pure final.1)}[(Hit guess) x] ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [first_capture_source decode input state work noSeal, prEvent_map]
  have bounded := PqxdhServerAuthPublicationTag.first_seal_guess decode input state unused (raw work)
    (raw_budget work _ _ _ noSeal) (raw_no_raw work)
    (fun candidate : Option Pqxdh.Bytes => candidate.bind guess)
  refine (prEvent_mono_of_support _ _ _ ?_).trans bounded
  intro result _ hit
  exact Eq.mp (hit_pair guess result.1 result.2.1 result.2.2) hit

/-- A quiet suffix starting without a captured record cannot win, regardless of its actual raw request or private/public state. Its work is still executed. -/
theorem capture_none (decode : RawDecoder) (state : State) (work : OracleComp ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) :
    Pr{let x ← Prod.fst <$> (simulateQ (impl decode) (capture work none)).run state}[(Hit guess) x] = 0 := by
  rw [capture_quiet work noSeal]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, prEvent_map, pair, Option.bind_none, Hit, prEvent_false]

/-- After the first selected request, the executable continuation sees only the fixed replacement. Both actual refusal and successful records are retained by the private observer; no writer outcome is conditioned on. -/
theorem first_scrub_bound (decode : RawDecoder) (input : CtxSealInput) (state : State)
    (unused : Unused state) (replacement : CtxRomRecord)
    (next : Option CtxRomRecord → OracleComp ReceiveSpec Result)
    (noSeal : ∀ reply, (next reply).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) :
    Pr{let x ← (do
      let sealed ← step decode (.inl (.inr (.inr input))) state
      let final ← (simulateQ (impl decode) (capture
        (simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement)
          (next (sealed.1.map fun _ => replacement))) sealed.1)).run sealed.2
      pure final.1)}[(Hit guess) x] ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  have quiet : ∀ reply, simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement) (next reply) = next reply :=
    fun reply => PqxdhServerAuthPublicationBlindKnown.quiet replacement _ (noSeal reply)
  simp_rw [quiet]
  have mapFst : ∀ work : ProbComp (Candidate × State),
      Pr{let x ← (work >>= fun final => pure final.1)}[Hit guess x] = Pr{let x ← Prod.fst <$> work}[Hit guess x] :=
    fun work => by rw [bind_pure_comp Prod.fst work]
  have same :
      Pr{let x ← (do
        let sealed ← step decode (.inl (.inr (.inr input))) state
        let final ← (simulateQ (impl decode) (capture (next (sealed.1.map fun _ => replacement)) sealed.1)).run sealed.2
        pure final.1)}[(Hit guess) x] =
      Pr{let x ← (do
        let sealed ← step decode (.inl (.inr (.inr input))) state
        let final ← (simulateQ (impl decode) (capture (next (some replacement)) sealed.1)).run sealed.2
        pure final.1)}[(Hit guess) x] := by
    refine prEvent_bind_congr _ _ _ _ _ fun sealed => ?_
    cases sealed.1 with
    | some record => simp only [Option.map_some]
    | none => rw [mapFst, mapFst, capture_none decode _ _ (noSeal _) guess, capture_none decode _ _ (noSeal _) guess]
  rw [same]
  exact first_capture_bound decode input state unused (next (some replacement)) (noSeal _) guess

set_option maxHeartbeats 400000 in
/-- Every adaptive prefix retains the actual unused selected state until its first seal. The concrete before-raw observer against the scrubbed continuation has one unconditional tag-guess charge, without selecting a successful attempt. -/
theorem scrub_capture_bound (decode : RawDecoder) (replacement : CtxRomRecord)
    (work : OracleComp ReceiveSpec Result)
    (bounded : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1)
    (state : State) (unused : Unused state)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) :
    Pr{let x ← (Prod.fst <$> (simulateQ (impl decode)
      (capture (simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement) work) none)).run state)}[(Hit guess) x] ≤
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  have pureMap : ∀ {α β : Type} (mx : ProbComp α) (f : α → β) (p : β → Prop),
      Pr{let y ← (mx >>= fun a => pure (f a))}[p y] = Pr{let a ← mx}[p (f a)] := fun mx f p => by
    rw [bind_pure_comp f mx, prEvent_map]
  have bindCongr : ∀ {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ) (p : β → Prop)
      (q : γ → Prop), (∀ x, Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) →
        Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] :=
    fun mx f g p q h => prEvent_bind_congr mx f g p q h
  simp only [prEvent_map]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    change Pr{let result ← (pure (none, state) : ProbComp _)}[Hit guess result.1] ≤ _
    simp only [prEvent_pure, Hit, ite_false, zero_le]
  | query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff] at bounded
    rcases query with ((coin | (input | request)) | bytes)
    all_goals simp only [simulateQ_bind, simulateQ_spec_query,
      PqxdhServerAuthPublicationBlindKnown.scrub, bind_assoc, pure_bind]
    · change Pr{let result ← ((simulateQ (impl decode) (do
          let reply ← ReceiveSpec.query (.inl (.inl coin))
          capture (simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement) (next reply)) none)).run state)}[Hit guess result.1] ≤ _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer reached
      apply ih answer.1 (by simpa [AdaptiveCtxQueryBounds.SourceSeal] using bounded.2 answer.1) answer.2
      exact quiet_unused decode _ state (by simp [AdaptiveCtxQueryBounds.SourceSeal])
        (by simp [IsRawQuery]) unused answer reached
    · change Pr{let result ← ((simulateQ (impl decode) (do
          let reply ← ReceiveSpec.query (.inl (.inr (.inl input)))
          capture (simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement) (next reply)) none)).run state)}[Hit guess result.1] ≤ _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer reached
      apply ih answer.1 (by simpa [AdaptiveCtxQueryBounds.SourceSeal] using bounded.2 answer.1) answer.2
      exact quiet_unused decode _ state (by simp [AdaptiveCtxQueryBounds.SourceSeal])
        (by simp [IsRawQuery]) unused answer reached
    · change Pr{let result ← ((simulateQ (impl decode) (do
          let reply ← ReceiveSpec.query (.inl (.inr (.inr request)))
          capture (simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement)
            (next (reply.map fun _ => replacement))) reply)).run state)}[Hit guess result.1] ≤ _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have bound := first_scrub_bound decode request state unused replacement next
        (fun reply => by simpa [AdaptiveCtxQueryBounds.SourceSeal] using bounded.2 reply) guess
      simp only [impl, StateT.run] at bound ⊢
      refine le_of_eq_of_le ?_ bound
      refine bindCongr _ _ _ _ _ fun sealed => ?_
      exact (pureMap _ Prod.fst (Hit guess)).symm
    · change Pr{let result ← (pure (none, state) : ProbComp _)}[Hit guess result.1] ≤ _
      simp only [prEvent_pure, Hit, ite_false, zero_le]

/-- A proved syntactic replacement equality discharges the fixed-reply condition of the actual adaptive capture bound. This helper is instantiated by the complete concrete reference, not treated as a primitive security assumption. -/
theorem blind_capture_bound (decode : RawDecoder) (replacement : CtxRomRecord)
    (work : OracleComp ReceiveSpec Result)
    (bounded : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1)
    (blind : simulateQ (PqxdhServerAuthPublicationBlindKnown.scrub replacement) work = work)
    (state : State) (unused : Unused state)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) :
    Pr{let x ← Prod.fst <$> (simulateQ (impl decode) (capture work none)).run state}[(Hit guess) x] ≤
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  simpa only [blind] using scrub_capture_bound decode replacement work bounded state unused guess

/-- Every complete capture preserves the original all-reply component budget while retaining its actual private record. This includes weighted plaintext bytes. -/
theorem capture_budget {Budget : Type} (work : OracleComp ReceiveSpec Result)
    (canQuery : ReceiveSpec.Domain → Budget → Prop)
    (cost : ReceiveSpec.Domain → Budget → Budget) (budget : Budget)
    (bounded : work.IsQueryBound budget canQuery cost) (saved : Option CtxRomRecord) :
    (capture work saved).IsQueryBound budget canQuery cost := by
  induction work using OracleComp.inductionOn generalizing budget saved with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [isQueryBound_query_bind_iff] at bounded
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin)); capture (next reply) saved : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply) saved⟩
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); capture (next reply) saved : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply) saved⟩
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request))); capture (next reply) reply : OracleComp ReceiveSpec _).IsQueryBound budget canQuery cost
      rw [isQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply) reply⟩
    · trivial

/-- The actual captured-record observer never issues a selected raw request, including malformed inputs. -/
theorem capture_no_raw (work : OracleComp ReceiveSpec Result) (saved : Option CtxRomRecord) :
    (capture work saved).IsQueryBoundP IsRawQuery 0 := by
  induction work using OracleComp.inductionOn generalizing saved with
  | pure value => trivial
  | query_bind query next ih =>
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin)); capture (next reply) saved : OracleComp ReceiveSpec Candidate).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); capture (next reply) saved : OracleComp ReceiveSpec Candidate).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request))); capture (next reply) reply : OracleComp ReceiveSpec Candidate).IsQueryBoundP IsRawQuery 0
      simp [IsRawQuery, ih]
    · trivial

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_raw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_raw
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.raw_no_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.raw_no_raw
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.raw_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.raw_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_capture_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_capture_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.hit_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.hit_pair
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_capture_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_capture_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_none
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_scrub_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.first_scrub_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.scrub_capture_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.scrub_capture_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.blind_capture_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.blind_capture_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_no_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess.capture_no_raw
