import BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler

/-! Ordered selected record and raw prefix from the actual all-attempt observer. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory
open CtxRomAuth AdaptiveCtxReceive
open RawCtxSelectedAuthenticationObserver
open PqxdhServerAuthPublicationGuess (Hit)
variable {Result : Type}

/-- A retained actual attempt matches the tag of a record in that attempt's earlier seal history. -/
def Matched (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (state : State) : Prop :=
  ∃ attempt ∈ state.attempts, ∃ entry ∈ attempt.sealsBefore, Hit guess (some (entry.record, attempt.raw))

/-- Zero selected raw requests preserve every actual earlier attempt, even through selected sealing and arbitrary known-key work. -/
theorem attempts_quiet (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (quiet : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run state)) :
    result.2.1.attempts = state.1.attempts := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
      have bounds := quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [observed, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, supported⟩ := supported
      have tail := ih reply.1 (by simpa using bounds.2 reply.1) _ result supported
      rw [tail]
      rcases query with ((coin | (input | request)) | raw) | known
      · rfl
      · rfl
      · cases reply.1 <;> rfl
      · have bad := bounds.1
        simp only [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery, not_true_eq_false, Nat.lt_irrefl, or_self] at bad
      · rfl

/-- The empty attempt list cannot contain a matched raw request. -/
theorem matched_empty (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (state : State)
    (empty : state.attempts = []) : ¬ Matched guess state := by
  rintro ⟨attempt, member, _⟩
  simp only [empty, List.not_mem_nil] at member

/-- At the first raw request, every possible earlier matching entry has exactly the saved record. This is an ordered-history condition, not a byte-origin reconstruction. -/
def Aligned (state : State) (saved : Option CtxRomRecord) : Prop :=
  state.attempts = [] ∧ ∀ entry ∈ state.seals, saved = some entry.record

/-- A quiet post-raw continuation can retain a matched event only if the exact pre-raw candidate already has the captured tag. The actual optional plaintext reply is unrestricted. -/
theorem raw_match (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (quiet : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved) (raw : Pqxdh.Bytes) (plaintext : Option Pqxdh.Bytes)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed real decode crypto key) work).run
      (step (.inl (.inr raw)) plaintext state.1, state.2)))
    (matched : Matched guess result.2.1) : Hit guess (saved.map fun record => (record, raw)) := by
  have kept := attempts_quiet real decode crypto key work quiet _ result supported
  obtain ⟨attempt, member, entry, prior, hit⟩ := matched
  simp only [kept, step, aligned.1, List.mem_singleton] at member
  subst attempt
  rw [aligned.2 entry prior]
  exact hit

/-- Before a saved record exists, alignment forces the actual earlier selected-seal list to be empty. -/
theorem aligned_empty (state : State) (aligned : Aligned state none) : state.seals = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry member
  have bad := aligned.2 entry member
  cases bad

/-- The reached selected seal records its actual optional response. Its poststate aligns with the same private captured reply, including refusal. -/
theorem aligned_seal (state : State) (aligned : Aligned state none) (input : CtxSealInput)
    (reply : Option CtxRomRecord) : Aligned (step (.inl (.inl (.inr (.inr input)))) reply state) reply := by
  have empty := aligned_empty state aligned
  cases reply with
  | none => exact aligned
  | some record =>
      refine ⟨aligned.1, ?_⟩
      intro entry member
      simp only [step, empty, List.mem_singleton] at member
      subst entry
      rfl

/-- On the first selected raw call, the complete original raw reply and quiet suffix cannot increase the captured tag event. No distribution is conditioned on the optional plaintext. -/
theorem raw_probability (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16)) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (quiet : ∀ reply, (next reply).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved) :
    Pr{let result ← ((simulateQ (observed real decode crypto key)
        (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr raw)); next reply)).run state)}[Matched guess result.2.1] ≤
    Pr{let result ← (pure (saved.map (fun record => (record, raw)), state.2) :
        ProbComp (PqxdhServerAuthPublicationGuess.Candidate × AdaptiveCtxDynamicKnownKeys.SourceState))}[Hit guess result.1] := by
  classical
  by_cases hit : Hit guess (saved.map fun record => (record, raw))
  · simpa only [prEvent_pure, hit, ite_true] using
      ((prEvent_le_one _) : Pr{let result ← ((simulateQ (observed real decode crypto key)
          (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr raw)); next reply)).run state)}[Matched guess result.2.1] ≤ 1)
  · simp only [prEvent_pure, hit, ite_false, nonpos_iff_eq_zero]
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported matched
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    simp only [observed, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, _, supported⟩ := supported
    exact hit (raw_match real decode crypto key guess (next reply.1) (quiet reply.1)
      (state.1, reply.2) saved aligned raw reply.1 result supported matched)

/-- The actual all-attempt matched-record event is bounded by the before-raw captured tag event. The all-reply one-seal/one-raw caps supply first-occurrence uniqueness; no success or writer event is conditioned on. -/
theorem capture_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (saved : Option CtxRomRecord)
    (aligned : Aligned state.1 saved)
    (sealBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1)
    (rawBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 1)
    (noMore : saved ≠ none → work.IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0) :
    Pr{let result ← (simulateQ (observed real decode crypto key) work).run state}[Matched guess result.2.1] ≤
    Pr{let result ← ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
        (PqxdhServerAuthPublicationCaptureSource.dynamic work saved)).run state.2)}[Hit guess result.1] := by
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
      rcases query with ((coin | (input | request)) | raw) | known
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [observed, StateT.run, prAssoc, pure_bind]
        change Pr{let result ← (do
          let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inl coin)))).run state.2
          (simulateQ (observed real decode crypto key) (next reply.1)).run (state.1, reply.2))}[Matched guess result.2.1] ≤
          Pr{let result ← (do
            let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inl (.inl (.inl coin)))).run state.2
            (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
              (PqxdhServerAuthPublicationCaptureSource.dynamic (next reply.1) saved)).run reply.2)}[Hit guess result.1]
        simp only [OracleComp.prEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro reply
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
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
              (PqxdhServerAuthPublicationCaptureSource.dynamic (next reply.1) saved)).run reply.2)}[Hit guess result.1]
        simp only [OracleComp.prEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro reply
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
        · intro present
          have quiet := noMore present
          simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
          exact quiet.2 reply.1
      · have none : saved = none := by
          cases found : saved with
          | none => rfl
          | some record =>
            have quiet := noMore (by simp only [found, ne_eq, reduceCtorEq, not_false_eq_true])
            simp only [isQueryBoundP_query_bind_iff, AdaptiveCtxDynamicKnownBounds.TargetClass,
              AdaptiveCtxQueryBounds.SourceSeal, Nat.lt_irrefl, not_true_eq_false, or_self, false_and] at quiet
        subst saved
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [observed, StateT.run, prAssoc, pure_bind]
        change Pr{let result ← (do
          let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key
            (.inl (.inl (.inr (.inr request))))).run state.2
          (simulateQ (observed real decode crypto key) (next reply.1)).run
            (step (.inl (.inl (.inr (.inr request)))) reply.1 state.1, reply.2))}[Matched guess result.2.1] ≤
          Pr{let result ← (do
            let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key
              (.inl (.inl (.inr (.inr request))))).run state.2
            (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
              (PqxdhServerAuthPublicationCaptureSource.dynamic (next reply.1) reply.1)).run reply.2)}[Hit guess result.1]
        simp only [OracleComp.prEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro reply
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        have tailSeal : (next reply.1).IsQueryBoundP
            (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
          simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal,
            ite_true, Nat.sub_self] using sealBound.2 reply.1
        refine ih reply.1 _ reply.1 (aligned_seal state.1 aligned request reply.1)
          (tailSeal.mono (by omega)) ?_ (fun _ => tailSeal)
        simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
      · exact raw_probability real decode crypto key guess raw next
          (fun reply => by simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery, ite_true,
            Nat.sub_self] using rawBound.2 reply) state saved aligned
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [observed, StateT.run, prAssoc, pure_bind]
        change Pr{let result ← (do
          let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inr known)).run state.2
          (simulateQ (observed real decode crypto key) (next reply.1)).run (state.1, reply.2))}[Matched guess result.2.1] ≤
          Pr{let result ← (do
            let reply ← (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key (.inr known)).run state.2
            (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
              (PqxdhServerAuthPublicationCaptureSource.dynamic (next reply.1) saved)).run reply.2)}[Hit guess result.1]
        simp only [OracleComp.prEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro reply
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        refine ih reply.1 (state.1, reply.2) saved aligned ?_ ?_ ?_
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal] using sealBound.2 reply.1
        · simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery] using rawBound.2 reply.1
        · intro present
          have quiet := noMore present
          simp only [isQueryBoundP_query_bind_iff, Nat.zero_sub, ite_self] at quiet
          exact quiet.2 reply.1


/-- The literal empty observer and source histories discharge all alignment and prior-record conditions. -/
theorem initial_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (sealBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1)
    (rawBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 1) :
    Pr{let result ← ((simulateQ (observed real decode crypto key) work).run
        (initialState, AdaptiveCtxDynamicKnownKeys.initialSource))}[Matched guess result.2.1] ≤
    Pr{let result ← ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key)
        (PqxdhServerAuthPublicationCaptureSource.dynamic work none)).run AdaptiveCtxDynamicKnownKeys.initialSource)}[Hit guess result.1] := by
  exact capture_bound real decode crypto key guess work _ none
    ⟨rfl, by simp [RawCtxSelectedAuthenticationObserver.initialState]⟩ sealBound rawBound (fun impossible => (impossible rfl).elim)

/-- The executable ordinary monitor and original uniformly sampled selected key preserve the matching-history bound, including the full shared source state. -/
theorem source_bound (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (guess : Pqxdh.Bytes → Option (FixedBytes 16))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (sealBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1)
    (rawBound : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 1) :
    Pr{let result ← AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto (monitor work initialState)}[Matched guess result.1.2] ≤
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic work none))}[Hit guess result.1] := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, OracleComp.prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro key
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have bound := initial_bound real decode crypto key guess work sealBound rawBound
  rw [← monitored_program real decode crypto key work] at bound
  simpa only [prEvent_map, Function.comp_def, PqxdhSelectedStateInterpreter.pair] using bound

open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The owner-indexed receipt supplies an actual earlier record in the matched raw attempt. Its tag comes from the decoded full tuple, not from an independently chosen ciphertext. -/
theorem receipt_matched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (index : Nat) (snap : Snapshot) (state : State)
    (receipt : PqxdhServerAuthPublicationOccurrence.ReceiptAt setup codec context index snap state) :
    Matched (PqxdhServerAuthPublicationRandom.decodedTag
      (RawCtxUniversalDecoder.decoder codec.frameRead)) state := by
  obtain ⟨message, reply, bytes, sealContext, entry, attempt, target,
    touched, input, beacon, logged, fields, records, member, decoded, plaintext, prior, same⟩ := receipt
  exact ⟨attempt, member, entry, prior,
    PqxdhServerAuthPublicationAcceptance.matching_hit _ _ _ _ decoded same⟩

/-- The exact normal journaled source execution yields either the existing ordinary authentication observer win or an ordered matching tag. The source acceptance, original owner and collision conditions retain their original meanings. -/
theorem journal_matched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (continues : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost) :
    won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      Matched (PqxdhServerAuthPublicationRandom.decodedTag
        (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1 := by
  rcases PqxdhServerAuthPublicationOccurrence.journal_receipt setup codec checks adversary context rest key Q j
    writable result supported journal continues snap accepted owned notBad unique with winning | receipt
  · exact Or.inl winning
  · exact Or.inr (receipt_matched setup codec context j.val snap result.2.1 receipt.2)

/-- The complete sampled accepted-observation client has the ordered capture bound with its source-derived one-seal and one-raw caps. This comparison alone does not impose the publication filter. -/
theorem client_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (observer : PqxdhServerAuthObservedEntry.Observer) :
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (monitor
          (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer) initialState))}[Matched (PqxdhServerAuthPublicationRandom.decodedTag
        (RawCtxUniversalDecoder.decoder codec.frameRead)) result.1.2] ≤
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (PqxdhServerAuthPublicationCaptureSource.dynamic
          (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer) none))}[Hit (PqxdhServerAuthPublicationRandom.decodedTag
        (RawCtxUniversalDecoder.decoder codec.frameRead)) result.1] := by
  have bills := PqxdhServerAuthPublicationObservedCompiler.client_record_bills setup codec checks adversary Q j observer
  exact source_bound true _ setup.source.crypto _ _ bills.1 bills.2.1


end BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.attempts_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.attempts_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.matched_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.matched_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.raw_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.raw_match
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.aligned_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.aligned_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.aligned_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.aligned_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.raw_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.raw_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.capture_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.capture_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.initial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.initial_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.source_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.receipt_matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.receipt_matched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.journal_matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.journal_matched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureHistory.client_bound
