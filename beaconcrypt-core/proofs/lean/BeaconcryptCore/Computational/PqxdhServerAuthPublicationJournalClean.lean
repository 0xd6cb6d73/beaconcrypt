import BeaconcryptCore.Computational.PqxdhServerAuthPublicationMarkedHistory
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource

/-! The original one-shot finish and chronological owner marks connect the public journal to request-time publication flags. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthPendingBudget PqxdhServerAuthGapDh
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Source mark transitions only preserve flags or set one flag to true; an existing marked owner cannot be erased by later allocation. -/
theorem mark_step (query : ServerAuthSpec.Domain) (before after : HiddenState KemSK)
    (step : MarkStep query before.1 after.1) (index : Nat) (marked : before.1.2.1 index = true) :
    after.1.2.1 index = true := by
  rcases query with coin | query
  · exact congrFun step index |>.trans marked
  · cases query with
    | accept raw =>
        rcases step with same | changed
        · exact congrFun same index |>.trans marked
        · rw [changed]
          by_cases equal : index = before.1.1.sessions
          · subst index
            simp
          · simp only [Function.update_of_ne equal, marked]
    | _ => exact congrFun step index |>.trans marked

/-- A normal actual checkpoint carries the literal callback resource and mark footprints; monitor refusal never fabricates a continuing state. -/
theorem stopped_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat))
    (supported : result ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state))
    (answer : ServerAuthSpec.Range query) (normal : result.1 = some answer) :
    ResourceStep query state.1.1.1 result.2.1.1.1 ∧ MarkStep query state.1.1 result.2.1.1 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨actual, supported, rfl⟩ := supported
  cases reply : actual.1 with
  | none => simp only [PqxdhServerAuthCtxStop.observe, reply, reduceCtorEq] at normal
  | some value =>
      have facts := PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j
        query state.1 actual supported value reply
      simpa only [PqxdhServerAuthCtxStop.observe_state] using facts

/-- The complete stopped callback has the original immediate raw allowance before any optional checkpoint refusal. -/
theorem stopped_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (rawBill query state.1.1.1) := by
  simpa only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped, OptionT.run_mk,
    StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
      (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query state.1).2


/-- The actual remaining one-shot Beacon phase pays every raw request in an arbitrary adaptive suffix. This does not require any cryptographic or successful-reply premise. -/
theorem program_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (initSentFlag state.1.1.1) := by
  apply optional_potential_invariant
    (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
    (fun _ => True) (fun (_ : Fin 1) (_ : ServerAuthSpec.Domain) => False)
    (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery)
    (fun _ state => initSentFlag state.1.1.1) ?_ work (fun _ => 0)
    (fun _ => isQueryBoundP_false work 0) state True.intro
  intro query before budget valid allowed
  refine ⟨rawBill query before.1.1.1, stopped_raw setup codec checks context rest Q j query before,
    rawBill_le query before.1.1.1, ?_⟩
  intro result supported reply normal
  have footprint := stopped_footprint setup codec checks context rest Q j query before result supported reply normal
  refine ⟨True.intro, ?_⟩
  simpa using raw_potential_step query before.1.1.1 result.2.1.1.1 footprint.1 true

/-- Private publication markers preserve that literal zero-raw guarantee after the first completed finish. -/
theorem marked_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat)
    (inactive : initSentFlag state.1.1.1 = 0) :
    (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work state).IsQueryBoundP
      PqxdhServerAuthPublicationMarkedHistory.Raw 0 := by
  have original := program_raw setup codec checks context rest Q j work state
  have erased := (PqxdhServerAuthPublicationMarkedHistory.erase_bound
    (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery)
    (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work state) 0).mpr
      (by simpa only [PqxdhServerAuthPublicationPrefixSource.program_erase, isQueryBoundP_map_iff, inactive] using original)
  exact erased

/-- Every earlier true session mark survives the complete normal source suffix. This is source transition monotonicity, not a key-equality or final-origin assumption. -/
theorem program_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK × Option Nat)
    (result : Option Result × (Local KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state))
    (answer : Result) (normal : result.1 = some answer)
    (index : Nat) (marked : state.1.1.2.1 index = true) : result.2.1.1.2.1 index = true := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact marked
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      cases reply : middle.1 with
      | none =>
          simp only [reply, Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases normal
      | some value =>
          simp only [reply, Option.elim_some] at supported
          have footprint := stopped_footprint setup codec checks context rest Q j query state middle reached value reply
          exact ih value middle.2 supported
            (mark_step query state.1 middle.2.1 footprint.2 index marked)

open CtxRomAuth AdaptiveCtxReceive

/-- Interpreting an original component program under the marked observer only restricts its possible replies; the complete callback result remains syntactically reachable. -/
theorem lifted_support (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Result × (PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode crypto key)
      (simulateQ PqxdhServerAuthPublicationPrefixStop.liftDynamic work)).run state)) : result.1 ∈ support work := by
  rw [← QueryImpl.simulateQ_compose] at supported
  apply support_simulateQ_run'_subset
    ((PqxdhServerAuthPublicationMarkedHistory.observed real decode crypto key).compose
      PqxdhServerAuthPublicationPrefixStop.liftDynamic) work state
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  exact ⟨result, supported, rfl⟩

/-- Removing private marker observations retains each complete returned value in the ordinary observed program's support. -/
theorem erased_support (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp PqxdhServerAuthPublicationPrefixStop.Spec Result)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Result × (PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode crypto key)
      work).run state)) : result.1 ∈ support (simulateQ PqxdhServerAuthPublicationPrefixStop.erase work) := by
  apply support_simulateQ_run'_subset (RawCtxSelectedAuthenticationObserver.observed real decode crypto key)
    (simulateQ PqxdhServerAuthPublicationPrefixStop.erase work) (state.1.observer, state.2)
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  refine ⟨(result.1, (result.2.1.observer, result.2.2)), ?_, rfl⟩
  rw [← PqxdhServerAuthPublicationMarkedHistory.observer_erase]
  rw [support_map]
  exact Set.mem_image_of_mem _ supported

/-- Any mark present before an actually interpreted marked program remains in its normal terminal source state. -/
theorem marked_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (real : Bool) (decode : RawDecoder) (key : CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Option (Result × (Local KemSK × Option Nat)) ×
      (PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
      (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work before)).run state))
    (answer : Result) (after : Local KemSK × Option Nat) (normal : result.1 = some (answer, after))
    (index : Nat) (marked : before.1.1.2.1 index = true) : after.1.1.2.1 index = true := by
  have original := erased_support real decode setup.source.crypto key _ state result supported
  rw [PqxdhServerAuthPublicationPrefixSource.program_erase, support_map, Set.mem_image] at original
  obtain ⟨actual, reached, same⟩ := original
  cases reply : actual.1 with
  | none => simp only [PqxdhServerAuthPublicationPrefixSource.optional, reply, Option.map_none, normal, reduceCtorEq] at same
  | some value =>
      simp only [PqxdhServerAuthPublicationPrefixSource.optional, reply, Option.map_some, normal,
        Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, final⟩ := same
      rw [← final]
      exact program_marks setup codec checks context rest Q j work before actual reached value reply index marked

open PqxdhServerAuthPublicationOccurrence

/-- A nonfinishing public head preserves the exact missing-publication predicate for the remaining chronological journal. -/
theorem unpublished_tail (index : Nat) (event : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query)
    (journal : QueryLog ServerAuthSpec) (notFinished : finishReturned event = false)
    (unpublished : ¬ Published index (event :: journal)) : ¬ Published index journal := by
  intro published
  obtain ⟨payload, reply, member⟩ := published
  apply unpublished
  refine ⟨payload, reply, ?_⟩
  simpa only [beforeAcceptance, List.takeWhile_cons, notFinished, Bool.not_false, ite_true,
    List.mem_cons] using Or.inr member

/-- If every currently marked coordinate is the actual owner, a missing publication in the public prefix rules out the callback's private publication marker. -/
theorem marker_false (index : Nat) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (reply : ServerAuthSpec.Range query) (journal : QueryLog ServerAuthSpec)
    (owner : ∀ k, before.1.2.1 k = true → k = index)
    (unpublished : ¬ Published index (⟨query, reply⟩ :: journal)) :
    PqxdhServerAuthPublicationFilter.published query before (some reply) = false := by
  rcases query with coin | query
  · rfl
  cases query with
  | build k payload =>
      cases reply with
      | none => simp [PqxdhServerAuthPublicationFilter.published]
      | some response =>
          by_cases marked : before.1.2.1 k = true
          · have same := owner k marked
            subst k
            exact False.elim (unpublished ⟨payload, response, by
              simp [beforeAcceptance, finishReturned]⟩)
          · have falseMark : before.1.2.1 k = false := Bool.eq_false_of_not_eq_true marked
            simp [PqxdhServerAuthPublicationFilter.published, falseMark]
  | _ => rfl

/-- The actual journal transformation prepends the real public reply while source markers remain exactly at callback completion. -/
theorem journal_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (next : ServerAuthSpec.Range query → OracleComp ServerAuthSpec Result) (before : Local KemSK × Option Nat) :
    PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
      (PqxdhServerAuthApiJournal.record (ServerAuthSpec.query query >>= next)) before = (do
      let actual ← simulateQ PqxdhServerAuthPublicationPrefixStop.liftDynamic
        ((PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
          query).run.run before)
      let _ ← PqxdhServerAuthPublicationPrefixStop.Spec.query
        (.inr (PqxdhServerAuthPublicationFilter.published query before.1 actual.1))
      match actual.1 with
      | none => pure none
      | some reply =>
          Option.map (Prod.map (fun result : Result × QueryLog ServerAuthSpec => (result.1, (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: result.2)) id) <$>
            PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
              (PqxdhServerAuthApiJournal.record (next reply)) actual.2) := by
  rw [PqxdhServerAuthApiJournal.record, run_simulateQ_loggingOracle_query_bind]
  change (do
    let actual ← simulateQ PqxdhServerAuthPublicationPrefixStop.liftDynamic
      ((PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        query).run.run before)
    let _ ← PqxdhServerAuthPublicationPrefixStop.Spec.query
      (.inr (PqxdhServerAuthPublicationFilter.published query before.1 actual.1))
    match actual.1 with
    | none => pure none
    | some reply =>
        PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
          ((fun result : Result × QueryLog ServerAuthSpec => (result.1, (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: result.2)) <$>
            PqxdhServerAuthApiJournal.record (next reply)) actual.2) = _
  refine bind_congr fun actual => ?_
  refine bind_congr fun _ => ?_
  cases actual.1 with
  | none => rfl
  | some reply => exact PqxdhServerAuthPublicationPrefixSource.program_map setup codec checks context rest Q j _ _ _

private theorem marker_run (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (flag : Bool) (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (PqxdhServerAuthPublicationMarkedHistory.observed real decode crypto key (.inr flag)).run state =
      pure ((), (PqxdhServerAuthPublicationMarkedHistory.step (.inr flag) () state.1, state.2)) := rfl

/-- Missing publication at the reached owner before the first successful public finish makes every recorded raw attempt clean. Subsequent publications remain unrestricted. -/
theorem journal_clean (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (real : Bool) (decode : RawDecoder) (key : CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (clean : PqxdhServerAuthPublicationMarkedHistory.Clean state.1) (unpublished : state.1.published = false)
    (answer : Result) (journal : QueryLog ServerAuthSpec) (after : Local KemSK × Option Nat)
    (finalState : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : (some ((answer, journal), after), finalState) ∈ support ((simulateQ
      (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
      (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
        (PqxdhServerAuthApiJournal.record work) before)).run state))
    (owner : ∀ index, after.1.1.2.1 index = true → index = j.val)
    (notPublished : ¬ Published j.val journal) : PqxdhServerAuthPublicationMarkedHistory.Clean finalState.1 := by
  induction work using OracleComp.inductionOn generalizing before state answer journal after finalState with
  | pure value =>
      change (some ((answer, journal), after), finalState) ∈ support (pure (some ((value, []), before), state)) at supported
      simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := supported
      exact clean
  | query_bind query next ih =>
      rw [journal_step] at supported
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      have middleClean := PqxdhServerAuthPublicationMarkedHistory.lifted_clean real decode setup.source.crypto key
        _ state clean unpublished middle reached
      have original := lifted_support real decode setup.source.crypto key _ state middle reached
      simp only [simulateQ_spec_query, marker_run, mem_support_pure_iff] at supported
      obtain ⟨markerState, rfl, supported⟩ := supported
      cases reply : middle.1.1 with
      | none =>
          simp only [reply, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, reduceCtorEq, false_and] at supported
      | some value =>
          simp only [reply, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
          obtain ⟨⟨outcome, remainingState⟩, tailSupport, same⟩ := supported
          cases outcome with
          | none => simp only [Option.map_none, Prod.mk.injEq, reduceCtorEq, false_and] at same
          | some outcome =>
              rcases outcome with ⟨⟨tailAnswer, tailJournal⟩, tailFinal⟩
              simp only [Option.map_some, Prod.map_apply, Prod.mk.injEq, Option.some.injEq] at same
              obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := same
              have footprint := stopped_footprint setup codec checks context rest Q j query before middle.1 original value reply
              have middleOwner : ∀ index, middle.1.2.1.1.2.1 index = true → index = j.val := by
                intro index marked
                apply owner
                exact marked_marks setup codec checks context rest Q j (PqxdhServerAuthApiJournal.record (next value))
                  middle.1.2 real decode key _ _ tailSupport _ _ rfl index marked
              have beforeOwner : ∀ index, before.1.1.2.1 index = true → index = j.val := by
                intro index marked
                exact middleOwner index (mark_step query before.1 middle.1.2.1 footprint.2 index marked)
              have marker := marker_false j.val query before.1 value tailJournal beforeOwner notPublished
              have nextClean : PqxdhServerAuthPublicationMarkedHistory.Clean
                  (PqxdhServerAuthPublicationMarkedHistory.step (.inr
                    (PqxdhServerAuthPublicationFilter.published query before.1 middle.1.1)) () middle.2.1) := middleClean.1
              by_cases finished : finishReturned ⟨query, value⟩ = true
              · have inactive : initSentFlag middle.1.2.1.1.1 = 0 := by
                  rcases query with coin | query
                  · cases finished
                  cases query with
                  | finish raw => exact footprint.1.2.2
                  | _ => cases finished
                exact PqxdhServerAuthPublicationMarkedHistory.quiet_clean real decode setup.source.crypto key _
                  (marked_inactive setup codec checks context rest Q j (PqxdhServerAuthApiJournal.record (next value))
                    middle.1.2 inactive)
                  (PqxdhServerAuthPublicationMarkedHistory.step (.inr
                    (PqxdhServerAuthPublicationFilter.published query before.1 middle.1.1)) () middle.2.1,
                    middle.2.2) nextClean _ tailSupport
              · apply ih value middle.1.2
                  (PqxdhServerAuthPublicationMarkedHistory.step (.inr
                    (PqxdhServerAuthPublicationFilter.published query before.1 middle.1.1)) () middle.2.1,
                    middle.2.2) nextClean ?_ tailAnswer tailJournal tailFinal remainingState tailSupport owner
                  (unpublished_tail j.val ⟨query, value⟩ tailJournal (Bool.eq_false_of_not_eq_true finished) notPublished)
                simp only [PqxdhServerAuthPublicationMarkedHistory.step, reply, marker, middleClean.2, Bool.or_self]

/-- The full marked source program projects to the unchanged ordinary authentication observer and component state. Only the terminal local state of an already refused source result is omitted. -/
theorem program_observer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (real : Bool) (decode : RawDecoder) (key : CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1, (result.2.1.observer, result.2.2))) <$>
      (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
        (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work before)).run state =
    (fun result => (PqxdhServerAuthPublicationPrefixSource.optional result.1, result.2)) <$>
      (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key)
        ((simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run before)).run
          (state.1.observer, state.2) := by
  rw [PqxdhServerAuthPublicationMarkedHistory.observer_erase,
    PqxdhServerAuthPublicationPrefixSource.program_erase, simulateQ_map, StateT.run_map]

/-- A normal marked journal retains the identical complete normal source result and ordinary observer state; there is no support or origin premise beyond the actual interpreted run. -/
theorem normal_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (real : Bool) (decode : RawDecoder) (key : CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (answer : Result) (after : Local KemSK × Option Nat)
    (finalState : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : (some (answer, after), finalState) ∈ support ((simulateQ
      (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
      (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work before)).run state)) :
    ((some answer, after), (finalState.1.observer, finalState.2)) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run before)).run
      (state.1.observer, state.2)) := by
  have reached : (some (answer, after), (finalState.1.observer, finalState.2)) ∈ support
      ((fun result => (result.1, (result.2.1.observer, result.2.2))) <$>
        (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
          (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work before)).run state) := by
    rw [support_map]
    exact ⟨_, supported, rfl⟩
  rw [program_observer, support_map, Set.mem_image] at reached
  obtain ⟨⟨⟨reply, localState⟩, component⟩, reached, same⟩ := reached
  cases reply with
  | none => simp only [PqxdhServerAuthPublicationPrefixSource.optional, Option.map_none,
      Prod.mk.injEq, reduceCtorEq, false_and] at same
  | some value =>
      simp only [PqxdhServerAuthPublicationPrefixSource.optional, Option.map_some, Prod.mk.injEq,
        Option.some.injEq] at same
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
      exact reached

/-- The actual accepted owner, unchanged source collision gate, and public missing-publication predicate imply either the existing ordinary authentication win or a clean matching request. Initial source and component histories discharge all local chronology premises. -/
theorem accepted_clean (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : CtxKey) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (journal : QueryLog ServerAuthSpec) (after : Local KemSK × Option Nat)
    (finalState : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : (some (((), journal), after), finalState) ∈ support ((simulateQ
      (PqxdhServerAuthPublicationMarkedHistory.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
        (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
        (PqxdhServerAuthCtxReserve.initial setup context).1)).run
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (snap : Snapshot) (accepted : after.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q after.1.1.1.ghost = some j)
    (notBad : after.1.1.2.2.bad = false) (unique : ¬ CollB setup context.seed context.scalar after.1.1.1.ghost)
    (notPublished : ¬ Published j.val journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) finalState.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) finalState.1 := by
  have original := normal_source setup codec checks context rest Q j _ _ true _ key
    (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
    ((), journal) after finalState supported
  rcases journal_receipt setup codec checks adversary context rest key Q j writable
      ((some ((), journal), after), (finalState.1.observer, finalState.2)) original journal rfl
      snap accepted owned notBad unique with won | receipt
  · exact Or.inl won
  · have erased : ((some (), after), (finalState.1.observer, finalState.2)) ∈ support ((simulateQ
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
        (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
      rw [← observed_erase setup codec checks adversary Q j context rest key, support_map]
      exact ⟨_, original, rfl⟩
    have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j
      adversary _ erased rfl
    have onlyOwner : ∀ index, after.1.1.2.1 index = true → index = j.val := by
      intro index marked
      obtain ⟨message, reply, bytes, sealContext, entry, attempt, target, touched, rooted, beacon, other⟩ := receipt.2
      exact marked_owner setup context Q j after.1 invariant.2.trace invariant.2.history snap accepted owned unique
        j.val ⟨message, reply, bytes, touched, rooted, beacon⟩ index marked
    have clean := journal_clean setup codec checks context rest Q j
      (adversary (contextInput setup false context)) (PqxdhServerAuthCtxReserve.initial setup context).1
      true (RawCtxUniversalDecoder.decoder codec.frameRead) key
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
      (by intro item member; cases member) rfl () journal after finalState supported onlyOwner notPublished
    have coherent := PqxdhServerAuthPublicationMarkedHistory.coherent_program true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key _
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource) rfl _ supported
    exact Or.inr (PqxdhServerAuthPublicationMarkedHistory.matched_clean _ finalState.1 coherent clean
      (PqxdhServerAuthPublicationCaptureHistory.receipt_matched setup codec context j.val snap finalState.1.observer receipt.2))

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.mark_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.mark_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.stopped_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.stopped_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.stopped_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.stopped_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marked_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marked_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_marks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.lifted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.lifted_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.erased_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.erased_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marked_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marked_marks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.unpublished_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.unpublished_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marker_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.marker_false

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.journal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.journal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.journal_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.journal_clean

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.program_observer

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.normal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.normal_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.accepted_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean.accepted_clean
