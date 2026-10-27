import BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClean

/-! Complete original context and residual samplers for the marked publication journal. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthPublicationPrefixStop CtxRomAuth AdaptiveCtxReceive
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Full sampled source result, retaining the public journal and complete continuing source state. -/
abbrev Answer (KemSK : Type) := Context KemSK × PqxdhServerAuthCtxCalls.Residual ×
  Option ((Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat))

/-- The same source context and residual draws precede the original journaled marked program. The reduction requires no selected-key argument. -/
noncomputable def full (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) : OracleComp Spec (Answer KemSK) := do
  let context ← simulateQ liftDynamic (simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec))
  let rest ← simulateQ liftDynamic (simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual))
  let result ← PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
    (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
    (PqxdhServerAuthCtxReserve.initial setup context).1
  pure (context, rest, result)

/-- The original accepted-owner observation reads only its unchanged terminal ghost and public journal. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (Q : Nat) (j : Fin (Q + 1)) (result : Answer KemSK) : Bool :=
  match result.2.2 with
  | none => false
  | some (reply, state) => PqxdhServerAuthPublicationObservedCompiler.decision setup result.1 Q j
      (PqxdhServerAuthPublicationOccurrence.observer j.val) (some reply, state)

/-- Erasing markers recovers the complete original sampled observed compiler, with only its existing refused terminal-state projection. -/
theorem full_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    simulateQ erase (full setup codec checks adversary Q j) =
      (fun result => (result.1, result.2.1, PqxdhServerAuthPublicationPrefixSource.optional result.2.2)) <$>
        PqxdhServerAuthPublicationObservedCompiler.full setup codec checks adversary Q j := by
  simp only [full, simulateQ_bind, simulateQ_map, erase_lift,
    PqxdhServerAuthPublicationPrefixSource.program_erase,
    PqxdhServerAuthPublicationObservedCompiler.full, PqxdhServerAuthPublicationOccurrence.execution,
    map_bind, bind_pure_comp, Functor.map_map]

/-- Discarding the terminal journal does not change any original callback or private marker timing. -/
theorem program_forget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    (fun _ => ()) <$> PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
      (PqxdhServerAuthApiJournal.record work) state =
    (fun _ => ()) <$> PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j work state := by
  have same := congrArg (fun source => PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j source state)
    (PqxdhServerAuthApiJournal.erase work)
  rw [PqxdhServerAuthPublicationPrefixSource.program_map] at same
  have projected := congrArg (fun source => (fun _ => ()) <$> source) same
  simpa only [Functor.map_map] using projected

/-- The private captured prefix uses exactly the previously bounded source client after a pure terminal projection. -/
theorem full_forget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (fun _ => ()) <$> full setup codec checks adversary Q j =
      PqxdhServerAuthPublicationPrefixSource.client setup codec checks adversary Q j := by
  simp only [full, PqxdhServerAuthPublicationPrefixSource.client, map_bind, bind_pure_comp, Functor.map_map]
  refine bind_congr fun context => ?_
  refine bind_congr fun rest => ?_
  exact program_forget setup codec checks context rest Q j _ _

/-- The original observation decision is exactly the erasure of the marked complete client; no event-transport assumption is supplied. -/
theorem full_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    simulateQ erase (decision setup Q j <$> full setup codec checks adversary Q j) =
      PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j
        (PqxdhServerAuthPublicationOccurrence.observer j.val) := by
  rw [simulateQ_map, full_erase, Functor.map_map,
    ← PqxdhServerAuthPublicationObservedCompiler.full_client]
  apply congrArg (fun f => f <$> PqxdhServerAuthPublicationObservedCompiler.full setup codec checks adversary Q j)
  funext result
  rcases result with ⟨context, rest, reply, state⟩
  cases reply <;> rfl

/-- A sampled uniform request changes none of the marked or component histories. -/
theorem observed_coin (crypto : Pqxdh.Crypto) (key : CtxKey) (decode : RawDecoder) (query : unifSpec.Domain)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed true decode crypto key)
      (simulateQ liftDynamic (PqxdhServerAuthCtxAmbient.coin query))).run state =
      (fun value => (value, state)) <$> (unifSpec.query query : ProbComp _) := by
  have map_apply {X Y σ : Type} (f : X → Y) (work : StateT σ ProbComp X) (initial : σ) :
      (f <$> work) initial = (fun result => (f result.1, result.2)) <$> work initial := by
    change (f <$> work).run initial = _
    rw [StateT.run_map]
    rfl
  have lift_apply {X σ : Type} (work : ProbComp X) (initial : σ) :
      (monadLift work : StateT σ ProbComp X) initial = (fun value => (value, initial)) <$> work := by
    change (work >>= fun value => pure (value, initial)) = _
    rw [bind_pure_comp]
  simp [PqxdhServerAuthCtxAmbient.coin, liftDynamic, PqxdhServerAuthPublicationMarkedHistory.observed,
    PqxdhServerAuthPublicationMarkedHistory.step, RawCtxSelectedAuthenticationObserver.step, AdaptiveCtxDynamicKnownKeys.sourceImpl,
    AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
    StateT.run, map_apply, lift_apply]

/-- Every actual source prefix coin is retained while the complete marked/ordinary/component state is unchanged. -/
theorem observed_coins (crypto : Pqxdh.Crypto) (key : CtxKey) (decode : RawDecoder) (work : ProbComp Result)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed true decode crypto key)
      (simulateQ liftDynamic (simulateQ PqxdhServerAuthCtxAmbient.coin work))).run state =
      (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, observed_coin,
        bind_map_left, map_bind, ih]

/-- The complete marked sampler retains the exact source one-seal/one-raw caps for all replies. Markers add no component request. -/
theorem full_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (full setup codec checks adversary Q j).IsQueryBoundP PqxdhServerAuthPublicationMarkedHistory.Seal 1 ∧
    (full setup codec checks adversary Q j).IsQueryBoundP PqxdhServerAuthPublicationMarkedHistory.Raw 1 := by
  have original := PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j
  constructor
  · apply (PqxdhServerAuthPublicationMarkedHistory.erase_bound
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) _ 1).mpr
    rw [full_erase, isQueryBoundP_map_iff]
    exact (isQueryBoundP_iff_of_map_eq (p := AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (PqxdhServerAuthPublicationObservedCompiler.full_original setup codec checks adversary Q j)).mpr original.1
  · apply (PqxdhServerAuthPublicationMarkedHistory.erase_bound
      (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) _ 1).mpr
    rw [full_erase, isQueryBoundP_map_iff]
    exact (isQueryBoundP_iff_of_map_eq (p := AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery)
      (PqxdhServerAuthPublicationObservedCompiler.full_original setup codec checks adversary Q j)).mpr original.2

/-- The complete actual context/residual sampler supplies the empty-history premises of accepted_clean; every true publication observation is an ordinary win or a clean matched request on this same run. -/
theorem full_winning (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (key : CtxKey) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Answer KemSK × (PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthPublicationMarkedHistory.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key) (full setup codec checks adversary Q j)).run
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (winning : decision setup Q j result.1 = true) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1 := by
  simp only [full, simulateQ_bind, StateT.run_bind, observed_coins, bind_map_left,
    bind_pure_comp, simulateQ_map, StateT.run_map, mem_support_bind_iff, support_map, Set.mem_image] at supported
  obtain ⟨context, _, rest, _, outcome, reached, rfl⟩ := supported
  cases normal : outcome.1 with
  | none => simp only [decision, normal, Bool.false_eq_true] at winning
  | some reply =>
      rcases reply with ⟨⟨answer, journal⟩, after⟩
      cases answer
      simp only [decision, normal, PqxdhServerAuthPublicationObservedCompiler.decision,
        PqxdhServerAuthPublicationObservedCompiler.observe, Bool.and_eq_true] at winning
      have event := (@of_decide_eq_true _ (Classical.propDecidable _) winning.2)
      obtain ⟨snap, accepted⟩ := event.1.1
      have supportedNormal : (some (((), journal), after), outcome.2) ∈ support ((simulateQ
          (PqxdhServerAuthPublicationMarkedHistory.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
            setup.source.crypto key)
          (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
            (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
            (PqxdhServerAuthCtxReserve.initial setup context).1)).run
          (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
        simpa only [← normal, Prod.mk.eta] using reached
      exact PqxdhServerAuthPublicationJournalClean.accepted_clean setup codec checks adversary context rest key Q j
        writable journal after outcome.2 supportedNormal snap accepted event.1.2.2.2 (by simpa only [Bool.not_eq_true'] using winning.1) event.1.2.2.1
        ((PqxdhServerAuthPublicationOccurrence.observer_true j.val _ journal).mp event.2)

/-- The cutoff ignores every pure terminal projection, preserving the exact saved record and request-time flag. -/
theorem capture_map {α β : Type} (f : α → β) (work : OracleComp Spec α)
    (saved : Option CtxRomRecord) (published : Bool) :
    capture (f <$> work) saved published = capture work saved published := by
  induction work using OracleComp.inductionOn generalizing saved published with
  | pure value => rfl
  | query_bind query next ih =>
      rw [map_bind]
      rcases query with (((coin | (input | request)) | raw) | known) | flag
      · exact bind_congr fun reply => ih reply saved published
      · exact bind_congr fun reply => ih reply saved published
      · exact bind_congr fun reply => ih reply reply published
      · rfl
      · exact bind_congr fun reply => ih reply saved published
      · exact ih () saved (published || flag)

/-- The captured marked journal is exactly the previously bounded actual source prefix, not a separately assumed comparison experiment. -/
theorem full_capture (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    capture (full setup codec checks adversary Q j) none false =
      capture (PqxdhServerAuthPublicationPrefixSource.client setup codec checks adversary Q j) none false := by
  rw [← capture_map (fun _ => ()), full_forget]

/-- The complete marked observer, including its original ordinary history and component cache, projects exactly to the established observed client with the same Boolean decision. -/
theorem observed_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (real : Bool) (decode : RawDecoder) (key : CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (decision setup Q j result.1, (result.2.1.observer, result.2.2))) <$>
      (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
        (full setup codec checks adversary Q j)).run state =
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key)
      (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j
        (PqxdhServerAuthPublicationOccurrence.observer j.val))).run (state.1.observer, state.2) := by
  have same := congrArg (fun work =>
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key) work).run
      (state.1.observer, state.2)) (full_decision setup codec checks adversary Q j)
  simp only [simulateQ_map, StateT.run_map] at same
  rw [← PqxdhServerAuthPublicationMarkedHistory.observer_erase] at same
  simpa only [Functor.map_map] using same

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.program_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.program_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_winning

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.capture_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.capture_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.full_capture

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient.observed_decision
