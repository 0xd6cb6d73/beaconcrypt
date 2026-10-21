import BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence

/-! Exact optional CTX compiler for accepted public observations, independent of the older W1/W2 event. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxStop
open PqxdhServerAuthObservedEntry (Observer)
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Complete source outcome, including literal public query/reply journal. -/
abbrev Answer (KemSK : Type) := (Unit × QueryLog ServerAuthSpec) × HiddenState KemSK

/-- The original accepted-owner gate and supplied public observation, with source refusal retained. -/
noncomputable def observe (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) (result : Answer KemSK) : Bool :=
  !result.2.1.2.2.bad &&
    PqxdhServerAuthObservedEntry.decision setup context Q j observer result.2.1.1.ghost result.1.2

/-- Outer stopping has no native reply or acceptance meaning. Continuing runs test the original complete observation. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (result : Option (Unit × QueryLog ServerAuthSpec) × (HiddenState KemSK × Option Nat)) : Bool :=
  match result.1 with
  | none => false
  | some reply => observe setup context Q j observer (reply, result.2.1)

/-- The actual two-mark stop cannot remove an accepted owner observation: its existing collision exclusion rules out precisely that source evidence. -/
theorem relation_observe (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) (left : Answer KemSK)
    (right : Option (Unit × QueryLog ServerAuthSpec) × (HiddenState KemSK × Option Nat))
    (related : SourceRelation setup context Q j left right) :
    observe setup context Q j observer left = decision setup context Q j observer right := by
  rcases related with ⟨invariant, (⟨reply, state, _⟩ | ⟨refused, doubled⟩)⟩
  · simp only [decision, reply, state, Prod.mk.eta]
  · simp only [decision, refused]
    apply Bool.eq_false_of_not_eq_true
    intro winning
    simp only [observe, Bool.and_eq_true] at winning
    have gate := (@of_decide_eq_true _ (Classical.propDecidable _) winning.2).1
    exact PqxdhServerAuthPublicationOccurrence.no_double_mark setup context Q j left.2 invariant
      gate.2.2.2 gate.2.2.1 doubled

/-- The unchanged arbitrary adaptive public client and its actual stopped source have the same accepted-observation distribution, jointly with the public journal. -/
theorem client_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (client : OracleComp ServerAuthSpec Unit)
    (observer : Observer) (state : HiddenState KemSK) (first : Option Nat)
    (invariant : TraceInvariant setup context Q j state) (tracked : Tracked state.1.2.1 first) :
    𝒟[observe setup context Q j observer <$>
      ((simulateQ (hiddenHandler setup codec checks context Q j (tableServices setup context tails))
        (PqxdhServerAuthApiJournal.record client)).run state)] =
    𝒟[decision setup context Q j observer <$>
      (((simulateQ (sourceStopped setup codec checks context Q j tails)
        (PqxdhServerAuthApiJournal.record client)).run).run (state, first))] := by
  apply EvalDistEq.evalDist_eq
  refine (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).1 ?_
  apply evalSPMF_map_eq_of_relTriple
  exact relTriple_post_mono
    (source_client_coupling setup codec checks context Q j tails (PqxdhServerAuthApiJournal.record client)
      state first invariant tracked)
    (fun left right related => relation_observe setup context Q j observer left right related)

/-- The literal factor-side experiment is unchanged by its operational stop on every actual sampled context and factor output. -/
theorem entry_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    𝒟[PqxdhServerAuthObservedEntry.distinguisher setup codec checks adversary false Q j observer context value] =
    𝒟[decision setup context Q j observer <$>
      (((simulateQ (sourceStopped setup codec checks context Q j (factorServices setup codec checks context value))
        (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))).run).run
          (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none))] := by
  have equality := client_event setup codec checks context Q j (factorServices setup codec checks context value)
    (adversary (contextInput setup false context)) observer _ none (TraceInvariant.initial setup context Q j)
    ⟨(by intro index marked; cases marked), (by intro index recorded; cases recorded)⟩
  exact equality

/-- Cache reinstatement changes none of the public observation, its owner gate or optional stopping decision. -/
theorem decision_project (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (result : Option (Unit × QueryLog ServerAuthSpec) × PqxdhServerAuthCtxReserve.Monitored KemSK) :
    decision setup context Q j observer (Prod.map id PqxdhServerAuthCtxReserve.project result) =
      decision setup context Q j observer (result.1, result.2.1) := by
  rcases result with ⟨_ | reply, after⟩ <;> rfl

/-- The executable continuation retains the complete actual journal and original event interface; it requires no selected-key argument. -/
noncomputable def continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  decision setup context Q j observer <$>
    PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest

/-- The complete selected component interpreter is the original stopped source run with identical public replies and journal. -/
theorem continuation_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) :
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (continuation setup codec checks adversary Q j observer context rest)).run
      AdaptiveCtxDynamicKnownKeys.initialSource =
    decision setup context Q j observer <$>
      (((simulateQ (sourceStopped setup codec checks context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)))
        (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))).run).run
          (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none)) := by
  have same := congrArg (fun program => decision setup context Q j observer <$> program)
    (PqxdhServerAuthCtxReserve.program_source setup codec checks context rest Q j key
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
      (PqxdhServerAuthCtxReserve.initial setup context) (PqxdhServerAuthCtxReserve.initial_valid setup context))
  have start : PqxdhServerAuthCtxReserve.project (PqxdhServerAuthCtxReserve.initial setup context) =
      (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none) := rfl
  rw [start] at same
  simp only [continuation, simulateQ_map, StateT.run_map, Functor.map_map]
  simpa only [Functor.map_map, Function.comp_def, decision_project, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, PqxdhServerAuthPublicationOccurrence.execution, StateT.run,
    PqxdhSelectedStateInterpreter.pair, Prod.mk.eta, PqxdhServerAuthCtxReserve.initial] using same

/-- The existing fixed-coordinate uniform observation is exactly this component continuation after full source projection. -/
theorem context_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) :
    𝒟[PqxdhServerAuthObservedEntry.distinguisher setup codec checks adversary false Q j observer context
      (PqxdhServerAuthCtxMaterial.output key rest)] =
    𝒟[Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (continuation setup codec checks adversary Q j observer context rest)).run
      AdaptiveCtxDynamicKnownKeys.initialSource] := by
  rw [continuation_source]
  exact entry_event setup codec checks adversary Q j observer context _

/-- The observer client draws the original complete context and residual schedule itself. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual)
  continuation setup codec checks adversary Q j observer context rest

/-- Both executable samplers preserve their entire continuation and the actual component state. -/
theorem client_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (key : RootOutput) :
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (client setup codec checks adversary Q j observer)).run AdaptiveCtxDynamicKnownKeys.initialSource =
    (do let context ← contextSample setup codec
        let rest ← $ᵗ PqxdhServerAuthCtxCalls.Residual
        Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
          (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
          (continuation setup codec checks adversary Q j observer context rest)).run
          AdaptiveCtxDynamicKnownKeys.initialSource) := by
  simp only [client, simulateQ_bind, StateT.run_bind, map_bind,
    PqxdhServerAuthCtxExperiment.sample_source, bind_map_left]

/-- The full observed uniform-entry experiment equals the constructed ordinary CTX client with coefficient one and no event-transfer premise. -/
theorem uniform_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) :
    𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j observer] =
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (client setup codec checks adversary Q j observer)] := by
  apply EvalDistEq.evalDist_eq
  have sampling := PqxdhServerAuthCtxMaterial.key_first_context (contextSample setup codec)
    (fun context value => PqxdhServerAuthObservedEntry.distinguisher setup codec checks adversary false Q j observer context value)
  unfold PqxdhServerAuthObservedSchedule.uniformGame
  refine sampling.trans ?_
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, map_bind, client_source]
  apply evalSPMF_bind_congr_support
  intro key _
  apply evalSPMF_bind_congr_support
  intro context _
  apply evalSPMF_bind_congr_support
  intro rest _
  exact EvalDistEq.of_evalDist_eq (context_source setup codec checks adversary Q j observer context rest key)

/-- The complete sampled run is shared by the new observation and the original decision; only pure terminal projections differ. -/
noncomputable def full (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual)
  let result ← PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest
  pure (context, rest, result)

/-- Exact projection to the new accepted observer; its predicate adds no oracle calls. -/
theorem full_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) :
    (fun result => decision setup result.1 Q j observer result.2.2) <$>
      full setup codec checks adversary Q j = client setup codec checks adversary Q j observer := by
  simp only [full, client, continuation, map_bind, bind_pure_comp, Functor.map_map]

/-- Exact projection to the prior complete client, erasing only the new public journal. This permits reuse of all source-derived component resource certificates. -/
theorem full_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (fun result => PqxdhServerAuthCtxExperiment.decision setup result.1 Q j
      (result.2.2.1.map Prod.fst, result.2.2.2)) <$> full setup codec checks adversary Q j =
      PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j := by
  simp only [full, PqxdhServerAuthCtxExperiment.client, PqxdhServerAuthCtxExperiment.continuation,
    map_bind, bind_pure_comp, Functor.map_map]
  apply bind_congr
  intro context
  apply bind_congr
  intro rest
  have same := congrArg (fun work => PqxdhServerAuthCtxExperiment.decision setup context Q j <$> work)
    (PqxdhServerAuthPublicationOccurrence.execution_erase setup codec checks adversary Q j context rest)
  simpa only [Functor.map_map, Function.comp_def] using same

/-- The new observation retains every original class certificate exactly, for arbitrary replies and all complete source samplers. -/
theorem client_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (cap : Nat) :
    (client setup codec checks adversary Q j observer).IsQueryBoundP predicate cap ↔
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP predicate cap := by
  exact (isQueryBoundP_iff_of_map_eq (p := predicate) (full_client setup codec checks adversary Q j observer)).symm.trans
    (isQueryBoundP_iff_of_map_eq (p := predicate) (full_original setup codec checks adversary Q j))

/-- Both terminal projections leave the ordinary all-attempt authentication observer exactly unchanged, so the existing constructed authentication reductions remain applicable. -/
theorem client_authentication (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (decode : AdaptiveCtxReceive.RawDecoder) :
    RawCtxSelectedAuthenticationObserver.decision decode (client setup codec checks adversary Q j observer) =
      RawCtxSelectedAuthenticationObserver.decision decode
        (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) := by
  rw [← full_client setup codec checks adversary Q j observer,
    ← full_original setup codec checks adversary Q j]
  simp only [RawCtxSelectedAuthenticationObserver.decision, RawCtxSelectedAuthenticationObserver.monitor,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- Generalized certificates, including weighted selected plaintext bytes, are identical for the two complete clients. -/
theorem client_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (available : Budget) (allowed : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    (client setup codec checks adversary Q j observer).IsQueryBound available allowed cost ↔
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBound available allowed cost := by
  exact (isQueryBound_iff_of_map_eq (full_client setup codec checks adversary Q j observer) allowed cost).symm.trans
    (isQueryBound_iff_of_map_eq (full_original setup codec checks adversary Q j) allowed cost)

/-- The actual new client retains the sharp one-seal/one-raw limits and the source overflow-derived plaintext allowance without a caller byte or success premise. -/
theorem client_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) :
    (client setup codec checks adversary Q j observer).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (client setup codec checks adversary Q j observer).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
    AdaptiveCtxDynamicKnownBounds.PlaintextBound (client setup codec checks adversary Q j observer)
      Aeneas.Std.Usize.max := by
  have original := PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j
  refine ⟨(client_bound setup codec checks adversary Q j observer _ 1).mpr original.1,
    (client_bound setup codec checks adversary Q j observer _ 1).mpr original.2, ?_⟩
  exact (client_budget setup codec checks adversary Q j observer _ _ _).mpr
    (PqxdhServerAuthCtxByteBounds.client_plaintext setup codec checks adversary Q j)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.relation_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.relation_observe

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_event

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.entry_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.entry_event

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.decision_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.decision_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.continuation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.context_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.context_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.uniform_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.uniform_game

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.full_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.full_client

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.full_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.full_original

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_authentication

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler.client_record_bills
