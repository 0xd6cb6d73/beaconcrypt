import BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal

/-! Actual acceptance requires a successful public finish in the same complete execution journal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhServerAuthRecordPublicationEvent
open PqxdhJointGapDh PqxdhJointIdentity
variable {ι KemSK Reader Response Result τ : Type} {baseSpec : OracleSpec ι}

/-- The source's final publication cannot record acceptance when its actual optional reply is absent. -/
theorem outcome_none (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (rejected : (finishOutcome control game staged).1 = none) :
    (finishOutcome control game staged).2.ghost.acceptance = game.ghost.acceptance := by
  change (PqxdhBeaconPhase2Publication.finish control game.beacon staged).1 = none at rejected
  simp only [finishOutcome, acceptedOf, rejected, Option.isSome_none, Bool.false_eq_true, ite_false, Ghost.accept]

/-- Every rejected complete source finish preserves the previous acceptance, while retaining its actual prefix, derivation and opening effects. -/
theorem finish_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ)
    (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state))
    (rejected : result.1 = none) : result.2.1.ghost.acceptance = state.1.ghost.acceptance := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [phase, mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    cases prepared with
    | none =>
      simp only [mem_support_pure_iff] at supported
      subst result
      exact outcome_none control state.1 none rejected
    | some pending =>
      simp only [mem_support_bind_iff] at supported
      obtain ⟨derived, _, supported⟩ := supported
      cases reply : derived.1 with
      | rejected =>
        simp only [reply, mem_support_pure_iff] at supported
        subst result
        exact outcome_none control _ none rejected
      | root root =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [mem_support_pure_iff] at supported
        subst result
        exact outcome_none control _ staged.1 rejected
      | hidden =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [mem_support_pure_iff] at supported
        subst result
        exact outcome_none control _ staged.1 rejected
  | _ =>
    simp only [phase, mem_support_pure_iff] at supported
    subst result
    rfl

/-- Any source callback whose actual reply is not a successful finish preserves the exact previous acceptance. -/
theorem skeleton_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HiddenTable) (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup)
      context.beaconSeed services query).run state))
    (absent : finishRaw ⟨query, result.1⟩ = none) :
    result.2.1.ghost.acceptance = state.1.ghost.acceptance := by
  rcases query with coin | query
  · exact PqxdhServerAuthCtxAcceptanceCover.skeleton_acceptance setup codec checks context services _
      (fun _ equal => by cases equal) state result supported
  · cases query with
    | finish raw =>
      cases reply : result.1 with
      | none => exact finish_none setup codec (context.publicValue setup) context.beaconSeed services raw state result supported reply
      | some payload => simp only [finishRaw, reply, reduceCtorEq] at absent
    | _ =>
      exact PqxdhServerAuthCtxAcceptanceCover.skeleton_acceptance setup codec checks context services _
        (fun _ equal => by cases equal) state result supported

/-- Source designation and the sticky refusal wrapper preserve acceptance whenever this exact public callback is not a successful finish. -/
theorem handler_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (services : Services Response HiddenTable) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state))
    (absent : finishRaw ⟨query, result.1⟩ = none) :
    result.2.1.1.ghost.acceptance = state.1.1.ghost.acceptance := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  have reply : (keepHiddenBad state middle).1 = middle.1 := by
    unfold keepHiddenBad
    split <;> rfl
  rw [reply] at absent
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, reached, rfl⟩ := supported
    exact skeleton_none setup codec checks context _ query state.1 step reached absent

/-- The actual interpreted callback inherits source acceptance preservation with its full private cache and exact public reply. -/
theorem observed_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before))
    (value : ServerAuthSpec.Range query) (normal : result.1.1 = some value)
    (absent : finishRaw ⟨query, value⟩ = none) :
    result.1.2.1.1.ghost.acceptance = state.1.1.ghost.acceptance := by
  obtain ⟨answer, returned, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support
    setup codec checks context rest key Q j query state before ready result supported
  have equal : answer = value := Option.some.inj (returned.symm.trans normal)
  subst answer
  exact handler_none setup codec checks context _ Q j query _ _ reached absent

/-- A continuing monitor returns the literal optional callback value; it never synthesizes a public reply. -/
theorem observe_reply {State : Type} (counter : State → Nat) (marks : State → Marks)
    (query : ServerAuthSpec.Domain) (before : State × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × State) (value : ServerAuthSpec.Range query)
    (normal : (PqxdhServerAuthCtxStop.observe counter marks query before result).1 = some value) :
    result.1 = some value := by
  cases returned : result.1 with
  | none => simp only [PqxdhServerAuthCtxStop.observe, returned, reduceCtorEq] at normal
  | some answer =>
    simp only [PqxdhServerAuthCtxStop.observe, returned] at normal
    rcases query with coin | query
    · exact normal
    · cases query with
      | accept raw =>
        simp only [PqxdhServerAuthCtxStop.checkpoint] at normal
        split_ifs at normal
        · cases recorded : before.2 <;> simp_all only [reduceCtorEq]
        · exact normal
      | _ => exact normal

/-- Every continuing stopped callback without a successful public finish preserves acceptance after the actual complete callback work. -/
theorem stopped_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state.1, before.2))
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before))
    (value : ServerAuthSpec.Range query) (normal : result.1.1 = some value)
    (absent : finishRaw ⟨query, value⟩ = none) :
    result.1.2.1.1.1.ghost.acceptance = state.1.1.1.ghost.acceptance := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  simpa only [PqxdhServerAuthCtxStop.observe_state] using
    observed_none setup codec checks context rest key Q j query state.1 before ready inner reached value
      (observe_reply _ _ query state inner.1 value normal) absent

/-- The complete combined interpreter preserves acceptance on every continuing reply that is not a successful public finish. Callback readiness is derived from the actual invariant. -/
theorem interpreted_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (result : Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxObserverHistory.interpreted
      setup codec checks context rest key Q j query).run.run state))
    (value : ServerAuthSpec.Range query) (normal : result.1 = some value)
    (absent : finishRaw ⟨query, value⟩ = none) :
    result.2.1.1.1.1.ghost.acceptance = state.1.1.1.1.ghost.acceptance := by
  simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact stopped_none setup codec checks context rest key Q j query state.1 state.2
    (PqxdhServerAuthCtxReserve.valid_ready query (state.1, state.2.2) invariant.1)
    inner reached value normal absent

/-- A complete normal journal with no successful finish retains its initial acceptance exactly, across every adaptive callback and all failed source operations. -/
theorem journal_none (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (result : Option (Result × QueryLog ServerAuthSpec) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j)
      (PqxdhServerAuthApiJournal.record work)).run.run state))
    (answer : Result) (journal : QueryLog ServerAuthSpec) (normal : result.1 = some (answer, journal))
    (absent : acceptedRaw journal = none) :
    result.2.1.1.1.1.ghost.acceptance = state.1.1.1.1.ghost.acceptance := by
  induction work using OracleComp.inductionOn generalizing state result answer journal with
  | pure value =>
    change result ∈ support (pure (some (value, []), state)) at supported
    rw [mem_support_pure_iff] at supported
    exact congrArg (fun final => final.2.1.1.1.1.ghost.acceptance) supported
  | query_bind query next ih =>
    rw [PqxdhServerAuthFinishJournal.journal_query] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    cases returned : middle.1 with
    | none =>
      simp only [returned, mem_support_pure_iff] at supported
      simp only [supported, reduceCtorEq] at normal
    | some value =>
      simp only [returned, support_map] at supported
      obtain ⟨last, continued, rfl⟩ := supported
      cases tailReply : last.1 with
      | none => simp only [tailReply, Option.map_none, reduceCtorEq] at normal
      | some tailValue =>
        rcases tailValue with ⟨tailAnswer, tailJournal⟩
        have journalSame : journal = (⟨query, value⟩ :
            (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: tailJournal :=
          (congrArg Prod.snd (Option.some.inj (by simpa only [tailReply, Option.map_some] using normal))).symm
        rw [journalSame] at absent
        have each := List.findSome?_eq_none_iff.mp absent
        exact (ih value middle.2
          (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
            query state invariant middle reached value returned)
          last continued tailAnswer tailJournal tailReply
          (List.findSome?_eq_none_iff.mpr (fun event member => each event (List.mem_cons_of_mem _ member)))).trans
          (interpreted_none setup codec checks context rest key Q j query state invariant middle reached value returned
            (each _ List.mem_cons_self))

/-- Starting without acceptance, any actual accepted normal execution has a successful public finish in its literal adaptive journal. -/
theorem program_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (fresh : state.1.1.1.1.ghost.acceptance = none)
    (result : Option (Result × QueryLog ServerAuthSpec) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j)
      (PqxdhServerAuthApiJournal.record work)).run.run state))
    (answer : Result) (journal : QueryLog ServerAuthSpec) (normal : result.1 = some (answer, journal))
    (snap : Snapshot) (accepted : result.2.1.1.1.1.ghost.acceptance = some snap) :
    ∃ raw, acceptedRaw journal = some raw := by
  cases selected : acceptedRaw journal with
  | none =>
    have retained := journal_none setup codec checks context rest key Q j work state invariant result supported
      answer journal normal selected
    simp only [accepted, fresh, reduceCtorEq] at retained
  | some raw => exact ⟨raw, rfl⟩

/-- The original accepted normal experiment supplies its own successful public finish selector, with initialization and callback invariants discharged internally. -/
theorem run_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap) :
    ∃ raw, acceptedRaw journal = some raw := by
  have evaluated : (result.1.1, (result.1.2, result.2)) ∈ support
      ((PqxdhSelectedStateInterpreter.evaluate
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))).run).run
        (PqxdhServerAuthCtxObserverHistory.initial setup context)) := by
    change (result.1.1, (result.1.2, result.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [PqxdhServerAuthCtxObserverHistory.program_interpreted] at evaluated
  exact program_accepted setup codec checks context rest key Q j _ _
    (PqxdhServerAuthCtxObserverHistory.initial_invariant setup codec context key Q j)
    rfl _ evaluated () journal normal snap accepted

/-- An actual accepted owner supplies both the successful original public request and its final selected-frame receipt, unless the ordinary authentication observer wins. No public-occurrence premise is supplied. -/
theorem accepted_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      ∃ raw, acceptedRaw journal = some raw ∧ PqxdhServerAuthFinishFrameReceipt.Receipt codec raw result.2.1 := by
  obtain ⟨raw, selected⟩ := run_accepted setup codec checks adversary context rest key Q j
    result supported journal normal snap accepted
  exact (PqxdhServerAuthFinishJournal.execution_receipt setup codec checks adversary context rest key Q j
    result supported journal normal raw selected snap accepted owned notBad).imp_right
    (fun receipt => ⟨raw, selected, receipt⟩)

end BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.outcome_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.outcome_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.finish_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.skeleton_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.skeleton_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.handler_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.handler_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.observed_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.observed_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.observe_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.observe_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.stopped_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.stopped_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.interpreted_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.interpreted_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.journal_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.journal_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.program_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.program_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.run_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.run_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.accepted_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance.accepted_receipt

