import BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient

/-! Actual public finish occurrences retain their original raw decoded frame through complete adaptive continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthFinishFrameReceipt PqxdhSecretInputKdf
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Every complete interpreted component continuation preserves earlier selected records, including all failed calls and private cache changes. -/
theorem observed_seals (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxRomAuth.CtxKey)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : Result × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed real decode crypto key) work).run before)) :
    before.1.seals ⊆ result.2.1.seals := by
  apply simulateQ_run_preservesInv (RawCtxSelectedAuthenticationObserver.observed real decode crypto key)
    (fun state => before.1.seals ⊆ state.1.seals) ?_ work before (List.Subset.refl _) result supported
  intro query state retained result supported
  simp only [RawCtxSelectedAuthenticationObserver.observed, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rcases query with (((coin | (hash | input)) | raw) | known) <;>
    first | exact retained | skip
  cases reply.1 <;> simp only [RawCtxSelectedAuthenticationObserver.step]
  · exact retained
  · exact fun entry member => List.mem_cons_of_mem _ (retained member)

/-- Alternatives retain the original selected receipt and the explicitly separate ordinary-root route. -/
def Alternatives (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (raw : Pqxdh.Bytes) (state : Local KemSK)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) observer = true ∨
    PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context state ∨ Receipt codec raw observer

/-- Every actual API callback retains an earlier original-frame receipt or its ordinary alternative, without removing failed calls or private state effects. -/
theorem handler_retained (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (raw : Pqxdh.Bytes)
    (state : Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (retained : Alternatives setup codec context raw state before.1)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Alternatives setup codec context raw result.1.2 result.2.1 := by
  rcases retained with winning | ⟨bytes, input, present⟩ | ⟨entry, member, frame, decoded, same⟩
  · exact Or.inl (PqxdhFirstBeaconRecordCanonical.observed_won _ _ _ _ before winning result supported)
  · obtain ⟨answer, _, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support setup codec checks context
      rest key Q j query state before ready result supported
    exact Or.inr (Or.inl ⟨bytes, beaconInput_prefix setup context.seed context.scalar _ _ bytes input
      (PqxdhServerAuthCtxAcceptanceHistory.handler_grows setup codec checks context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
        (PqxdhServerAuthCtxState.project (state, before.2)) _ reached).touches,
      (PqxdhServerAuthCtxChronology.handler_history setup codec checks context
        (PqxdhServerAuthCtxMaterial.output key rest) Q j query
        (PqxdhServerAuthCtxState.project (state, before.2)) invariant.clean _ reached).1 bytes present⟩)
  · exact Or.inr (Or.inr ⟨entry, observed_seals _ _ _ _ _ before result supported member, frame, decoded, same⟩)

/-- Post-callback reservation checks retain earlier receipts and ordinary alternatives, including all work before refusal. -/
theorem stopped_retained (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (raw : Pqxdh.Bytes)
    (state : Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state.1, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state.1 before)
    (retained : Alternatives setup codec context raw state.1 before.1)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before)) :
    Alternatives setup codec context raw result.1.2.1 result.2.1 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  simpa only [PqxdhServerAuthCtxStop.observe_state] using
    handler_retained setup codec checks context key rest Q j query raw state.1 before ready invariant retained inner reached

/-- The ordinary interpreted callback preserves the earlier public-frame alternatives on the same complete state. Its unused-endpoint condition is supplied by the concrete reservation invariant. -/
theorem interpreted_retained (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (retained : Alternatives setup codec context raw state.1.1 state.2.1)
    (result : Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxObserverHistory.interpreted
      setup codec checks context rest key Q j query).run.run state)) :
    Alternatives setup codec context raw result.2.1.1 result.2.2.1 := by
  simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact stopped_retained setup codec checks context key rest Q j query raw state.1 state.2
    (PqxdhServerAuthCtxReserve.valid_ready query (state.1, state.2.2) invariant.1)
    invariant.2 retained inner reached

/-- A full adaptive continuation retains the successful original-frame alternatives with every reply-dependent branch and complete source/observer state. -/
theorem program_retained (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (retained : Alternatives setup codec context raw state.1.1 state.2.1)
    (result : Option Result × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j) work).run.run state)) :
    Alternatives setup codec context raw result.2.1.1 result.2.2.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    simpa only [supported] using retained
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    cases reply : middle.1 with
    | none =>
      simp only [reply, Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
      simpa only [supported] using
        interpreted_retained setup codec checks context rest key Q j query raw state invariant retained middle reached
    | some value =>
      simp only [reply, Option.elim_some] at supported
      exact ih value middle.2
        (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
          query state invariant middle reached value reply)
        (interpreted_retained setup codec checks context rest key Q j query raw state invariant retained middle reached)
        supported

/-- A successful interpreted finish creates its receipt in the exact same combined source/observer state used by adaptive continuation preservation. -/
theorem interpreted_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (raw payload : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (result : Option (Option Pqxdh.Bytes) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxObserverHistory.interpreted
      setup codec checks context rest key Q j (.inr (.finish raw))).run.run state))
    (returned : result.1 = some (some payload)) :
    Alternatives setup codec context raw result.2.1.1 result.2.2.1 := by
  simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact stopped_receipt setup codec checks context key rest Q j raw payload state.1 state.2 invariant.2 inner reached returned

/-- The actual public journal records a reply after its full optional callback, retaining the complete continuation and state on every refusal branch. -/
theorem journal_query {σ : Type} (impl : QueryImpl ServerAuthSpec (OptionT (StateT σ ProbComp)))
    (query : ServerAuthSpec.Domain) (next : ServerAuthSpec.Range query → OracleComp ServerAuthSpec Result)
    (state : σ) :
    ((simulateQ impl (PqxdhServerAuthApiJournal.record (ServerAuthSpec.query query >>= next))).run.run state) = (do
      let actual ← (impl query).run.run state
      match actual.1 with
      | none => pure (none, actual.2)
      | some reply =>
          (fun result => (result.1.map (fun value => (value.1,
            (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: value.2)), result.2)) <$>
            ((simulateQ impl (PqxdhServerAuthApiJournal.record (next reply))).run.run actual.2)) := by
  rw [PqxdhServerAuthApiJournal.record, run_simulateQ_loggingOracle_query_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply bind_congr
  intro actual
  cases actual.1 <;> simp only [Option.elim_none, Option.elim_some, StateT.run_pure,
    simulateQ_map, OptionT.run_map, StateT.run_map]
  rfl

/-- Any actual successful public finish occurrence supplies its original raw-frame alternatives in the final state of the same complete adaptive journaled execution. -/
theorem journal_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (result : Option (Result × QueryLog ServerAuthSpec) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j)
      (PqxdhServerAuthApiJournal.record work)).run.run state))
    (answer : Result) (journal : QueryLog ServerAuthSpec) (normal : result.1 = some (answer, journal))
    (raw payload : Pqxdh.Bytes)
    (member : (⟨.inr (.finish raw), some payload⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal) :
    Alternatives setup codec context raw result.2.1.1 result.2.2.1 := by
  induction work using OracleComp.inductionOn generalizing state result answer journal with
  | pure value =>
    change result ∈ support (pure (some (value, []), state)) at supported
    rw [mem_support_pure_iff] at supported
    simp only [supported, Option.some.injEq, Prod.mk.injEq] at normal
    simp only [← normal.2, List.not_mem_nil] at member
  | query_bind query next ih =>
    rw [journal_query] at supported
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
        have journalSame : journal = (⟨query, value⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: tailJournal :=
          (congrArg Prod.snd (Option.some.inj (by simpa only [tailReply, Option.map_some] using normal))).symm
        rw [journalSame] at member
        rcases List.mem_cons.mp member with head | tail
        · have querySame := congrArg Sigma.fst head
          cases querySame
          have valueSame : some payload = value := eq_of_heq (Sigma.mk.inj_iff.mp head).2
          subst value
          exact program_retained setup codec checks context rest key Q j
            (PqxdhServerAuthApiJournal.record (next (some payload))) raw middle.2
            (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
              (.inr (.finish raw)) state invariant middle reached (some payload) returned)
            (interpreted_receipt setup codec checks context rest key Q j raw payload state invariant middle reached returned)
            last continued
        · exact ih value middle.2
            (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
              query state invariant middle reached value returned)
            last continued tailAnswer tailJournal tailReply tail

/-- The public raw selector names an actual successful finish in the same journal. -/
theorem accepted_member (journal : QueryLog ServerAuthSpec) (raw : Pqxdh.Bytes)
    (accepted : PqxdhServerAuthRecordPublicationEvent.acceptedRaw journal = some raw) :
    ∃ payload, (⟨.inr (.finish raw), some payload⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal := by
  obtain ⟨event, member, selected⟩ := List.exists_of_findSome?_eq_some accepted
  rcases event with ⟨coin | query, reply⟩
  · cases selected
  · cases query <;> simp only [PqxdhServerAuthRecordPublicationEvent.finishRaw, reduceCtorEq] at selected
    cases reply <;> simp only [Option.some.injEq, reduceCtorEq] at selected
    exact ⟨_, selected ▸ member⟩

/-- The actual complete journaled run carries the original successful raw-frame receipt to its final state, with no supplied intermediate trace or target-origin premise. -/
theorem run_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
    (raw : Pqxdh.Bytes)
    (accepted : PqxdhServerAuthRecordPublicationEvent.acceptedRaw journal = some raw) :
    Alternatives setup codec context raw result.1.2.1 result.2.1 := by
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
  obtain ⟨payload, member⟩ := accepted_member journal raw accepted
  exact journal_receipt setup codec checks context rest key Q j _ _
    (PqxdhServerAuthCtxObserverHistory.initial_invariant setup codec context key Q j)
    _ evaluated () journal normal raw payload member

/-- The accepted owner in the same normal execution discharges the ordinary-root route. The remaining receipt decodes the literal original public request, with no additional message or cryptographic contract. -/
theorem execution_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
    (raw : Pqxdh.Bytes)
    (selectedRaw : PqxdhServerAuthRecordPublicationEvent.acceptedRaw journal = some raw)
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      Receipt codec raw result.2.1 := by
  have erased : ((result.1.1.map Prod.fst, result.1.2), result.2) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
    rw [← PqxdhServerAuthPublicationOccurrence.observed_erase setup codec checks adversary Q j context rest key]
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  have continues : result.1.1.map Prod.fst = some () := by simp only [normal, Option.map_some]
  have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j
    adversary _ erased continues
  have source := PqxdhServerAuthCtxObserverEvent.execution_source setup codec checks adversary context rest key Q j
    _ erased continues
  obtain ⟨bytes, selected, input⟩ := PqxdhServerAuthPublicationAcceptance.accepted_input setup codec checks adversary context
    (PqxdhServerAuthCtxMaterial.output key rest) Q j _ source snap accepted owned notBad
  rcases run_receipt setup codec checks adversary context rest key Q j result supported journal normal raw selectedRaw with
    won | ⟨other, otherInput, occupied⟩ | receipt
  · exact Or.inl won
  · have equal : other = bytes := Option.some.inj (otherInput.symm.trans input)
    subst other
    exact (occupied (invariant.2.clean bytes selected)).elim
  · exact Or.inr receipt

end BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.observed_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.observed_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.handler_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.handler_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.stopped_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.stopped_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.interpreted_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.interpreted_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.program_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.program_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.interpreted_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.interpreted_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.journal_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.journal_query

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.journal_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.journal_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.accepted_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.accepted_member

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.run_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.run_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.execution_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishJournal.execution_receipt

