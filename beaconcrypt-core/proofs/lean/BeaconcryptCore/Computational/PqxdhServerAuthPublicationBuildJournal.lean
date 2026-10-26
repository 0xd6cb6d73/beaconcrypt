import BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuiltRecord

/-! A successful public build retains its literal allocated source coordinate through all later callbacks. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop
open PqxdhServerAuthPublicationRecordReserve (Observed Reserved)
open PqxdhJointKdfGame PqxdhSecretInputKdf
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- New marks are set only at the fresh allocation coordinate. Every previously allocated coordinate keeps its exact old mark. -/
theorem allocated_step (query : ServerAuthSpec.Domain) (before after : HiddenState KemSK)
    (resources : ResourceStep query before.1.1 after.1.1) (marks : MarkStep query before.1 after.1)
    (index : Nat) (allocated : index < before.1.1.sessions) :
    index < after.1.1.sessions ∧ after.1.2.1 index = before.1.2.1 index := by
  cases query with
  | inl coin => exact ⟨resources.1 ▸ allocated, congrFun marks index⟩
  | inr query =>
      cases query with
      | accept raw =>
          refine ⟨by rw [resources.1]; omega, ?_⟩
          rcases marks with unchanged | inserted
          · exact congrFun unchanged index
          · rw [inserted, Function.update_of_ne (Nat.ne_of_lt allocated)]
      | _ => exact ⟨resources.1 ▸ allocated, congrFun marks index⟩

/-- The complete normal adaptive source preserves the exact mark of an already allocated coordinate, not merely marks already known true. -/
theorem allocated_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (index : Nat) (allocated : index < before.1.1.1.sessions)
    (result : Option Result × (Local KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run before))
    (reply : Result) (normal : result.1 = some reply) :
    index < result.2.1.1.1.sessions ∧ result.2.1.1.2.1 index = before.1.1.2.1 index := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨allocated, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      cases returned : middle.1 with
      | none =>
          simp only [returned, Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases normal
      | some value =>
          simp only [returned, Option.elim_some] at supported
          have footprint := PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j
            query before middle reached value returned
          have step := allocated_step query before.1 middle.2.1 footprint.1 footprint.2 index allocated
          have tail := ih value middle.2 step.1 supported
          exact ⟨tail.1, tail.2.trans step.2⟩

/-- The public journal inserts its literal query and returned reply only after the complete callback. -/
theorem journal_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (next : ServerAuthSpec.Range query → OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
      (PqxdhServerAuthApiJournal.record (ServerAuthSpec.query query >>= next))).run.run state) = (do
      let actual ← (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state
      match actual.1 with
      | none => pure (none, actual.2)
      | some reply =>
          (fun result => (result.1.map (fun value => (value.1, (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: value.2)), result.2)) <$>
            ((simulateQ (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
              (PqxdhServerAuthApiJournal.record (next reply))).run.run actual.2)) := by
  rw [PqxdhServerAuthApiJournal.record, run_simulateQ_loggingOracle_query_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply bind_congr
  intro actual
  cases actual.1 <;> simp only [Option.elim_none, Option.elim_some, StateT.run_pure,
    simulateQ_map, OptionT.run_map, StateT.run_map]
  rfl

/-- A genuine successful build whose allocated coordinate is marked in the final source supplies every later selected record's actual response-writer witnesses. Original prefix validity and reservation are operational invariants, and the suffix keeps every original component effect. -/
theorem successful_suffix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK × Option Nat) (before : Observed)
    (reserved : Reserved state before.1) (valid : ResourceValid state.1.1.1)
    (response : PqxdhServerRegistrationPublication.Response)
    (middle : ((Option (Option PqxdhServerRegistrationPublication.Response)) × (Local KemSK × Option Nat)) × Observed)
    (built : middle ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run state)).run before))
    (returned : middle.1.1 = some (some response))
    (work : OracleComp ServerAuthSpec Result)
    (last : (Option Result × (Local KemSK × Option Nat)) × Observed)
    (continued : last ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
        work).run.run middle.1.2)).run middle.2))
    (reply : Result) (normal : last.1.1 = some reply) (marked : last.1.2.1.1.2.1 index = true) :
    ∃ token, state.1.1.1.pending index = some token ∧
      ∀ entry ∈ last.2.1.seals,
        PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload state.1.1.1.server response entry := by
  have actual := PqxdhServerAuthPublicationRecordReserve.observed_support setup.source codec.frameRead key _ before middle built
  obtain ⟨token, present⟩ := PqxdhServerAuthPublicationBuiltRecord.build_present setup codec checks context rest Q j index payload
    state middle.1.2 response (by rw [← returned]; exact actual)
  have allocated := valid index token present
  have footprint := PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j
    (.inr (.build index payload)) state middle.1 actual (some response) returned
  have step := allocated_step (.inr (.build index payload)) state.1 middle.1.2.1 footprint.1 footprint.2 index allocated
  have suffix := allocated_program setup codec checks context rest Q j work middle.1.2 index step.1 last.1
    (PqxdhServerAuthPublicationRecordReserve.observed_support setup.source codec.frameRead key _ middle.2 last continued) reply normal
  have currentMark : state.1.1.2.1 index = true := (suffix.2.trans step.2).symm.trans marked
  have empty := PqxdhServerAuthPublicationRecordReserve.selected_empty state before.1 reserved index token currentMark present
  have records := PqxdhServerAuthPublicationBuiltRecord.stopped_at setup codec checks context rest Q j index token payload
    state middle.1.2 currentMark present before.1 middle.2.1 empty response
      (by rw [← returned]; exact PqxdhFirstBeaconRecordCanonical.observed_monitor _ _ _ _ before middle built)
  have closed := PqxdhServerAuthPublicationRecordReserve.selected_closed setup codec checks context rest Q j index payload state
    reserved.1 token currentMark present middle.1 actual (some response) returned
  have same := PqxdhServerAuthPublicationRecordReserve.suffix_records setup codec checks context rest key Q j work middle.1.2
    middle.2 closed.1 closed.2 last continued
  exact ⟨token, present, fun entry found => records entry (same ▸ found)⟩

/-- An actual successful public-journal entry at a finally marked coordinate supplies the response-writer origin of every final selected record. The proof follows the literal callback occurrence, not a serialization preimage or an equal-key session. -/
theorem public_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK × Option Nat) (before : Observed)
    (reserved : Reserved state before.1) (valid : ResourceValid state.1.1.1)
    (result : (Option (Result × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
        (PqxdhServerAuthApiJournal.record work)).run.run state)).run before))
    (answer : Result) (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some (answer, journal))
    (index : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (published : (⟨.inr (.build index payload), some response⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal)
    (marked : result.1.2.1.1.2.1 index = true) :
    ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState),
      ∀ entry ∈ result.2.1.seals, PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  induction work using OracleComp.inductionOn generalizing state before result answer journal with
  | pure value =>
      change result ∈ support (pure ((some (value, []), state), before)) at supported
      rw [mem_support_pure_iff] at supported
      subst result
      simp only [Option.some.injEq, Prod.mk.injEq] at normal
      rw [← normal.2] at published
      cases published
  | query_bind query next ih =>
      rw [journal_query] at supported
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      cases returned : middle.1.1 with
      | none =>
          simp only [returned, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases normal
      | some value =>
          simp only [returned, simulateQ_map, StateT.run_map, support_map] at supported
          obtain ⟨last, continued, rfl⟩ := supported
          cases tailReply : last.1.1 with
          | none => simp only [tailReply, Option.map_none, reduceCtorEq] at normal
          | some tailValue =>
              rcases tailValue with ⟨tailAnswer, tailJournal⟩
              have journalSame : journal = (⟨query, value⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: tailJournal :=
                (congrArg Prod.snd (Option.some.inj (by simpa only [tailReply, Option.map_some] using normal))).symm
              rw [journalSame] at published
              rcases List.mem_cons.mp published with head | tail
              · have querySame := congrArg Sigma.fst head
                cases querySame
                have valueSame : some response = value := eq_of_heq (Sigma.mk.inj_iff.mp head).2
                subst value
                obtain ⟨token, _, records⟩ := successful_suffix setup codec checks context rest key Q j index payload
                  state before reserved valid response middle reached returned
                  (PqxdhServerAuthApiJournal.record (next (some response))) last continued
                  (tailAnswer, tailJournal) tailReply marked
                exact ⟨token, state.1.1.1.server, records⟩
              · have actual := PqxdhServerAuthPublicationRecordReserve.observed_support setup.source codec.frameRead key _ before middle reached
                have footprint := PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j query
                  state middle.1 actual value returned
                exact ih value middle.1.2 middle.2
                  (PqxdhServerAuthPublicationRecordReserve.stopped_reserved setup codec checks context rest key Q j query
                    state before reserved middle reached value returned)
                  (ResourceStep.valid query state.1.1.1 middle.1.2.1.1.1 valid footprint.1)
                  last continued tailAnswer tailJournal tailReply tail marked

/-- The literal empty source and observer histories discharge every local reservation and allocation premise of the whole public-journal result. -/
theorem initial_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (index : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (published : (⟨.inr (.build index payload), some response⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal)
    (marked : result.1.2.1.1.2.1 index = true) :
    ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState),
      ∀ entry ∈ result.2.1.seals, PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry :=
  public_records setup codec checks context rest key Q j (adversary (contextInput setup false context))
    (PqxdhServerAuthCtxReserve.initial setup context).1 _
    (PqxdhServerAuthPublicationRecordReserve.initial_reserved setup context)
    (by intro index token found; cases found) result supported () journal normal index payload response published marked

/-- A retained actual selected record requires a reached selected coordinate in the source's own monitor. -/
theorem marked_of_record (state : Local KemSK × Option Nat)
    (observer : RawCtxSelectedAuthenticationObserver.State) (reserved : Reserved state observer)
    (entry : CtxRomAuth.CtxSuccessfulSeal) (member : entry ∈ observer.seals) :
    ∃ index, state.1.1.2.1 index = true := by
  cases first : state.2 with
  | none =>
      have empty := reserved.2 (by simp only [buildReserve, first])
      rw [empty] at member
      cases member
  | some index => exact ⟨index, reserved.1.1.present index first⟩

/-- Every saved raw-attempt prefix remains a subhistory of the current selected seals. -/
def Retained (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∀ attempt ∈ observer.attempts, ∀ entry ∈ attempt.sealsBefore, entry ∈ observer.seals

/-- The literal observer retains prior records through every query, including failed seal and raw replies. -/
theorem retained_step (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (reply : AdaptiveCtxDynamicKnownKeys.Spec.Range query)
    (state : RawCtxSelectedAuthenticationObserver.State) (retained : Retained state) :
    Retained (RawCtxSelectedAuthenticationObserver.step query reply state) := by
  rcases query with (((coin | (hash | input)) | raw) | known) <;> simp only [RawCtxSelectedAuthenticationObserver.step, Retained] at *
  all_goals first | exact retained | (cases reply <;> simp only [List.mem_cons, forall_eq_or_imp])
  all_goals first | exact retained | exact fun attempt found entry prior => Or.inr (retained attempt found entry prior) | exact ⟨fun _ found => found, retained⟩

/-- The complete ordinary component execution preserves every saved attempt's literal seal prefix, with arbitrary earlier histories when initially retained. -/
theorem retained_program (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) (key : CtxRomAuth.CtxKey)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) (state : Observed)
    (retained : Retained state.1) (result : Result × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed real decode crypto key) work).run state)) :
    Retained result.2.1 := by
  apply simulateQ_run_preservesInv (RawCtxSelectedAuthenticationObserver.observed real decode crypto key)
    (fun state => Retained state.1) ?_ work state retained result supported
  intro query state retained result supported
  simp only [RawCtxSelectedAuthenticationObserver.observed, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  exact retained_step query reply.1 state.1 retained

/-- The actual accepted record and source partner identify the final marked owner. Empty source histories establish the operational invariants; no mark or seal-origin premise is supplied by the caller. -/
theorem receipt_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost)
    (receipt : PqxdhServerAuthPublicationOccurrence.ReceiptAt setup codec context j.val snap result.2.1) :
    result.1.2.1.1.2.1 j.val = true := by
  obtain ⟨message, reply, bytes, sealContext, entry, attempt, target,
    touched, rooted, beacon, _, _, _, attempted, _, _, sealed, _⟩ := receipt
  have retained := retained_program true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
    (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)
    (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
    (by intro attempt found; cases found) result supported
  have reserved := PqxdhServerAuthPublicationRecordReserve.program_reserved setup codec checks context rest key Q j
    (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
    (PqxdhServerAuthCtxReserve.initial setup context).1 _
    (PqxdhServerAuthPublicationRecordReserve.initial_reserved setup context)
    result supported ((), journal) normal
  obtain ⟨index, marked⟩ := marked_of_record result.1.2 result.2.1 reserved entry
    (retained attempt attempted entry sealed)
  have erased : ((result.1.1.map Prod.fst, result.1.2), result.2) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
    rw [← PqxdhServerAuthPublicationOccurrence.observed_erase setup codec checks adversary Q j context rest key, support_map]
    exact ⟨result, supported, rfl⟩
  have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j adversary
    _ erased (by simp only [normal, Option.map_some])
  have same := PqxdhServerAuthPublicationOccurrence.marked_owner setup context Q j result.1.2.1
    invariant.2.trace invariant.2.history snap accepted owned unique j.val
    ⟨message, reply, bytes, touched, rooted, beacon⟩ index marked
  exact same ▸ marked

/-- A successful public build at the accepted owner is either accompanied by the ordinary authentication observer's win, or supplies the actual response writers for every retained selected record. All allocation, mark and empty-history obligations come from this same original execution. -/
theorem accepted_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthPublicationOccurrence.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (normal : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost)
    (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (published : (⟨.inr (.build j.val payload), some response⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      PqxdhServerAuthPublicationOccurrence.ReceiptAt setup codec context j.val snap result.2.1 ∧
      ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState),
        ∀ entry ∈ result.2.1.seals,
          PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  rcases PqxdhServerAuthPublicationOccurrence.journal_receipt setup codec checks adversary context rest key Q j writable
    result supported journal normal snap accepted owned notBad unique with won | ⟨_, receipt⟩
  · exact Or.inl won
  · exact Or.inr ⟨receipt, initial_records setup codec checks adversary context rest key Q j result supported journal normal
      j.val payload response published
      (receipt_marked setup codec checks adversary context rest key Q j result supported journal normal snap accepted owned unique receipt)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.allocated_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.allocated_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.allocated_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.allocated_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.journal_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.journal_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.successful_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.successful_suffix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.public_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.public_records
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.initial_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.initial_records
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.marked_of_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.marked_of_record
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.retained_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.retained_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.retained_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.retained_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.receipt_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.receipt_marked
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.accepted_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal.accepted_records
