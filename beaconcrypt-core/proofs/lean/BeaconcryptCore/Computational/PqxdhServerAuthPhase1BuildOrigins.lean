import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins

/-! The actual consumed builder token retains its earlier verified Phase1 occurrence. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthPendingBudget PqxdhSecretInputKdf
open PqxdhServerAuthPhase1Origins
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
abbrev Observed := PqxdhServerAuthPublicationRecordReserve.Observed

/-- The complete interpreted handler transports the live-token receipt through the actual source projection. -/
theorem handler_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (journal : QueryLog ServerAuthSpec)
    (state : Local KemSK) (before : Observed)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (origins : Origins setup codec checks (context.publicValue setup) journal state.1.1)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before))
    (answer : ServerAuthSpec.Range query) (normal : result.1.1 = some answer) :
    Origins setup codec checks (context.publicValue setup) (journal ++ [⟨query, answer⟩]) result.1.2.1.1 := by
  obtain ⟨reply, returned, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support setup codec checks context
    rest key Q j query state before ready result supported
  have same : reply = answer := Option.some.inj (returned.symm.trans normal)
  subst reply
  exact PqxdhServerAuthPhase1Origins.handler_origins setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) journal query
    (PqxdhServerAuthCtxState.project (state, before.2)) _ reached origins

/-- A continuing actual checkpoint appends its unchanged public reply and retains the source pending receipt. -/
theorem stopped_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (journal : QueryLog ServerAuthSpec)
    (state : Local KemSK × Option Nat) (before : Observed)
    (valid : PqxdhServerAuthCtxReserve.Valid (state, before.2))
    (origins : Origins setup codec checks (context.publicValue setup) journal state.1.1.1)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)).run before))
    (answer : ServerAuthSpec.Range query) (normal : result.1.1 = some answer) :
    Origins setup codec checks (context.publicValue setup) (journal ++ [⟨query, answer⟩]) result.1.2.1.1.1 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key)
    ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before) at supported
  simp only [PqxdhServerAuthCtxReserve.stopped, stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  cases returned : inner.1.1 with
  | none =>
    simp only [observe, returned] at normal
    cases normal
  | some reply =>
    have same := checkpoint_reply query state.1.1.1.sessions inner.1.2.1.2.1 state.2 reply answer
      (by simpa only [observe, returned] using normal)
    subst answer
    have kept := handler_origins setup codec checks context rest key Q j query journal state.1 before
      (PqxdhServerAuthCtxReserve.valid_ready query (state, before.2) valid) origins inner reached reply returned
    simpa only [observe_state] using kept

/-- The successful acceptance occurs in the literal journal prefix before this successful builder occurrence. -/
def BeforeBuild (journal : QueryLog ServerAuthSpec) (index : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response) (raw : Pqxdh.Bytes) : Prop :=
  ∃ earlier suffix : QueryLog ServerAuthSpec,
    journal = earlier ++ (⟨.inr (.build index payload), some response⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :: suffix ∧
    (⟨.inr (.accept raw), some index⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ earlier

/-- The actual successful builder occurrence joins its own consumed token's earlier verified acceptance to every retained selected record's exact response writers. -/
theorem public_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (oldJournal : QueryLog ServerAuthSpec) (state : Local KemSK × Option Nat) (before : Observed)
    (reserved : PqxdhServerAuthPublicationRecordReserve.Reserved state before.1)
    (allocated : ResourceValid state.1.1.1)
    (valid : PqxdhServerAuthCtxReserve.Valid (state, before.2))
    (origins : Origins setup codec checks (context.publicValue setup) oldJournal state.1.1.1)
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
    ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState) (raw : Pqxdh.Bytes),
      TokenReceipt setup codec checks (context.publicValue setup) raw token ∧
      BeforeBuild (oldJournal ++ journal) index payload response raw ∧
      ∀ entry ∈ result.2.1.seals, PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  induction work using OracleComp.inductionOn generalizing oldJournal state before result answer journal with
  | pure value =>
      change result ∈ support (pure ((some (value, []), state), before)) at supported
      rw [mem_support_pure_iff] at supported
      subst result
      simp only [Option.some.injEq, Prod.mk.injEq] at normal
      rw [← normal.2] at published
      cases published
  | query_bind query next ih =>
      rw [PqxdhServerAuthPublicationBuildJournal.journal_query] at supported
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
                obtain ⟨token, present, records⟩ := PqxdhServerAuthPublicationBuildJournal.successful_suffix setup codec checks context rest key Q j index payload
                  state before reserved allocated response middle reached returned
                  (PqxdhServerAuthApiJournal.record (next (some response))) last continued
                  (tailAnswer, tailJournal) tailReply marked
                obtain ⟨raw, accepted, receipt⟩ := origins index token present
                exact ⟨token, state.1.1.1.server, raw, receipt,
                  ⟨oldJournal, tailJournal, by rw [journalSame], accepted⟩, records⟩
              · have actual := PqxdhServerAuthPublicationRecordReserve.observed_support setup.source codec.frameRead key _ before middle reached
                have footprint := PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j query
                  state middle.1 actual value returned
                have journalEq : oldJournal ++ journal =
                    (oldJournal ++ [⟨query, value⟩]) ++ tailJournal := by
                  rw [journalSame]
                  exact (List.append_assoc oldJournal [⟨query, value⟩] tailJournal).symm
                rw [journalEq]
                exact ih value (oldJournal ++ [⟨query, value⟩]) middle.1.2 middle.2
                  (PqxdhServerAuthPublicationRecordReserve.stopped_reserved setup codec checks context rest key Q j query
                    state before reserved middle reached value returned)
                  (ResourceStep.valid query state.1.1.1 middle.1.2.1.1.1 allocated footprint.1)
                  (PqxdhServerAuthCtxObserverHistory.stopped_valid setup codec checks context rest key Q j query
                    state before valid middle reached value returned)
                  (stopped_origins setup codec checks context rest key Q j query oldJournal state before valid origins
                    middle reached value returned)
                  last continued tailAnswer tailJournal tailReply tail marked

/-- Literal empty pending and observer histories discharge every provenance, allocation and reservation premise of the consumed-token join. -/
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
    ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState) (raw : Pqxdh.Bytes),
      TokenReceipt setup codec checks (context.publicValue setup) raw token ∧
      BeforeBuild journal index payload response raw ∧
      ∀ entry ∈ result.2.1.seals, PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  simpa only [List.nil_append] using
    public_records setup codec checks context rest key Q j (adversary (contextInput setup false context))
      [] (PqxdhServerAuthCtxReserve.initial setup context).1 _
      (PqxdhServerAuthPublicationRecordReserve.initial_reserved setup context)
      (by intro index token found; cases found)
      (PqxdhServerAuthCtxReserve.initial_valid setup context)
      (by intro index token found; cases found)
      result supported () journal normal index payload response published marked

/-- An actual accepted owner with a successful build has either the existing ordinary observer win or the same consumed token's earlier verification and exact response-writer receipt. -/
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
      ∃ (token : PqxdhServerRelatedRootConsumer.Returned) (server : ServerState) (raw : Pqxdh.Bytes),
        TokenReceipt setup codec checks (context.publicValue setup) raw token ∧
        BeforeBuild journal j.val payload response raw ∧
        ∀ entry ∈ result.2.1.seals,
          PqxdhServerAuthPublicationBuiltRecord.At codec token.pending payload server response entry := by
  rcases PqxdhServerAuthPublicationOccurrence.journal_receipt setup codec checks adversary context rest key Q j writable
    result supported journal normal snap accepted owned notBad unique with won | ⟨_, receipt⟩
  · exact Or.inl won
  · exact Or.inr ⟨receipt, initial_records setup codec checks adversary context rest key Q j result supported journal normal
      j.val payload response published
      (PqxdhServerAuthPublicationBuildJournal.receipt_marked setup codec checks adversary context rest key Q j result supported
        journal normal snap accepted owned unique receipt)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.handler_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.handler_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.stopped_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.stopped_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.public_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.public_records

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.initial_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.initial_records

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.accepted_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins.accepted_records
