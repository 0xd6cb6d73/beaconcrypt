import BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource

/-! Actual accepted selected-record receipts, without requiring the older W1/W2 violation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthDesignation
open PqxdhSecretInputKdf PqxdhJointKdfGame CtxRomAuth PqxdhServerAuthCtxStop PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Actual acceptance, owner attribution and absence of sticky refusal identify the selected input even when the older authentication violation is false. -/
theorem accepted_input (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary false context Q j
      (factorServices setup codec checks context value)))
    (snap : Snapshot) (accepted : result.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.1.ghost = some j)
    (notBad : result.1.2.2.bad = false) :
    ∃ bytes, result.1.2.2.hidden = some bytes ∧
      beaconInput setup context.seed context.scalar result.1.1.ghost.touches = some bytes := by
  have established := accepted_established setup context Q j result.1.1 result.1.2.2
    (PqxdhServerAuthCtxAcceptanceHistory.run_history setup codec checks adversary false context value Q j result supported)
    (run_resolved setup codec checks adversary false context value Q j result supported)
    (run_covered setup codec checks adversary false context value Q j result supported).2 snap accepted owned
  cases hidden : result.1.2.2.hidden with
  | none =>
      simp only [Established, hidden, Option.isSome_none, notBad, Bool.false_eq_true, or_self] at established
  | some bytes =>
      have trace := PqxdhServerAuthCtxStop.run_trace setup codec checks context Q j (factorServices setup codec checks context value)
        adversary false result supported
      exact ⟨bytes, rfl, PqxdhServerAuthCtxStop.selected_input setup context Q j result.1.1.ghost
        trace.shape.once owned bytes (trace.selected bytes hidden)⟩

/-- The real accepted finish supplies its exact component request, actual optional plaintext, attempt-time seal history and a matching earlier record unless the ordinary authentication observer wins. -/
theorem program_receipt (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        source.crypto key)
      (PqxdhServerAuthFinishMaterial.program source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      let prepared := PqxdhPhase2DhRootConsumer.cleared pending
      let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
      ∃ (bytes componentBytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
        (kernel : ConcreteRatchetKernel) (entry : CtxSuccessfulSeal),
        codec.application prepared.response = some bytes ∧
        RawCtxUniversalDecoder.decoder codec.frameRead componentBytes = some target ∧
        PqxdhPhase2LocalMatching.LocalTarget codec.frameRead bytes candidate staged.opened target ∧
        PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged ∧
        ⟨componentBytes, some staged.opened.plaintext, before.1.seals⟩ ∈ after.1.attempts ∧
        entry ∈ before.1.seals ∧ target.toLegacy.sameFullTupleAsSuccessfulSeal entry ∧
        staged.opened.plaintext = entry.input.plaintext := by
  classical
  have monitored := PqxdhFirstBeaconRecordCanonical.observed_monitor
    (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key
    (PqxdhServerAuthFinishMaterial.program source codec rest pending) before (some staged, after) supported
  obtain ⟨bytes, componentBytes, target, kernel, application, decoded, delivery, success, attempt⟩ :=
    PqxdhServerAuthFinishReceipt.program_target source codec rest pending staged before.1 after.1 monitored
  by_cases winning : RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true
  · exact Or.inl winning
  · right
    have matched : ∃ entry ∈ before.1.seals, target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
      by_contra absent
      have fresh : ∀ entry ∈ before.1.seals, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry :=
        fun entry member same => absent ⟨entry, member, same⟩
      exact winning (PqxdhPhase2LocalMatching.won_of_attempt _ _ _ attempt
        (PqxdhPhase2LocalMatching.attempt_accepted _ _ target decoded _ _ fresh))
    obtain ⟨entry, member, same⟩ := matched
    have finalGood := RawCtxSelectedPlaintextOrigins.schedule_good
      (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key
      (PqxdhServerAuthFinishMaterial.program source codec rest pending) before good (some staged, after) supported
    have plaintext := finalGood.2.2 _ attempt target decoded entry member same (by simp)
    exact ⟨bytes, componentBytes, target, kernel, entry, application, decoded, delivery, success,
      attempt, member, same, Option.some.inj plaintext⟩

/-- A matching complete CTX tuple implies the exact tag predicate used by the before-raw capture, without reconstructing the record from source writer bytes. -/
theorem matching_hit (decode : AdaptiveCtxReceive.RawDecoder)
    (raw : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target) (entry : CtxSuccessfulSeal)
    (decoded : decode raw = some target) (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    PqxdhServerAuthPublicationGuess.Hit (PqxdhServerAuthPublicationRandom.decodedTag decode)
      (some (entry.record, raw)) := by
  have parsed := congrArg Pqxdh.decodeRecord same.2.2
  simp only [decodeRecord_romRecord, Option.some.injEq] at parsed
  have tag := congrArg Pqxdh.RecordCipher.tag parsed
  simp only [PqxdhServerAuthPublicationGuess.Hit, PqxdhServerAuthPublicationRandom.decodedTag, decoded]
  exact congrArg some (Subtype.ext tag)

/-- An actual accepted snapshot retains its partner-indexed cryptographic seal and the exact component attempt and earlier record. This predicate deliberately asserts no successful outer response publication. -/
def Receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (snap : Snapshot) (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∃ (index : Nat) (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput)
    (bytes : Pqxdh.Bytes) (sealContext : RawCtxSourceSend.SealContext)
    (entry : CtxSuccessfulSeal) (attempt : RawCtxSelectedAuthenticationObserver.Attempt)
    (target : CtxUnclaimedAcceptance.Target),
    Touch.session index message reply ∈ snap.touches ∧
    rootInput setup context.seed context.scalar message = some bytes ∧
    beaconInput setup context.seed context.scalar snap.touches = some bytes ∧
    (index, sealContext) ∈ snap.seals ∧ sealed sealContext = snap.accepted ∧
    PqxdhPhase2LocalMatching.Records entry sealContext ∧
    attempt ∈ observer.attempts ∧
    RawCtxUniversalDecoder.decoder codec.frameRead attempt.raw = some target ∧
    attempt.plaintext = some entry.input.plaintext ∧ entry ∈ attempt.sealsBefore ∧
    target.toLegacy.sameFullTupleAsSuccessfulSeal entry

/-- The literal successful selected finish supplies an accepted receipt or an ordinary forgery. ReadWritable is used only on the concrete accepted matching frame to exclude its inner-writer failure. -/
theorem local_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged) (ghost : Ghost) (hidden : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite ghost hidden before.1)
    (selected : beaconInput setup context.seed context.scalar ghost.touches = hidden)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      Receipt setup codec context ⟨Accepted.ofStaged staged, ghost.touches, ghost.seals⟩ after.1 := by
  rcases program_receipt setup.source codec key rest pending staged before after good supported with
    winning | ⟨raw, componentBytes, target, kernel, entry, application, decoded, delivery, success, attempt, member, same, plaintext⟩
  · exact Or.inl winning
  · obtain ⟨index, message, reply, bytes, sealContext, sequence, touched, hiddenInput, input, bound,
      records, seq, sender, publication⟩ := origins entry member
    obtain ⟨encoded, written⟩ := PqxdhServerAuthFinishReceipt.matched_writable codec.frameWrite codec.frameRead
      writable raw _ staged.opened target delivery entry same sequence sealContext.senderId seq sender
    have fields := PqxdhServerAuthFinishReceipt.matched_fields _ kernel staged success codec.frameRead raw target
      delivery entry same plaintext sealContext records bound
    have acceptedFields : sealed sealContext = Accepted.ofStaged staged := by
      have sameFields := congrArg (fun value : Std.U64 × Pqxdh.Bytes × Pqxdh.Bytes =>
        (⟨value.1, value.2.1, value.2.2⟩ : Accepted)) fields
      exact sameFields.symm
    exact Or.inr ⟨index, message, reply, bytes, sealContext, entry,
      ⟨componentBytes, some staged.opened.plaintext, before.1.seals⟩, target,
      touched, input, selected.trans hiddenInput,
      publication.resolve_left (fun failed => Option.some_ne_none encoded (written.symm.trans failed)),
      acceptedFields, records, attempt, decoded, congrArg some plaintext, member, same⟩

/-- The receipt's unchanged actual component request satisfies the capture predicate. -/
theorem receipt_hit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (snap : Snapshot) (observer : RawCtxSelectedAuthenticationObserver.State)
    (receipt : Receipt setup codec context snap observer) :
    ∃ (entry : CtxSuccessfulSeal) (attempt : RawCtxSelectedAuthenticationObserver.Attempt),
      attempt ∈ observer.attempts ∧ entry ∈ attempt.sealsBefore ∧
      PqxdhServerAuthPublicationGuess.Hit
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead))
        (some (entry.record, attempt.raw)) := by
  obtain ⟨index, message, reply, bytes, sealContext, entry, attempt, target,
    touched, input, beacon, logged, fields, records, found, decoded, plaintext, member, same⟩ := receipt
  exact ⟨entry, attempt, found, member, matching_hit _ _ _ _ decoded same⟩

/-- Extending the actual attempt ledger retains the same accepted receipt and its attempt-time history. -/
theorem receipt_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (snap : Snapshot) (before after : RawCtxSelectedAuthenticationObserver.State)
    (receipt : Receipt setup codec context snap before) (grown : before.attempts ⊆ after.attempts) :
    Receipt setup codec context snap after := by
  obtain ⟨index, message, reply, bytes, sealContext, entry, attempt, target,
    touched, input, beacon, logged, fields, records, found, decoded, plaintext, member, same⟩ := receipt
  exact ⟨index, message, reply, bytes, sealContext, entry, attempt, target,
    touched, input, beacon, logged, fields, records, grown found, decoded, plaintext, member, same⟩

/-- Coverage concerns every actual accepted snapshot, including accepted records for which the old W1/W2 event is false. -/
def Covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (state : PqxdhServerAuthCtxState.Local KemSK)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∀ snap, state.1.1.ghost.acceptance = some snap →
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) observer = true ∨
      PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context state ∨ Receipt setup codec context snap observer

/-- The complete selected callback preserves the exact new acceptance snapshot and all native publication gates before producing the receipt alternative. -/
theorem selected_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (control : pqxdh.BeaconInitSent)
    (localBefore localAfter : PqxdhServerAuthCtxState.Local KemSK) (answer : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite localBefore.1.1.ghost localBefore.1.2.2.hidden before.1)
    (selected : beaconInput setup context.seed context.scalar localBefore.1.1.ghost.touches = localBefore.1.2.2.hidden)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key before)
    (fresh : localBefore.1.1.ghost.acceptance = none)
    (supported : ((answer, localAfter), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.selected setup.source codec rest control pending).run localBefore)).run before)) :
    Covered setup codec context localAfter after.1 := by
  change ((answer, localAfter), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
    (PqxdhServerAuthCtxFinish.complete control localBefore <$>
      PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before) at supported
  rw [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨staged, component⟩, reached, equal⟩ := supported
  have localEqual := congrArg (fun value => value.1.2) equal
  have observerEqual := congrArg Prod.snd equal
  dsimp only at localEqual observerEqual
  subst after
  intro snap captured
  rw [← localEqual] at captured
  cases staged with
  | none =>
      simp only [PqxdhServerAuthCtxFinish.complete, finishOutcome, acceptedOf, Option.map_none,
        ite_self, Ghost.accept, fresh, reduceCtorEq] at captured
  | some staged =>
      cases returned : (PqxdhBeaconPhase2Publication.finish control localBefore.1.1.beacon (some staged)).1 with
      | none =>
          simp only [PqxdhServerAuthCtxFinish.complete, finishOutcome, returned, acceptedOf,
            Option.isSome_none, Bool.false_eq_true, ite_false, Ghost.accept, fresh, reduceCtorEq] at captured
      | some payload =>
          have snapshot : snap = ⟨Accepted.ofStaged staged, localBefore.1.1.ghost.touches, localBefore.1.1.ghost.seals⟩ := by
            simpa only [PqxdhServerAuthCtxFinish.complete, finishOutcome, returned, acceptedOf,
              Option.isSome_some, ite_true, Option.map_some, Ghost.accept, fresh, Option.some.injEq] using captured.symm
          subst snap
          exact (local_receipt setup codec context key rest pending staged localBefore.1.1.ghost
            localBefore.1.2.2.hidden before component origins selected writable good reached).imp_right Or.inr

/-- Rejection before a staged result cannot create an accepted snapshot. -/
theorem rejected_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (control : pqxdh.BeaconInitSent) (state : PqxdhServerAuthCtxState.Local KemSK)
    (fresh : state.1.1.ghost.acceptance = none) (observer : RawCtxSelectedAuthenticationObserver.State) :
    Covered setup codec context (PqxdhServerAuthCtxFinish.complete control state none).2 observer := by
  intro snap captured
  simp only [PqxdhServerAuthCtxFinish.complete, finishOutcome, acceptedOf, Option.map_none,
    ite_self, Ghost.accept, fresh, reduceCtorEq] at captured

/-- Every actual active finish yields a receipt, an ordinary observer win, or an occupied ordinary-root entry. The source prefix, both table routes, actual optional plaintext and final registration gates all remain in the experiment. -/
theorem active_finish_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (unselected : select = true → state.1.2.2.hidden = none)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (phase : state.1.1.beacon.beacon.phase = .initSent control prekey oneTime kem)
    (result : (Option Pqxdh.Bytes × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  have active : InitSent state.1.1 := ⟨control, prekey, oneTime, kem, phase⟩
  have fresh := invariant.history.fresh active
  have clean := invariant.trace.shape.clean active
  intro snap captured
  have runBind {σ α β : Type} (work : StateT σ ProbComp α)
      (next : α → StateT σ ProbComp β) (initial : σ) :
      (work >>= next) initial = work initial >>= fun result => next result.1 result.2 := rfl
  have runCoins {α : Type} (work : ProbComp α)
      (initial : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :=
    PqxdhServerAuthCtxAcceptanceCover.observed_coins setup.source key codec.frameRead work initial
  simp only [StateT.run] at runCoins
  simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_bind,
    runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, supported⟩ := supported
  cases prepared with
  | none =>
    simp only [simulateQ_pure] at supported
    subst supported
    exact rejected_cover setup codec context control state fresh _ snap captured
  | some pending =>
    simp only [simulateQ_bind, runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨derived, reached, supported⟩ := supported
    cases reply : derived.1 with
    | rejected =>
      simp only [reply, simulateQ_pure] at supported
      subst supported
      exact rejected_cover setup codec context control
        (PqxdhServerAuthCtxFinish.touched state
          (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) derived.2)
        fresh before.1 snap captured
    | root root =>
      simp only [reply] at supported
      obtain ⟨bytes, input, occupied⟩ := PqxdhServerAuthCtxChronology.table_root setup context select
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
        state.1.2.2 derived.2 root (by rw [← reply]; exact reached)
      apply Or.inr ∘ Or.inl
      apply PqxdhServerAuthCtxAcceptanceCover.known_ordinary setup codec context key control pending root _ result.1.2 _ before result.2 result.1.1 supported
      refine ⟨bytes, ?_, occupied⟩
      change beaconInput setup context.seed context.scalar
        (state.1.1.ghost.touches ++ [Touch.beacon _]) = some bytes
      rw [beaconInput, firstBeacon_after _ [] _ clean, Option.bind_some]
      exact input
    | hidden =>
      simp only [reply] at supported
      exact selected_cover setup codec context key rest pending control _ result.1.2 result.1.1 before result.2
        (PqxdhServerAuthCtxAcceptanceCover.derive_origins setup codec context select state before.1
          invariant.origins unselected _ derived reached)
        (PqxdhServerAuthCtxOrigin.touched_input setup context select state
          (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
          derived.2 clean (by rw [← reply]; exact reached))
        writable invariant.good fresh supported snap captured

/-- The complete finish capability preserves acceptance coverage through all actual source phases, including rejection without a new Beacon attempt. -/
theorem finish_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (unselected : select = true → state.1.2.2.hidden = none)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Pqxdh.Bytes × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    exact active_finish_cover setup codec context key rest Q j select raw state before invariant
      unselected writable control prekey oneTime kem phase result supported
  | _ =>
    simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_pure] at supported
    subst supported
    exact covered

/-- A complete nonfinish compiled operation preserves the same acceptance coverage. Earlier wins persist, while an ordinary input remains occupied through the actual source table continuation. -/
theorem quiet_handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (notFinish : ∀ raw, query ≠ .inr (.finish raw))
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  obtain ⟨answer, _, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support setup codec checks context
    rest key Q j query state before ready result supported
  have accepted := PqxdhServerAuthCtxAcceptanceCover.handler_acceptance setup codec checks context
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) Q j query notFinish
    (PqxdhServerAuthCtxState.project (state, before.2)) _ reached
  have grown := PqxdhServerAuthCtxAcceptanceHistory.handler_grows setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
    (PqxdhServerAuthCtxState.project (state, before.2)) _ reached
  have retained := (PqxdhServerAuthCtxChronology.handler_history setup codec checks context
    (PqxdhServerAuthCtxMaterial.output key rest) Q j query
    (PqxdhServerAuthCtxState.project (state, before.2)) invariant.clean _ reached).1
  intro snap captured
  change result.1.2.1.1.ghost.acceptance = state.1.1.ghost.acceptance at accepted
  rw [accepted] at captured
  rcases covered snap captured with winning | ⟨bytes, input, present⟩ | receipt
  · exact Or.inl (PqxdhFirstBeaconRecordCanonical.observed_won _ _ _ _ before winning result supported)
  · exact Or.inr (Or.inl ⟨bytes, beaconInput_prefix setup context.seed context.scalar _ _ bytes input grown.touches,
      retained bytes present⟩)
  · exact Or.inr (Or.inr (receipt_grows setup codec context snap before.1 result.2.1 receipt
      (RawCtxSelectedAcceptedRecord.monitor_attempts _ _ _
        (PqxdhFirstBeaconRecordCanonical.observed_monitor _ _ _ _ before result supported))))

/-- Actual complete finish dispatch and designation settlement preserve the proved acceptance alternatives without observing an invented plaintext or assuming the finish succeeds. -/
theorem finish_handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Option Pqxdh.Bytes) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j (.inr (.finish raw))).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxHandler.settle Q j (.inr (.finish raw)) state <$>
        ((PqxdhServerAuthCtxHandler.route setup codec checks context rest
          (!state.2 && hiddenDesignated Q j (.inr (.finish raw)) state.1)
          (.inr (.finish raw))).run.run state))).run before) at supported
  simp only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp, StateT.run_map,
    Functor.map_map, simulateQ_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := finish_cover setup codec context key rest Q j
    (!state.2 && hiddenDesignated Q j (.inr (.finish raw)) state.1) raw state before invariant covered
    (by
      intro selected
      cases flag : state.2
      · exact invariant.trace.unselected flag
      · simp only [flag, Bool.not_true, Bool.false_and, Bool.false_eq_true] at selected)
    writable inner reached
  unfold PqxdhServerAuthCtxHandler.settle keepHiddenBad
  split <;> exact retained

/-- Every original compiled API operation preserves acceptance coverage on the same full observed execution. -/
theorem handler_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (covered : Covered setup codec context state before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Covered setup codec context result.1.2 result.2.1 := by
  classical
  by_cases finish : ∃ raw, query = .inr (.finish raw)
  · obtain ⟨raw, rfl⟩ := finish
    exact finish_handler_cover setup codec checks context key rest Q j raw state before
      invariant covered writable result supported
  · exact quiet_handler_cover setup codec checks context key rest Q j query
      (fun raw equal => finish ⟨raw, equal⟩) state before ready invariant covered result supported

/-- The actual post-callback checkpoint preserves acceptance coverage, including the complete callback work before an outer stop. -/
theorem stopped_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxState.Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state.1, before.2))
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state.1 before)
    (covered : Covered setup codec context state.1 before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (ServerAuthSpec.Range query) × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before)) :
    Covered setup codec context result.1.2.1 result.2.1 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have retained := handler_cover setup codec checks context key rest Q j query state.1 before ready invariant
    covered writable inner reached
  simpa only [observe_state] using retained

/-- The ordinary interpreted callback supplies the next acceptance alternative from the actual joint source invariant and reservation. -/
theorem interpreted_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (covered : Covered setup codec context state.1.1 state.2.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxObserverHistory.interpreted
      setup codec checks context rest key Q j query).run.run state)) :
    Covered setup codec context result.2.1.1 result.2.2.1 := by
  simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
    PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact stopped_cover setup codec checks context key rest Q j query state.1 state.2
    (PqxdhServerAuthCtxReserve.valid_ready query (state.1, state.2.2) invariant.1)
    invariant.2 covered writable inner reached

/-- The complete adaptive optional continuation preserves acceptance coverage using the actual source/observer invariant after every continuing reply. -/
theorem program_cover {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (client : OracleComp ServerAuthSpec α)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (invariant : PqxdhServerAuthCtxObserverHistory.Invariant setup codec context key Q j state)
    (covered : Covered setup codec context state.1.1 state.2.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Option α × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j) client).run.run state))
    (answer : α) (continues : result.1 = some answer) :
    Covered setup codec context result.2.1.1 result.2.2.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact covered
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    cases reply : middle.1 with
    | none =>
      simp only [reply, Option.elim_none, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases continues
    | some value =>
      simp only [reply, Option.elim_some] at supported
      exact ih value middle.2
        (PqxdhServerAuthCtxObserverHistory.interpreted_invariant setup codec checks context rest key Q j
          query state invariant middle reached value reply)
        (interpreted_cover setup codec checks context rest key Q j query state invariant covered writable middle reached)
        supported

/-- The actual initial experiment has no acceptance to cover. -/
theorem initial_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) :
    Covered setup codec context (PqxdhServerAuthCtxObserverHistory.initial setup context).1.1
      (PqxdhServerAuthCtxObserverHistory.initial setup context).2.1 := by
  intro snap captured
  cases captured

/-- The original adversary's literal complete observed execution derives its acceptance alternative with no supplied trace, origin, selected-freshness or success premise. -/
theorem run_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (adversary : Adversary)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
        (adversary (contextInput setup false context))).run.run
        (PqxdhServerAuthCtxObserverHistory.initial setup context).1)).run
      (PqxdhServerAuthCtxObserverHistory.initial setup context).2))
    (continues : result.1.1 = some ()) :
    Covered setup codec context result.1.2.1 result.2.1 := by
  have evaluated : (result.1.1, (result.1.2, result.2)) ∈ support
      ((PqxdhSelectedStateInterpreter.evaluate
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run
        (PqxdhServerAuthCtxObserverHistory.initial setup context)) := by
    change (result.1.1, (result.1.2, result.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [PqxdhServerAuthCtxObserverHistory.program_interpreted] at evaluated
  exact program_cover setup codec checks context rest key Q j _ (PqxdhServerAuthCtxObserverHistory.initial setup context)
    (PqxdhServerAuthCtxObserverHistory.initial_invariant setup codec context key Q j)
    (initial_cover setup codec context) writable _ evaluated () continues


/-- Every accepted normal full execution at its actual owner coordinate yields a partner-indexed selected receipt or the ordinary authentication observer event. Source designation and cache omission discharge the ordinary-root alternative; the old W1/W2 predicate is not required. -/
theorem execution_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (continues : result.1.1 = some ())
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      Receipt setup codec context snap result.2.1 := by
  have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j
    adversary result supported continues
  have covered := run_cover setup codec checks context rest key Q j adversary writable result supported continues
  have source := PqxdhServerAuthCtxObserverEvent.execution_source setup codec checks adversary context rest key Q j
    result supported continues
  obtain ⟨bytes, selected, input⟩ := accepted_input setup codec checks adversary context
    (PqxdhServerAuthCtxMaterial.output key rest) Q j _ source snap accepted owned notBad
  rcases covered snap accepted with won | ⟨other, otherInput, occupied⟩ | receipt
  · exact Or.inl won
  · have equal : other = bytes := Option.some.inj (otherInput.symm.trans input)
    subst other
    exact (occupied (invariant.2.clean bytes selected)).elim
  · exact Or.inr receipt

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.accepted_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.accepted_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.program_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.program_receipt
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.matching_hit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.matching_hit
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.local_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.local_receipt
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.receipt_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.receipt_hit
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.receipt_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.receipt_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.selected_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.selected_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.rejected_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.rejected_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.active_finish_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.active_finish_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.finish_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.finish_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.quiet_handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.quiet_handler_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.finish_handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.finish_handler_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.handler_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.handler_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.stopped_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.stopped_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.interpreted_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.interpreted_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.program_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.program_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.initial_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.initial_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.run_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.run_cover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.execution_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance.execution_receipt
