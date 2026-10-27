import BeaconcryptCore.Computational.PqxdhServerAuthPublicationAcceptance
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily

/-! Literal source owner and public build occurrence for the accepted-record receipt. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor CtxRomAuth
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Atomic source acceptance and the existing collision exclusion identify every actual partner with the selected owner coordinate. No equality of encoded bytes identifies a session. -/
theorem partner_owner (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (game : GameState KemSK)
    (history : PqxdhServerAuthCtxAcceptanceHistory.History game)
    (snap : Snapshot) (accepted : game.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q game.ghost = some j)
    (unique : ¬ CollB setup context.seed context.scalar game.ghost)
    (index : Nat) (partner : Partner setup context.seed context.scalar snap index) :
    index = j.val ∧ j.val < Q := by
  obtain ⟨before, beaconTouch, snapEq, clean⟩ := history.atomic snap accepted
  have isPrefix := (history.frozen snap accepted).1
  have below : j.val < Q := by
    by_contra notBelow
    have last : j = Fin.last Q := Fin.ext (by simp; omega)
    exact owner_beacon_ghost setup context.seed context.scalar Q game.ghost snap isPrefix before beaconTouch
      snapEq clean (by simpa only [last] using owned) index partner
  have owner := owner_session_ghost setup context.seed context.scalar Q game.ghost snap isPrefix before
    beaconTouch snapEq clean j owned below
  refine ⟨?_, below⟩
  by_contra distinct
  obtain ⟨message, reply, bytes, touched, rooted, beacon⟩ := partner
  obtain ⟨ownerMessage, ownerReply, ownerBytes, ownerTouched, ownerRooted, ownerBeacon⟩ := owner
  have same : ownerBytes = bytes := Option.some.inj (ownerBeacon.symm.trans beacon)
  subst ownerBytes
  exact unique ⟨index, j.val, message, ownerMessage, reply, ownerReply, bytes, distinct,
    isPrefix.subset touched, isPrefix.subset ownerTouched,
    beaconInput_prefix setup context.seed context.scalar _ _ bytes beacon isPrefix, rooted, ownerRooted⟩

/-- The actual component receipt with its literal Server owner coordinate retained. -/
def ReceiptAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (index : Nat) (snap : Snapshot) (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∃ (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput)
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

/-- Source chronology gives the receipt's exact owner without strengthening its full-tuple or optional-plaintext evidence. -/
theorem receipt_at (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (game : GameState KemSK)
    (history : PqxdhServerAuthCtxAcceptanceHistory.History game)
    (snap : Snapshot) (accepted : game.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q game.ghost = some j)
    (unique : ¬ CollB setup context.seed context.scalar game.ghost)
    (observer : RawCtxSelectedAuthenticationObserver.State)
    (receipt : PqxdhServerAuthPublicationAcceptance.Receipt setup codec context snap observer) :
    j.val < Q ∧ ReceiptAt setup codec context j.val snap observer := by
  obtain ⟨index, message, reply, bytes, sealContext, entry, attempt, target, touched, rooted, beacon, rest⟩ := receipt
  have owner := partner_owner setup context Q j game history snap accepted owned unique index
    ⟨message, reply, bytes, touched, rooted, beacon⟩
  have equal := owner.1
  subst index
  exact ⟨owner.2, message, reply, bytes, sealContext, entry, attempt, target, touched, rooted, beacon, rest⟩

/-- The complete supported compiler run identifies a matching receipt with its actual selected owner, or exposes the unchanged ordinary authentication observer event. -/
theorem execution_receipt_at (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
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
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      j.val < Q ∧ ReceiptAt setup codec context j.val snap result.2.1 := by
  rcases PqxdhServerAuthPublicationAcceptance.execution_receipt setup codec checks adversary context rest key Q j
    writable result supported continues snap accepted owned notBad with won | receipt
  · exact Or.inl won
  · have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j
      adversary result supported continues
    exact Or.inr (receipt_at setup codec context Q j _ invariant.2.history snap accepted owned unique _ receipt)

/-- Every actual marked session is the receipt's owner under the original final collision exclusion. This includes marks retained through later public API calls. -/
theorem marked_owner (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (trace : PqxdhServerAuthCtxStop.TraceInvariant setup context Q j state)
    (history : PqxdhServerAuthCtxAcceptanceHistory.History state.1.1)
    (snap : Snapshot) (accepted : state.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q state.1.1.ghost = some j)
    (unique : ¬ CollB setup context.seed context.scalar state.1.1.ghost)
    (partnerIndex : Nat) (partner : Partner setup context.seed context.scalar snap partnerIndex)
    (index : Nat) (marked : state.1.2.1 index = true) : index = j.val := by
  have owner := partner_owner setup context Q j state.1.1 history snap accepted owned unique partnerIndex partner
  obtain ⟨message, reply, bytes, touched, selected, rooted⟩ := trace.marked index marked
  have beacon := PqxdhServerAuthCtxStop.selected_input setup context Q j state.1.1.ghost trace.shape.once
    owned bytes (trace.selected bytes selected)
  obtain ⟨partnerMessage, partnerReply, partnerBytes, partnerTouched, partnerRooted, partnerBeacon⟩ := partner
  have partnerFinal := beaconInput_prefix setup context.seed context.scalar _ _ partnerBytes partnerBeacon
    (history.frozen snap accepted).1
  have same : partnerBytes = bytes := Option.some.inj (partnerFinal.symm.trans beacon)
  subst partnerBytes
  have sameIndex : index = partnerIndex := by
    by_contra distinct
    exact unique ⟨index, partnerIndex, message, partnerMessage, reply, partnerReply, bytes, distinct, touched,
      (history.frozen snap accepted).1.subset partnerTouched, beacon, rooted, partnerRooted⟩
  exact sameIndex.trans owner.1

/-- A successful literal finish reply terminates the public history relevant to this acceptance. No decoder or writer readback is used. -/
def finishReturned : ((query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) → Bool
  | ⟨.inr (.finish _), reply⟩ => reply.isSome
  | _ => false

/-- Exact public calls preceding the first successful finish. Rejected calls remain in their original positions. -/
def beforeAcceptance (journal : QueryLog ServerAuthSpec) : QueryLog ServerAuthSpec :=
  journal.takeWhile fun event => !finishReturned event

/-- Publication is a literal successful build call at the supplied source session coordinate. Equal bytes or accepted fields in another session are irrelevant. -/
def Published (index : Nat) (journal : QueryLog ServerAuthSpec) : Prop :=
  ∃ payload reply, (⟨.inr (.build index payload), some reply⟩ :
    (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ beforeAcceptance journal

/-- Root-erased/public observer for a missing publication at a fixed owner coordinate. Acceptance and actual ownership are supplied by the already proved owner-family gate. -/
noncomputable def observer (index : Nat) : PqxdhServerAuthObservedEntry.Observer := fun _ journal =>
  @decide (¬ Published index journal) (Classical.propDecidable _)

/-- The concrete predicate exposes only the chronological public journal and the supplied coordinate. -/
theorem observer_true (index : Nat) (ghost : Ghost) (journal : QueryLog ServerAuthSpec) :
    observer index ghost journal = true ↔ ¬ Published index journal := by
  simp only [observer, decide_eq_true_eq]

/-- The prefix predicate really stops before a successful finish, preserving every preceding callback and omitting every later callback. -/
theorem before_finish (before after : QueryLog ServerAuthSpec) (raw payload : Pqxdh.Bytes)
    (prior : ∀ event ∈ before, finishReturned event = false) :
    beforeAcceptance (before ++ ⟨.inr (.finish raw), some payload⟩ :: after) = before := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, beforeAcceptance, List.takeWhile_cons, prior head (List.mem_cons_self),
        Bool.not_false]
      exact congrArg (List.cons head) (ih fun event member => prior event (List.mem_cons_of_mem _ member))

/-- Journal the exact public replies while running the unchanged optional component compiler. The component interpreter still owns its full private state. -/
noncomputable def execution (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :=
  ((simulateQ (PqxdhServerAuthCtxReserve.stopped
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
    (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))).run).run
      (PqxdhServerAuthCtxReserve.initial setup context).1

/-- Removing just the public journal recovers the identical optional compiler program and complete terminal local state. -/
theorem execution_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    (fun result => (result.1.map Prod.fst, result.2)) <$>
      execution setup codec checks adversary Q j context rest =
      PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest := by
  have same := congrArg (fun work : OracleComp ServerAuthSpec Unit =>
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run).run
        (PqxdhServerAuthCtxReserve.initial setup context).1)
    (PqxdhServerAuthApiJournal.erase (adversary (contextInput setup false context)))
  simpa only [execution, PqxdhServerAuthCtxExperiment.execution, simulateQ_map, OptionT.run_map,
    StateT.run_map, Functor.map_map] using same

/-- Every component query certificate is unchanged by the chronological public journal, for all possible optional replies. -/
theorem execution_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (cap : Nat) :
    (execution setup codec checks adversary Q j context rest).IsQueryBoundP predicate cap ↔
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest).IsQueryBoundP predicate cap :=
  isQueryBoundP_iff_of_map_eq (p := predicate) (execution_erase setup codec checks adversary Q j context rest)

/-- The new joint public journal does not change the ordinary observer's real record/attempt history or any underlying component state. -/
theorem observed_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (state : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => ((result.1.1.map Prod.fst, result.1.2), result.2)) <$>
      (simulateQ (RawCtxSelectedAuthenticationObserver.observed true
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (execution setup codec checks adversary Q j context rest)).run state =
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run state := by
  have same := congrArg (fun work =>
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key) work).run state)
    (execution_erase setup codec checks adversary Q j context rest)
  simpa only [simulateQ_map, StateT.run_map] using same

/-- The full public journal and matched component receipt come from the same execution. Only the extra journal is projected to invoke the original accepted-receipt theorem. -/
theorem journal_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option (Unit × QueryLog ServerAuthSpec) × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (journal : QueryLog ServerAuthSpec) (continues : result.1.1 = some ((), journal))
    (snap : Snapshot) (accepted : result.1.2.1.1.1.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q result.1.2.1.1.1.ghost = some j)
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      j.val < Q ∧ ReceiptAt setup codec context j.val snap result.2.1 := by
  have erased : ((result.1.1.map Prod.fst, result.1.2), result.2) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
    rw [← observed_erase setup codec checks adversary Q j context rest key]
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  exact execution_receipt_at setup codec checks adversary context rest key Q j writable _ erased
    (by simp only [continues, Option.map_some]) snap accepted owned notBad unique

/-- The original selected-input collision exclusion rejects two actual marks without requiring the old W1/W2 event. -/
theorem no_double_mark (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (trace : PqxdhServerAuthCtxStop.TraceInvariant setup context Q j state)
    (owned : entryOwner setup context.seed context.scalar Q state.1.1.ghost = some j)
    (unique : ¬ CollB setup context.seed context.scalar state.1.1.ghost) :
    ¬ PqxdhServerAuthCtxStop.DoubleMarked state.1.2.1 := by
  rintro ⟨first, second, different, one, two⟩
  obtain ⟨firstMessage, firstReply, bytes, firstTouch, hidden, firstInput⟩ := trace.marked first one
  obtain ⟨secondMessage, secondReply, other, secondTouch, otherHidden, secondInput⟩ := trace.marked second two
  have same : other = bytes := Option.some.inj (otherHidden.symm.trans hidden)
  subst other
  have beacon := PqxdhServerAuthCtxStop.selected_input setup context Q j state.1.1.ghost trace.shape.once
    owned bytes (trace.selected bytes hidden)
  exact unique ⟨first, second, firstMessage, secondMessage, firstReply, secondReply, bytes,
    different, firstTouch, secondTouch, beacon, firstInput, secondInput⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.partner_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.partner_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.receipt_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.receipt_at

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_receipt_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_receipt_at

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.marked_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.marked_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.observer_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.observer_true

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.before_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.before_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.execution_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.observed_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.observed_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.journal_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.journal_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.no_double_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOccurrence.no_double_mark
