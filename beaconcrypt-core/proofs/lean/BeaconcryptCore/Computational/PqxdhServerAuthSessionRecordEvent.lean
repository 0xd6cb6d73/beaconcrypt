import BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin

/-! Keep the same-owner authenticated seal fields beside decoded-record publication. The observer takes no separate root or secret-key argument. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The exact accepted key ID, payload and associated data have an earlier seal at the specified source coordinate. The transient acceptance annotation contains no persistence operation. -/
def SealedAt (index : Nat) (ghost : Ghost) : Prop :=
  ∃ snap context, ghost.acceptance = some snap ∧
    (index, context) ∈ snap.seals ∧ sealed context = snap.accepted

/-- Matching authenticated fields and actual earlier decoded-record publication are both required at the same source coordinate. -/
def Published (codec : Codec Reader Response) (index : Nat) (ghost : Ghost)
    (journal : QueryLog ServerAuthSpec) : Prop :=
  SealedAt index ghost ∧ PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index journal

/-- The observer sees only the root-erased analysis fields and original public journal. -/
noncomputable def observer (codec : Codec Reader Response) (index : Nat) : PqxdhServerAuthObservedEntry.Observer :=
  fun ghost journal => @decide (¬ Published codec index ghost journal) (Classical.propDecidable _)

/-- Erasing all derived root replies changes none of the matching authenticated seal fields. -/
theorem sealed_erase (index : Nat) (ghost : Ghost) : SealedAt index (eraseGhost ghost) ↔ SealedAt index ghost := by
  cases found : ghost.acceptance <;> simp [SealedAt, eraseGhost, found, eraseSnap]

/-- The full publication observation remains root-independent, including its same-owner seal condition. -/
theorem published_erase (codec : Codec Reader Response) (index : Nat) (ghost : Ghost)
    (journal : QueryLog ServerAuthSpec) : Published codec index (eraseGhost ghost) journal ↔ Published codec index ghost journal := by
  simp only [Published, sealed_erase]

/-- The selected-entry decision tests exactly failure of the combined root-erased publication condition. -/
theorem observer_true (codec : Codec Reader Response) (index : Nat) (ghost : Ghost)
    (journal : QueryLog ServerAuthSpec) : observer codec index (eraseGhost ghost) journal = true ↔
      ¬ Published codec index ghost journal := by
  simp only [observer, decide_eq_true_eq, published_erase]

/-- The existing same-owner component receipt retains the accepted associated data, payload and key ID, rather than only the decoded frame. -/
theorem receipt_sealed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK)
    (index : Nat) (ghost : Ghost) (snap : Snapshot) (accepted : ghost.acceptance = some snap)
    (recordState : RawCtxSelectedAuthenticationObserver.State)
    (receipt : PqxdhServerAuthPublicationOccurrence.ReceiptAt setup codec context index snap recordState) :
    SealedAt index ghost := by
  obtain ⟨message, reply, bytes, sealContext, entry, attempt, target, _, _, _, member, same, _⟩ := receipt
  exact ⟨snap, sealContext, accepted, member, same⟩

/-- Failure of the combined same-owner seal and public-record condition is charged to the existing ordinary authentication or unpublished matched-attempt event on this same complete execution. -/
theorem accepted_clean (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : CtxRomAuth.CtxKey) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
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
    (notPublished : ¬ Published codec j.val after.1.1.1.ghost journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) finalState.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) finalState.1 := by
  have original := PqxdhServerAuthPublicationJournalClean.normal_source setup codec checks context rest Q j _ _ true _ key
    (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
    ((), journal) after finalState supported
  rcases PqxdhServerAuthPublicationOccurrence.journal_receipt setup codec checks adversary context rest key Q j
    writable ((some ((), journal), after), (finalState.1.observer, finalState.2)) original journal rfl
    snap accepted owned notBad unique with won | ⟨_, receipt⟩
  · exact Or.inl won
  · exact PqxdhServerAuthRecordPublicationJoin.accepted_clean setup codec checks adversary context rest key Q j
      writable responseBack frameBack journal after finalState supported snap accepted owned notBad unique
      (fun published => notPublished ⟨receipt_sealed setup codec context j.val _ snap accepted _ receipt, published⟩)

end BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.sealed_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.sealed_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.published_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.published_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.observer_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.observer_true
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.receipt_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.receipt_sealed
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.accepted_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSessionRecordEvent.accepted_clean
