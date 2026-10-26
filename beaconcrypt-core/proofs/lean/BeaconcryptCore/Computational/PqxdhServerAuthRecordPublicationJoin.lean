import BeaconcryptCore.Computational.PqxdhServerAuthFinishJournalAcceptance
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationBuildJournal

/-! Join the actual accepted public request to the exact earlier Server response in the same complete execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhServerAuthRecordPublicationEvent
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The actual builder's two successful writer calls return the precise received frame under the existing one-way abstract message readback contracts. -/
theorem written_frame (codec : Codec Reader Response)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (server : ServerState)
    (response : PqxdhServerRegistrationPublication.Response) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (built : PqxdhServerAuthPublicationBuiltRecord.At codec pending data server response entry)
    (record : RawCtxReceive.DecodedFrame) (same : PqxdhServerAuthFinishFrameReceipt.Matches record entry) :
    frame codec response.serialized = some record := by
  obtain ⟨key, candidate, binding, sealed, encrypted, nonce, width, _, _, _, _, outer, _, _, input, inner⟩ := built
  have sequence : record.sequence = sealed.sequence := UScalar.eq_of_val_eq
    (by simpa only [input, RawCtxSelectedMessageSealing.selectedInput] using same.1)
  have sender : record.sender = sealed.context.senderId := UScalar.eq_of_val_eq
    (by simpa only [input, RawCtxSelectedMessageSealing.selectedInput] using same.2.1)
  have payload := same.2.2
  cases record
  simp only at sequence sender payload
  simpa only [sequence, sender, payload] using frame_written codec responseBack frameBack
    (PqxdhServerRegistrationPublication.responseFields candidate encrypted) response.serialized
    ⟨sealed.sequence, sealed.context.senderId, entry.record.encode⟩ outer inner

/-- A successful earlier outer publication at the actual accepted owner publishes the exact received decoded record, unless the original authentication observer wins. Both receipts come from the same complete execution. -/
theorem accepted_published (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
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
    (notBad : result.1.2.1.1.2.2.bad = false)
    (unique : ¬ CollB setup context.seed context.scalar result.1.2.1.1.1.ghost)
    (published : PqxdhServerAuthPublicationOccurrence.Published j.val journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      RecordPublished codec j.val journal := by
  rcases PqxdhServerAuthFinishJournalAcceptance.accepted_receipt setup codec checks adversary context rest key Q j
    result supported journal normal snap accepted owned notBad with won | ⟨raw, selected, entry, member, record, decoded, same⟩
  · exact Or.inl won
  · obtain ⟨payload, response, earlier⟩ := published
    rcases PqxdhServerAuthPublicationBuildJournal.accepted_records setup codec checks adversary context rest key Q j
      writable result supported journal normal snap accepted owned notBad unique payload response
      (List.takeWhile_subset _ earlier) with won | ⟨_, token, server, records⟩
    · exact Or.inl won
    · exact Or.inr ⟨payload, response, raw, record, earlier, selected, decoded,
        written_frame codec responseBack frameBack token.pending payload server response entry
          (records entry member) record same⟩

/-- The stronger missing-record event uses the same ordinary-authentication and unpublished-matched-attempt alternatives on the same marked execution. It introduces no second authentication charge. -/
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
    (notPublished : ¬ RecordPublished codec j.val journal) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) finalState.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) finalState.1 := by
  classical
  by_cases published : PqxdhServerAuthPublicationOccurrence.Published j.val journal
  · have original := PqxdhServerAuthPublicationJournalClean.normal_source setup codec checks context rest Q j _ _ true _ key
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)
      ((), journal) after finalState supported
    rcases accepted_published setup codec checks adversary context rest key Q j writable responseBack frameBack
      ((some ((), journal), after), (finalState.1.observer, finalState.2)) original journal rfl
      snap accepted owned notBad unique published with won | record
    · exact Or.inl won
    · exact (notPublished record).elim
  · exact PqxdhServerAuthPublicationJournalClean.accepted_clean setup codec checks adversary context rest key Q j
      writable journal after finalState supported snap accepted owned notBad unique published

end BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.written_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.written_frame
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.accepted_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.accepted_published
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.accepted_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin.accepted_clean
