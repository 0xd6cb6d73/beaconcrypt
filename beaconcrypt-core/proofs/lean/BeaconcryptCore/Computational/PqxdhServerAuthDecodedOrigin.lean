import BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin

/-! Exact decoded-record provenance for the actual selected registration callback. This does not assert equality of serialization bytes or successful outer response publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin
open PqxdhServerAuthExperiment PqxdhServerAuthCtxCalls
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {Reader Response : Type}

/-- The decoded frame of a matching local target has the exact issued protected payload and the actual accepted sequence and sender. No decoder injectivity, canonical encoding or writer-totality premise is used. -/
theorem matched_frame (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (opened : RawCtxWholeOwner.Decrypted)
    (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget read bytes candidate opened target)
    (entry : CtxRomAuth.CtxSuccessfulSeal)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    read bytes = some ⟨opened.sequence, opened.keyId, entry.record.encode⟩ := by
  obtain ⟨frame, nonce, slices, parsed, width, _, decoded, _, sender, sequence, rfl⟩ := delivery
  have payload : frame.payload = entry.record.encode :=
    (RawCtxSelectedPlaintextOrigins.record_payload frame slices parsed).symm.trans same.2.2
  simpa only [sequence, sender, ← payload] using decoded

/-- The complete actual selected finish returns either the existing ordinary forgery event or an earlier component receipt for its exact decoded frame and returned plaintext. The original target, source acceptance gates and chronological membership are retained. -/
theorem program_or_origin (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (key : RootOutput) (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key)
      (PqxdhServerAuthFinishMaterial.program source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      let prepared := PqxdhPhase2DhRootConsumer.cleared pending
      let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
      ∃ (bytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target) (kernel : ConcreteRatchetKernel)
        (entry : CtxRomAuth.CtxSuccessfulSeal),
        codec.application prepared.response = some bytes ∧
        PqxdhPhase2LocalMatching.LocalTarget codec.frameRead bytes candidate staged.opened target ∧
        PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged ∧
        entry ∈ before.1.seals ∧ target.toLegacy.sameFullTupleAsSuccessfulSeal entry ∧
        staged.opened.plaintext = entry.input.plaintext ∧
        codec.frameRead bytes = some ⟨staged.opened.sequence, staged.opened.keyId, entry.record.encode⟩ := by
  refine (PqxdhServerAuthFinishReceipt.program_or_match source codec key rest pending staged before after good supported).imp_right ?_
  rintro ⟨bytes, target, kernel, entry, application, delivery, success, member, same, plaintext⟩
  exact ⟨bytes, target, kernel, entry, application, delivery, success, member, same, plaintext,
    matched_frame codec.frameRead bytes _ staged.opened target delivery entry same⟩

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The actual ordinary receipt retains its chronological source session, exact decoded frame and returned plaintext. Only an accepted decoded match rules out inner writer failure; successful outer response publication is a separate event. -/
theorem source_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : PqxdhServerAuthEntryFactor.Context KemSK) (key : RootOutput) (rest : Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged) (ghost : Ghost) (hidden : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite ghost hidden before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      ∃ (index : Nat) (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput)
        (input : Pqxdh.Bytes) (sealContext : RawCtxSourceSend.SealContext)
        (entry : CtxRomAuth.CtxSuccessfulSeal) (raw : Pqxdh.Bytes),
        Touch.session index message reply ∈ ghost.touches ∧ hidden = some input ∧
        rootInput setup context.seed context.scalar message = some input ∧
        entry ∈ before.1.seals ∧ (index, sealContext) ∈ ghost.seals ∧
        PqxdhPhase2LocalMatching.Records entry sealContext ∧
        codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some raw ∧
        codec.frameRead raw = some ⟨staged.opened.sequence, staged.opened.keyId, entry.record.encode⟩ ∧
        staged.opened.plaintext = entry.input.plaintext ∧
        PqxdhPhase2LocalMatching.acceptedFields staged = PqxdhPhase2LocalMatching.sealedFields sealContext := by
  refine (program_or_origin setup.source codec key rest pending staged before after good supported).imp_right ?_
  rintro ⟨raw, target, kernel, entry, application, delivery, success, member, same, plaintext, decoded⟩
  obtain ⟨index, message, reply, input, sealContext, sequence, touched, selected, derived, bound,
    records, seq, sender, publication⟩ := origins entry member
  obtain ⟨encoded, written⟩ := PqxdhServerAuthFinishReceipt.matched_writable codec.frameWrite codec.frameRead
    writable raw _ staged.opened target delivery entry same sequence sealContext.senderId seq sender
  exact ⟨index, message, reply, input, sealContext, entry, raw, touched, selected, derived, member,
    publication.resolve_left (fun failed => Option.some_ne_none encoded (written.symm.trans failed)),
    records, application, decoded, plaintext,
    PqxdhServerAuthFinishReceipt.matched_fields _ kernel staged success codec.frameRead raw target
      delivery entry same plaintext sealContext records bound⟩

end BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.matched_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.matched_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.program_or_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.program_or_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin.source_origin
