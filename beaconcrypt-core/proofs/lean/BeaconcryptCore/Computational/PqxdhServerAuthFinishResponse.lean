import BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent
import BeaconcryptCore.Computational.PqxdhServerAuthDecodedOrigin

/-! The accepted preparation retains the response read from the original public finish bytes. This is a source callback receipt, with no writer preimage or decoder injectivity assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse
open PqxdhJointIdentity PqxdhJointGapDh PqxdhPhase2GapDhSource PqxdhServerAuthExperiment
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The response retained through every ordered optional callback is the response of the first actual raw decode. All intervening callback effects and rejection paths remain in the supported computation. -/
theorem collect_response {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A : Type} (read : Pqxdh.Bytes → Option Response)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (decode : ∀ bytes initial response final,
      (some response, final) ∈ support ((aux (.decode bytes)).run initial) → read bytes = some response)
    (visit : PqxdhBeaconPhase2Preparation.Word32 → StateT A ProbComp Unit)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (initial final : A) (input : Inputs Response)
    (reached : (some input, final) ∈ support
      ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial)) :
    read raw = some input.response := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at reached
  repeat' first
    | (simp only [Option.elim_none, Option.elim_some, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        prefixImpl, selectedReply, bind_assoc, pure_bind, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq, Option.some_ne_none, false_and] at reached)
    | (obtain ⟨⟨reply, state⟩, step, reached⟩ := reached; cases reply)
    | (split at reached)
  rcases reached with ⟨rfl, rfl⟩
  solve_by_elim [decode]

/-- The literal source preparation, including admission after all ordered callbacks, retains the response decoded from the original public raw bytes. -/
theorem prefix_response (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (supported : some pending ∈ support ((beaconPrefix setup codec seed control identity oneTime kem raw).run' ())) :
    codec.read2 raw = some pending.collected.response := by
  simp only [beaconPrefix, PqxdhPhase2DhMetadata.prepare, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, mem_support_bind_iff,
    mem_support_pure_iff] at supported
  obtain ⟨⟨collected, final⟩, reached, same⟩ := supported
  cases collected with
  | none => simp only [Option.bind_none, reduceCtorEq] at same
  | some value =>
    cases admitted : PqxdhPhase2DhMetadata.admitted control value with
    | none => simp only [Option.bind_some, admitted, Option.map_none, reduceCtorEq] at same
    | some metadata =>
      simp only [Option.bind_some, admitted, Option.map_some, Option.some.injEq] at same
      rw [same]
      refine collect_response setup.beaconDomain codec.read2 (beaconAuxUnit setup codec seed) ?_
        (fun _ => pure ()) identity oneTime kem raw () final value reached
      simp only [beaconAuxUnit, beaconAux, StateT.run_lift, pure_bind, mem_support_pure_iff, Prod.mk.injEq]
      exact fun _ _ _ _ equal => equal.1.symm

/-- The actual prefix receipt and accepted inner decoder identify the public frame of the original finish request. No writer or readback contract is needed on this receive side. -/
theorem prefix_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (supported : some pending ∈ support ((beaconPrefix setup codec seed control identity oneTime kem raw).run' ()))
    (bytes : Pqxdh.Bytes) (record : RawCtxReceive.DecodedFrame)
    (application : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some bytes)
    (decoded : codec.frameRead bytes = some record) :
    PqxdhServerAuthRecordPublicationEvent.frame codec raw = some record := by
  have response := prefix_response setup codec seed control identity oneTime kem raw pending supported
  change codec.application pending.collected.response = some bytes at application
  simpa only [PqxdhServerAuthRecordPublicationEvent.frame, response,
    Option.bind_eq_bind, Option.bind_some, application] using decoded

/-- The original raw prefix and complete selected receive yield either the existing forgery monitor event or an earlier seal matching the public decoded record. The full callback receipt is retained; no response publication is presumed. -/
theorem prefix_program_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (prefixReached : some pending ∈ support ((beaconPrefix setup codec seed control identity oneTime kem raw).run' ()))
    (key : PqxdhSecretInputKdf.RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before)) :
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
        PqxdhServerAuthRecordPublicationEvent.frame codec raw =
          some ⟨staged.opened.sequence, staged.opened.keyId, entry.record.encode⟩ := by
  refine (PqxdhServerAuthDecodedOrigin.program_or_origin setup.source codec key rest pending staged
    before after good supported).imp_right ?_
  rintro ⟨bytes, target, kernel, entry, application, delivery, success, member, same, plaintext, decoded⟩
  exact ⟨bytes, target, kernel, entry, application, delivery, success, member, same, plaintext,
    prefix_frame setup codec seed control identity oneTime kem raw pending prefixReached bytes _ application decoded⟩

end BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.collect_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.collect_response

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_response

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_program_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse.prefix_program_origin
