import BeaconcryptCore.Computational.PqxdhServerAuthFinishResponse

/-! Preserve the original public raw frame through the full selected finish and source acceptance gate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exact decoded fields of a selected component record; source ordinals are compared at their bounded numeric value. -/
def Matches (frame : RawCtxReceive.DecodedFrame) (entry : CtxRomAuth.CtxSuccessfulSeal) : Prop :=
  frame.sequence.val = entry.input.context.ad.seq ∧ frame.sender.val = entry.input.context.ad.sid ∧
    frame.payload = entry.record.encode

/-- The literal original public raw request decodes to an actual earlier selected record. This alone does not assert outer response publication. -/
def Receipt (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∃ entry ∈ observer.seals, ∃ frame,
    PqxdhServerAuthRecordPublicationEvent.frame codec raw = some frame ∧ Matches frame entry

/-- The complete selected receive returns an existing ordinary forgery event or an exact public-frame receipt. Its supplied raw decode is the functional fact established by the original source prefix. -/
theorem program_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (raw : Pqxdh.Bytes)
    (response : codec.read2 raw = some pending.collected.response)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      Receipt codec raw after.1 := by
  refine (PqxdhServerAuthDecodedOrigin.program_or_origin setup.source codec key rest pending staged
    before after good supported).imp_right ?_
  rintro ⟨bytes, target, kernel, entry, application, delivery, success, member, same, plaintext, decoded⟩
  have retained : after.1.seals = before.1.seals := PqxdhFirstBeaconRecordCanonical.observed_seals _ _ _ _
    (PqxdhServerAuthFinishMaterial.program_other setup.source codec rest pending).1 before (some staged, after) supported
  have context := same.2.1.symm.trans
    (PqxdhPhase2LocalMatching.localTarget_context codec.frameRead bytes _ staged.opened target delivery).1
  refine ⟨entry, by simpa only [retained] using member,
    ⟨staged.opened.sequence, staged.opened.keyId, entry.record.encode⟩, ?_,
    (congrArg Pqxdh.RecordAD.seq context).symm, (congrArg Pqxdh.RecordAD.sid context).symm, rfl⟩
  change codec.application pending.collected.response = some bytes at application
  simpa only [PqxdhServerAuthRecordPublicationEvent.frame, response,
    Option.bind_eq_bind, Option.bind_some, application] using decoded

/-- Success of the complete selected callback preserves the actual raw-frame receipt through both final source binding checks and full native publication. -/
theorem selected_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (control : pqxdh.BeaconInitSent)
    (raw payload : Pqxdh.Bytes) (response : codec.read2 raw = some pending.collected.response)
    (localBefore localAfter : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : ((some payload, localAfter), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.selected setup.source codec rest control pending).run localBefore)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      Receipt codec raw after.1 := by
  change ((some payload, localAfter), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
    (PqxdhServerAuthCtxFinish.complete control localBefore <$>
      PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before) at supported
  rw [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨staged, component⟩, reached, equal⟩ := supported
  rcases Prod.mk.inj equal with ⟨returned, rfl⟩
  cases staged with
  | none => cases (congrArg Prod.fst returned)
  | some staged => exact program_receipt setup codec key rest pending raw response staged before component good reached

/-- The actual active finish retains its original raw decode and both table routes. Success gives an ordinary observer win, an occupied ordinary-root entry, or the exact public-frame receipt. -/
theorem active_finish_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw payload : Pqxdh.Bytes)
    (state final : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : Unit ⊕ PqxdhJointGapDh.ScalarBytes) (kem : KemSK)
    (phase : state.1.1.beacon.beacon.phase = .initSent control prekey oneTime kem)
    (supported : ((some payload, final), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context final ∨ Receipt codec raw after.1 := by
  have runBind {σ α β : Type} (work : StateT σ ProbComp α)
      (next : α → StateT σ ProbComp β) (initial : σ) :
      (work >>= next) initial = work initial >>= fun result => next result.1 result.2 := rfl
  have runCoins {α : Type} (work : ProbComp α)
      (initial : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) :=
    PqxdhServerAuthCtxAcceptanceCover.observed_coins setup.source key codec.frameRead work initial
  simp only [StateT.run] at runCoins
  simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_bind,
    runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨prepared, prefixReached, supported⟩ := supported
  cases prepared with
  | none =>
    simp only [simulateQ_pure] at supported
    cases (congrArg (fun value => value.1.1) ((mem_support_pure_iff _ _).mp supported))
  | some pending =>
    simp only [simulateQ_bind, runBind, runCoins, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨derived, reached, supported⟩ := supported
    cases reply : derived.1 with
    | rejected =>
      simp only [reply, simulateQ_pure] at supported
      cases (congrArg (fun value => value.1.1) ((mem_support_pure_iff _ _).mp supported))
    | root root =>
      simp only [reply] at supported
      obtain ⟨bytes, input, occupied⟩ := PqxdhServerAuthCtxChronology.table_root setup context select
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
        state.1.2.2 derived.2 root (by rw [← reply]; exact reached)
      refine Or.inr (Or.inl (PqxdhServerAuthCtxAcceptanceCover.known_ordinary setup codec context key
        control pending root _ final ?_ before after (some payload) supported))
      refine ⟨bytes, ?_, occupied⟩
      change beaconInput setup context.seed context.scalar
        (state.1.1.ghost.touches ++ [Touch.beacon _]) = some bytes
      rw [beaconInput, firstBeacon_after _ [] _
        (invariant.trace.shape.clean ⟨control, prekey, oneTime, kem, phase⟩), Option.bind_some]
      exact input
    | hidden =>
      simp only [reply] at supported
      exact (selected_receipt setup codec key rest pending control raw payload
        (PqxdhServerAuthFinishResponse.prefix_response setup codec context.beaconSeed control
          state.1.1.beacon.beacon.identity oneTime kem raw pending prefixReached)
        _ final before after invariant.good supported).imp_right Or.inr

/-- Every successful complete finish, with all original phase checks and rejection behavior, retains the exact original public-frame receipt or one of the existing ordinary alternatives. -/
theorem finish_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (select : Bool) (raw payload : Pqxdh.Bytes)
    (state final : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (supported : ((some payload, final), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.finish setup codec context rest select raw).run state)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context final ∨ Receipt codec raw after.1 := by
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    exact active_finish_receipt setup codec context key rest Q j select raw payload state final before after
      invariant control prekey oneTime kem phase supported
  | _ =>
    simp only [PqxdhServerAuthCtxFinish.finish, StateT.run, phase, simulateQ_pure] at supported
    cases (congrArg (fun value => value.1.1) ((mem_support_pure_iff _ _).mp supported))

/-- The complete API handler, including designation settlement, retains a receipt for its actual successful public finish reply. -/
theorem handler_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (raw payload : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state before)
    (result : (Option (Option Pqxdh.Bytes) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j (.inr (.finish raw))).run.run state)).run before))
    (returned : result.1.1 = some (some payload)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context result.1.2 ∨ Receipt codec raw result.2.1 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxHandler.settle Q j (.inr (.finish raw)) state <$>
        ((PqxdhServerAuthCtxHandler.route setup codec checks context rest
          (!state.2 && PqxdhServerAuthEntryFactor.hiddenDesignated Q j (.inr (.finish raw)) state.1)
          (.inr (.finish raw))).run.run state))).run before) at supported
  simp only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp, StateT.run_map,
    Functor.map_map, simulateQ_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have reply : inner.1.1 = some payload := by
    cases bad : state.1.2.2.bad <;> simpa only [PqxdhServerAuthCtxHandler.settle, keepHiddenBad, bad,
      Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, Option.some.injEq] using returned
  have retained := finish_receipt setup codec context key rest Q j
    (!state.2 && hiddenDesignated Q j (.inr (.finish raw)) state.1) raw payload state inner.1.2
    before inner.2 invariant (by rw [← reply]; exact reached)
  unfold PqxdhServerAuthCtxHandler.settle keepHiddenBad
  split <;> exact retained

/-- The post-callback checkpoint retains the successful public finish's original frame receipt and complete component work. -/
theorem stopped_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (raw payload : Pqxdh.Bytes)
    (state : PqxdhServerAuthCtxState.Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (invariant : PqxdhServerAuthCtxObserverHistory.Joint setup codec context key Q j state.1 before)
    (result : (Option (Option Pqxdh.Bytes) × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) (.inr (.finish raw))).run state)).run before))
    (returned : result.1.1 = some (some payload)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true ∨
      PqxdhServerAuthCtxAcceptanceCover.Ordinary setup context result.1.2.1 ∨ Receipt codec raw result.2.1 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have normal : inner.1.1 = some (some payload) := by
    cases reply : inner.1.1 <;> simpa only [PqxdhServerAuthCtxStop.observe, reply,
      PqxdhServerAuthCtxStop.checkpoint] using returned
  simpa only [PqxdhServerAuthCtxStop.observe_state] using
    handler_receipt setup codec checks context key rest Q j raw payload state.1 before invariant inner reached normal

end BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.program_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.program_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.selected_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.selected_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.active_finish_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.active_finish_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.finish_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.finish_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.handler_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.handler_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.stopped_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishFrameReceipt.stopped_receipt
