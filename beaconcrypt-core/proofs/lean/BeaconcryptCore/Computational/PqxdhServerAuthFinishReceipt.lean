import BeaconcryptCore.Computational.PqxdhServerAuthFinishMaterial
import BeaconcryptCore.Computational.PqxdhPhase2LocalMatching
import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical

/-! Actual selected-opening provenance for an accepted Beacon finish. Receipts are derived from the literal executable callback, retaining the queried bytes and actual optional plaintext. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhServerAuthCtxCalls

/-- The actual first uncached opening selects precisely its stored material and sequence one. -/
theorem opening_input (send receiving next : Chain) (material : Material)
    (context : RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedArguments.openArguments (PqxdhServerAuthCtxCalls.opening
      (PqxdhServerAuthBeaconFirstOpening.opening send receiving next material context)) =
      some ⟨material, 1#u64, context⟩ := by
  have selected := (RawCtxInterpretedArguments.material_total (PqxdhServerAuthCtxCalls.opening
    (PqxdhServerAuthBeaconFirstOpening.opening send receiving next material context))).choose_spec
  have sequence := (RawCtxInterpretedArguments.sequence_total (PqxdhServerAuthCtxCalls.opening
    (PqxdhServerAuthBeaconFirstOpening.opening send receiving next material context))).choose_spec
  change ok (core.option.Option.Some material) = _ at selected
  change ok 1#u64 = _ at sequence
  simp only [RawCtxInterpretedArguments.openArguments, ← RustM.ok.inj selected, ← RustM.ok.inj sequence]
  rfl

/-- The complete sequence-one driver reaches one selected raw request and returns that request's actual optional plaintext before the source finish. -/
theorem execute_selected (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (send : Chain)
    (context : RawCtxWholeOwner.OpenContext) (width : context.associatedData.length = 281) :
    simulateQ (receive source rest read expected)
      (RawCtxChainReceive.execute (PqxdhServerAuthBeaconFirstOpening.initial send .hidden) 1#u64 context) =
      (do
        let plaintext ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr
          (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope rest.1 context width))))
        let reply := RawCtxSharedOpeningConsumer.apiReply 1#u64 context plaintext
        pure ((match reply with
          | .None => PqxdhServerAuthBeaconFirstOpening.initial send .hidden
          | .Some _ => PqxdhServerAuthBeaconFirstOpening.published send
              (.known (RawCtxFreshChainCut.concreteChain rest.2.1))), reply)) := by
  rw [PqxdhServerAuthBeaconFirstOpening.execute_one]
  simp only [receive, step, pure_bind, RawCtxSelectedOpenConsumer.service, opening_input,
    RawCtxUniversalOpening.call, dite_eq_left width, bind_map_left]
  congr 1
  funext plaintext
  cases plaintext <;> rfl

/-- The source's final registration observation after its single selected opening. -/
noncomputable def completed (rest : Residual) (candidate : pqxdh.BeaconRegistrationCandidate)
    (context : RawCtxWholeOwner.OpenContext) (plaintext : Option Pqxdh.Bytes) :
    Option PqxdhBeaconPhase2Publication.Staged :=
  let reply := RawCtxSharedOpeningConsumer.apiReply 1#u64 context plaintext
  PqxdhBeaconPhase2Publication.afterOpening candidate
    (PqxdhServerAuthCtxBuildSettlement.resolve (match reply with
      | .None => PqxdhServerAuthFinishMaterial.initial rest.2.2
      | .Some _ => PqxdhServerAuthBeaconFirstOpening.published
          (.known (RawCtxFreshChainCut.concreteChain rest.2.2))
          (.known (RawCtxFreshChainCut.concreteChain rest.2.1)))) reply

/-- Every actual valid sequence-one delivery uses exactly the selected raw query before the original registration observation. -/
theorem raw_one (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (frame : RawCtxReceive.DecodedFrame)
    (nonempty : bytes.isEmpty = false) (decoded : read bytes = some frame)
    (valid : RawCtxReceive.ValidFrame candidate.server_binding.identity_key_id
      (absBytes candidate.associated_data) frame) (one : frame.sequence = 1#u64) :
    PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate =
      completed rest candidate ⟨bytes, frame, absBytes candidate.associated_data⟩ <$>
        (AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr (RawCtxUniversalDecoder.pack
          (RawCtxUniversalDecoder.envelope rest.1 ⟨bytes, frame, absBytes candidate.associated_data⟩ valid.2.2)))) :
          OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Pqxdh.Bytes)) := by
  simp only [PqxdhServerAuthFinishMaterial.rawProgram, raw, RawCtxChainOwner.rawReceive,
    StateT.run, nonempty, Bool.false_eq_true, ite_false, decoded,
    PqxdhServerAuthFinishMaterial.localState, valid, ite_true, bind_pure_comp,
    Functor.map_map, calls, one, PqxdhServerAuthFinishMaterial.initial]
  rw [execute_selected source rest read frame.sender _ _ valid.2.2]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

/-- Syntactic success of the literal raw callback supplies the actual accepted frame and input sequence one. This does not assume successful parsing or move the sequence gate before opening. -/
theorem raw_accepts (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : some staged ∈ support
      (PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate)) :
    bytes.isEmpty = false ∧ ∃ frame, read bytes = some frame ∧
      RawCtxReceive.ValidFrame candidate.server_binding.identity_key_id
        (absBytes candidate.associated_data) frame ∧ frame.sequence = 1#u64 := by
  unfold PqxdhServerAuthFinishMaterial.rawProgram raw RawCtxChainOwner.rawReceive at supported
  dsimp only [StateT.run] at supported
  split at supported
  · simp only [map_pure, PqxdhServerAuthFinishMaterial.observe, RawCtxChainOwner.publish,
      PqxdhBeaconPhase2Publication.afterOpening, support_pure, Set.mem_singleton_iff,
      reduceCtorEq] at supported
  · rename_i nonempty
    refine ⟨Bool.eq_false_iff.mpr nonempty, ?_⟩
    split at supported
    · simp only [map_pure, PqxdhServerAuthFinishMaterial.observe, RawCtxChainOwner.publish,
        PqxdhBeaconPhase2Publication.afterOpening, support_pure, Set.mem_singleton_iff,
        reduceCtorEq] at supported
    · rename_i frame decoded
      split at supported
      · rename_i valid
        refine ⟨frame, decoded, valid, ?_⟩
        by_contra wrong
        simp only [bind_pure_comp, Functor.map_map, PqxdhServerAuthFinishMaterial.observe,
          RawCtxChainOwner.publish, calls] at supported
        have rejected := PqxdhServerAuthFinishMaterial.program_wrong source rest read frame.sender candidate
          PqxdhServerAuthCtxBuildSettlement.resolve frame.sequence
          ⟨bytes, frame, absBytes candidate.associated_data⟩
          (RawCtxChainReceive.normalBegin (PqxdhServerAuthFinishMaterial.initial rest.2.2) frame.sequence
            ⟨bytes, frame, absBytes candidate.associated_data⟩) (begin_scope _ _ _) wrong
        simp only [RawCtxChainReceive.execute, PqxdhServerAuthFinishMaterial.localState] at supported
        rw [rejected] at supported
        simp only [support_map, Set.mem_image, reduceCtorEq, and_false, exists_false] at supported
      · simp only [map_pure, PqxdhServerAuthFinishMaterial.observe, RawCtxChainOwner.publish,
          PqxdhBeaconPhase2Publication.afterOpening, support_pure, Set.mem_singleton_iff,
          reduceCtorEq] at supported

open RawCtxSelectedAuthenticationObserver in
/-- Accepted raw execution supplies the original validated frame and the exact selected attempt in the existing authentication observer, including its actual plaintext and attempt-time seal history. -/
theorem monitored_raw (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (supported : (some staged, after) ∈ support (monitor
      (PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate) before)) :
    bytes.isEmpty = false ∧ ∃ (frame : RawCtxReceive.DecodedFrame)
      (valid : RawCtxReceive.ValidFrame candidate.server_binding.identity_key_id
        (absBytes candidate.associated_data) frame) (plaintext : Pqxdh.Bytes),
      read bytes = some frame ∧ frame.sequence = 1#u64 ∧
      completed rest candidate ⟨bytes, frame, absBytes candidate.associated_data⟩ (some plaintext) = some staged ∧
      after = RawCtxSelectedAuthenticationObserver.step (.inl (.inr (RawCtxUniversalDecoder.pack
        (RawCtxUniversalDecoder.envelope rest.1 ⟨bytes, frame, absBytes candidate.associated_data⟩ valid.2.2))))
        (some plaintext) before := by
  have syntactic : some staged ∈ support
      (PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate) := by
    rw [← monitor_erase (PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate) before, support_map]
    exact ⟨(some staged, after), supported, rfl⟩
  obtain ⟨nonempty, frame, decoded, valid, one⟩ := raw_accepts source rest read bytes candidate staged syntactic
  refine ⟨nonempty, frame, valid, ?_⟩
  rw [raw_one source rest read bytes candidate frame nonempty decoded valid one] at supported
  rw [RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  simp only [monitor, simulateQ_spec_query, handler, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at reached
  obtain ⟨reply, _, rfl⟩ := reached
  cases reply with
  | none =>
    have impossible := congrArg Prod.fst equal
    simp only [completed, RawCtxSharedOpeningConsumer.apiReply,
      PqxdhBeaconPhase2Publication.afterOpening, reduceCtorEq] at impossible
  | some plaintext =>
    exact ⟨plaintext, decoded, one, congrArg Prod.fst equal, (congrArg Prod.snd equal).symm⟩

open RawCtxSelectedAuthenticationObserver in
/-- The concrete accepted callback supplies both the original local target and a present actual observer attempt. Its plaintext comes from the challenger reply and its seal history is the one preceding the attempt. -/
theorem raw_target (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (supported : (some staged, after) ∈ support (monitor
      (PqxdhServerAuthFinishMaterial.rawProgram source rest read bytes candidate) before)) :
    ∃ (componentBytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target) (kernel : ConcreteRatchetKernel),
      RawCtxUniversalDecoder.decoder read componentBytes = some target ∧
      PqxdhPhase2LocalMatching.LocalTarget read bytes candidate staged.opened target ∧
      PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged ∧
      ⟨componentBytes, some staged.opened.plaintext, before.seals⟩ ∈ after.attempts := by
  obtain ⟨nonempty, frame, valid, plaintext, decoded, one, accepted, afterEq⟩ :=
    monitored_raw source rest read bytes candidate staged before after supported
  obtain ⟨slices, parsed⟩ := (RawCtxFrameDecoding.fromPayload_some_iff frame.payload).2 valid.2.1
  let context : RawCtxWholeOwner.OpenContext := ⟨bytes, frame, absBytes candidate.associated_data⟩
  let envelope := RawCtxUniversalDecoder.envelope rest.1 context valid.2.2
  let target := RawCtxKeyFreeDecoder.target rest.1 frame.sequence frame (absBytes candidate.associated_data)
    slices parsed valid.2.2
  let kernel : ConcreteRatchetKernel := PqxdhServerAuthCtxBuildSettlement.resolve
    (PqxdhServerAuthBeaconFirstOpening.published
      (.known (RawCtxFreshChainCut.concreteChain rest.2.2))
      (.known (RawCtxFreshChainCut.concreteChain rest.2.1)))
  have success : PqxdhBeaconPhase2Publication.afterOpening candidate kernel
      (.Some ⟨plaintext, frame.sender, 1#u64⟩) = some staged := accepted
  have opened : staged.opened = ⟨plaintext, frame.sender, 1#u64⟩ := by
    have same := (PqxdhPhase2LocalMatching.authenticated_binding candidate kernel _ staged success).1
    injection same with same
    exact same.symm
  refine ⟨RawCtxUniversalDecoder.pack envelope, target, kernel, ?_, ?_, ?_, ?_⟩
  · exact RawCtxUniversalDecoder.decoder_pack read envelope frame slices nonempty decoded parsed
  · exact ⟨frame, rest.1, slices, parsed, valid.2.2, nonempty, decoded, valid,
      by rw [opened], by rw [opened]; exact one.symm, rfl⟩
  · simpa only [opened] using success
  · rw [afterEq, opened]
    exact List.mem_cons_self

open PqxdhServerAuthExperiment RawCtxSelectedAuthenticationObserver
variable {Reader Response : Type}

/-- The complete callback's actual optional application getter supplies the raw bytes of every successful monitored finish. -/
theorem program_raw (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged) (before after : RawCtxSelectedAuthenticationObserver.State)
    (supported : (some staged, after) ∈ support (monitor
      (PqxdhServerAuthFinishMaterial.program source codec rest pending) before)) :
    ∃ bytes, codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response = some bytes ∧
      (some staged, after) ∈ support (monitor (PqxdhServerAuthFinishMaterial.rawProgram source rest
        codec.frameRead bytes (PqxdhBeaconPhase2Publication.clearedCandidate
          (PqxdhPhase2DhRootConsumer.cleared pending).candidate)) before) := by
  unfold PqxdhServerAuthFinishMaterial.program at supported
  dsimp only at supported
  cases found : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response with
  | none =>
    simp only [found, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | some bytes => exact ⟨bytes, rfl, by simpa only [found] using supported⟩

/-- Complete accepted callback provenance includes the actual application bytes, original local target, source registration observation and selected observer attempt. -/
theorem program_target (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged) (before after : RawCtxSelectedAuthenticationObserver.State)
    (supported : (some staged, after) ∈ support (monitor
      (PqxdhServerAuthFinishMaterial.program source codec rest pending) before)) :
    let prepared := PqxdhPhase2DhRootConsumer.cleared pending
    let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
    ∃ (bytes componentBytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target) (kernel : ConcreteRatchetKernel),
      codec.application prepared.response = some bytes ∧
      RawCtxUniversalDecoder.decoder codec.frameRead componentBytes = some target ∧
      PqxdhPhase2LocalMatching.LocalTarget codec.frameRead bytes candidate staged.opened target ∧
      PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged ∧
      ⟨componentBytes, some staged.opened.plaintext, before.seals⟩ ∈ after.attempts := by
  obtain ⟨bytes, application, reached⟩ := program_raw source codec rest pending staged before after supported
  obtain ⟨componentBytes, target, kernel, decoded, delivery, success, attempt⟩ :=
    raw_target source rest codec.frameRead bytes _ staged before after reached
  exact ⟨bytes, componentBytes, target, kernel, application, decoded, delivery, success, attempt⟩

/-- In the actual ordinary component interpretation, every accepted complete Beacon callback either wins the existing observer or matches a prior selected seal with exactly the accepted plaintext. The correct-history invariant is the existing invariant proved from empty endpoint state. -/
theorem program_or_match (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (key : RootOutput) (rest : Residual) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (observed true (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key)
      (PqxdhServerAuthFinishMaterial.program source codec rest pending)).run before)) :
    won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      let prepared := PqxdhPhase2DhRootConsumer.cleared pending
      let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
      ∃ (bytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target) (kernel : ConcreteRatchetKernel)
        (entry : CtxRomAuth.CtxSuccessfulSeal),
        codec.application prepared.response = some bytes ∧
        PqxdhPhase2LocalMatching.LocalTarget codec.frameRead bytes candidate staged.opened target ∧
        PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged ∧
        entry ∈ before.1.seals ∧ target.toLegacy.sameFullTupleAsSuccessfulSeal entry ∧
        staged.opened.plaintext = entry.input.plaintext := by
  classical
  have monitored := PqxdhFirstBeaconRecordCanonical.observed_monitor
    (RawCtxUniversalDecoder.decoder codec.frameRead) source.crypto key
    (PqxdhServerAuthFinishMaterial.program source codec rest pending) before (some staged, after) supported
  obtain ⟨bytes, componentBytes, target, kernel, application, decoded, delivery, success, attempt⟩ :=
    program_target source codec rest pending staged before.1 after.1 monitored
  by_cases winning : won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true
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
    exact ⟨bytes, target, kernel, entry, application, delivery, success, member, same, Option.some.inj plaintext⟩

/-- An actual matching selected seal with its source binding context fixes precisely the accepted registration fields. This compares the authenticated fields rather than raw serialization bytes. -/
theorem matched_fields (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (success : PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget read bytes candidate staged.opened target)
    (entry : CtxRomAuth.CtxSuccessfulSeal) (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (plaintext : staged.opened.plaintext = entry.input.plaintext)
    (context : RawCtxSourceSend.SealContext) (records : PqxdhPhase2LocalMatching.Records entry context)
    (bound : PqxdhPhase2LocalMatching.KeyIdBound context) :
    PqxdhPhase2LocalMatching.acceptedFields staged = PqxdhPhase2LocalMatching.sealedFields context := by
  have ad := (PqxdhPhase2LocalMatching.localTarget_context read bytes candidate staged.opened target delivery).1
  have entryAd := same.2.1.symm.trans ad
  exact PqxdhPhase2LocalMatching.accepted_of_plaintext candidate kernel _ staged success context bound
    (plaintext.trans records.1) ((congrArg (fun value => value.bytes) entryAd).symm.trans records.2.1)

/-- The approved abstract readable-frame contract rules out writer failure only for the concrete seal frame that actually matches an accepted decoded target. It requires no canonical encoding or blanket writer totality. -/
theorem matched_writable (writer : RawCtxMixedShared.Writer) (read : RawCtxReceive.FrameDecoder)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable writer read)
    (bytes : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate)
    (opened : RawCtxWholeOwner.Decrypted) (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget read bytes candidate opened target)
    (entry : CtxRomAuth.CtxSuccessfulSeal) (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (sequence sender : Std.U64) (seq : entry.input.context.ad.seq = sequence.val)
    (sid : entry.input.context.ad.sid = sender.val) :
    ∃ encoded, writer ⟨sequence, sender, entry.record.encode⟩ = some encoded := by
  obtain ⟨frame, nonce, slices, parsed, width, _, decoded, _, _, _, rfl⟩ := delivery
  have frameSeq : frame.sequence = sequence := UScalar.eq_of_val_eq
    ((congrArg (fun value => value.seq) same.2.1).trans seq)
  have frameSender : frame.sender = sender := UScalar.eq_of_val_eq
    ((congrArg (fun value => value.sid) same.2.1).trans sid)
  have payload : frame.payload = entry.record.encode :=
    (RawCtxSelectedPlaintextOrigins.record_payload frame slices parsed).symm.trans same.2.2
  have equal : frame = ⟨sequence, sender, entry.record.encode⟩ := by
    change (⟨frame.sequence, frame.sender, frame.payload⟩ : RawCtxReceive.DecodedFrame) = _
    rw [frameSeq, frameSender, payload]
  obtain ⟨encoded, written⟩ := writable bytes frame decoded
  exact ⟨encoded, by rw [← equal]; exact written⟩

end BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.opening_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.opening_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.execute_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.execute_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_one

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_accepts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.monitored_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.monitored_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.raw_target

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_target

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_or_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.program_or_match

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.matched_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.matched_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.matched_writable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt.matched_writable
