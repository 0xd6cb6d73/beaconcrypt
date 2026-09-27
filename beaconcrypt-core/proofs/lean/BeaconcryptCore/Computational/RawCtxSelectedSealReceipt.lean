import BeaconcryptCore.Computational.RawCtxSelectedRoleReceipt

/-!
Successful selected sealing receipts retain cryptographic production separately from the source's optional writer result. The ordinary authentication history includes a produced CTX record even when the writer fails. These source facts therefore do not turn a matching prior CTX seal into an assumed successful network publication.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSealReceipt
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKey
open RawCtxSelectedAuthenticationObserver RawCtxSelectedAcceptedRecord
open RawCtxSelectedMessageSealing
open CtxRomAuth

/-- The actual selected callback records the challenger-produced typed record before preserving the writer's optional result. It requires no selected-key argument. -/
theorem selected_call (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 153) (before : State) :
    monitor (RawCtxSelectedSealConsumer.call c writer ⟨.hidden nonce, sequence, context⟩) before =
      (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr
            (selectedInput nonce sequence context width)))))
          pure (match reply with
              | none => SealResult.repeatedNonce
              | some record => .completed (writer ⟨sequence, context.senderId, record.encode⟩),
            step (.inl (.inl (.inr (.inr (selectedInput nonce sequence context width))))) reply before)) := by
  simp only [RawCtxSelectedSealConsumer.call, selected, dite_eq_left width,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, RawCtxSelectedSealConsumer.liftSelected]
  simp only [monitor, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [handler, StateT.run, bind_assoc, pure_bind]
  rfl

/-- Every completed selected call carries its actual typed record and writer result; explicit nonce refusal leaves the observer unchanged. A completed writer failure still appends the cryptographic production. -/
theorem selected_production (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 153) (before after : State) (result : SealResult)
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedSealConsumer.call c writer ⟨.hidden nonce, sequence, context⟩) before)) :
    (result = .repeatedNonce ∧ after = before) ∨
      ∃ record, result = .completed (writer ⟨sequence, context.senderId, record.encode⟩) ∧
        after = {before with seals := ⟨selectedInput nonce sequence context width, record⟩ :: before.seals} := by
  rw [selected_call c writer nonce sequence context width before] at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, _, equal⟩ := supported
  cases reply with
  | none =>
    cases equal
    exact Or.inl ⟨rfl, rfl⟩
  | some record =>
    cases equal
    exact Or.inr ⟨record, rfl, rfl⟩

/-- Every operation other than the selected seal leaves the selected successful-seal history unchanged, including known-key aliases and raw attempts. -/
theorem step_seals (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (reply : AdaptiveCtxDynamicKnownKeys.Spec.Range query) (before : State)
    (other : ¬AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query) :
    (step query reply before).seals = before.seals := by
  rcases query with ((coin | (hash | sealing)) | raw) | known
  all_goals simp only [RawCtxSelectedAuthenticationObserver.step, AdaptiveCtxDynamicKnownBounds.TargetClass,
    AdaptiveCtxQueryBounds.SourceSeal, not_true_eq_false] at other ⊢

/-- A complete adaptive component computation with zero selected seals retains the exact selected seal history; its other calls and actual optional replies are unrestricted. -/
theorem monitor_seals {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (noSeals : client.IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before : State) (result : Result × State) (supported : result ∈ support (monitor client before)) :
    result.2.seals = before.seals := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl
  | query_bind query continuation ih =>
    rw [monitor_query] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨reply, _, reached⟩ := supported
    rw [isQueryBoundP_query_bind_iff] at noSeals
    have absent : ¬AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal query := by
      simpa only [Nat.lt_irrefl, or_false] using noSeals.1
    have tail := ih reply (by simpa only [ite_eq_right absent] using noSeals.2 reply)
      (step query reply before) result reached
    exact tail.trans (step_seals query reply before absent)

/-- The actual pending selected seal propagates nonce refusal separately from the complete optional writer result while retaining the produced typed record and exact source metadata. -/
theorem sealing_selected (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (nonce : NonceOutput) (selectedMaterial : pending.material = .hidden nonce)
    (width : pending.context.associatedData.length = 153) (before after : State)
    (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support (monitor (RawCtxSelectedSealConsumer.sealing c writer pending) before)) :
    (result = none ∧ after = before) ∨
      ∃ record, result = some ((writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
          (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments pending))) ∧
        after = {before with seals := ⟨selectedInput nonce pending.sequence pending.context width, record⟩ :: before.seals} := by
  simp only [RawCtxSelectedSealConsumer.sealing, monitor_map, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, equal⟩ := supported
  have inputSame : RawCtxInterpretedArguments.sealArguments pending =
      ⟨.hidden nonce, pending.sequence, pending.context⟩ := by
    simp only [RawCtxInterpretedArguments.sealArguments, selectedMaterial]
  rw [inputSame] at reached
  have branches := selected_production c writer nonce pending.sequence pending.context width before actual.2 actual.1 reached
  rcases branches with ⟨refused, history⟩ | ⟨record, completed, history⟩
  · left
    have value := congrArg Prod.fst equal
    have state := congrArg Prod.snd equal
    exact ⟨by simpa only [refused, RawCtxSelectedSealConsumer.reply] using value.symm, state.symm.trans history⟩
  · right
    have value := congrArg Prod.fst equal
    have state := congrArg Prod.snd equal
    exact ⟨record, by simpa only [completed, RawCtxSelectedSealConsumer.reply] using value.symm, state.symm.trans history⟩

/-- Every newly recorded successful selected seal is attributed to the actual source pending capability and actual optional writer result. Known material, invalid AD and nonce refusal cannot add a selected receipt. -/
theorem sealing_provenance (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (before after : State) (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support (monitor (RawCtxSelectedSealConsumer.sealing c writer pending) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨
      ∃ (nonce : NonceOutput) (width : pending.context.associatedData.length = 153) (record : CtxRomRecord),
        pending.material = .hidden nonce ∧ entry = ⟨selectedInput nonce pending.sequence pending.context width, record⟩ ∧
        result = some ((writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
          (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments pending))) ∧
        after = {before with seals := entry :: before.seals} := by
  cases material : pending.material with
  | known value =>
    have noSeals : (RawCtxSelectedSealConsumer.sealing c writer pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
      simp only [RawCtxSelectedSealConsumer.sealing, isQueryBoundP_map_iff]
      simpa only [RawCtxInterpretedArguments.sealArguments, material] using
        RawCtxSelectedSealConsumer.call_seal c writer (RawCtxInterpretedArguments.sealArguments pending)
    have unchanged := monitor_seals (RawCtxSelectedSealConsumer.sealing c writer pending) noSeals before (result, after) supported
    exact Or.inl (unchanged ▸ found)
  | hidden nonce =>
    by_cases width : pending.context.associatedData.length = 153
    · rcases sealing_selected c writer pending nonce material width before after result supported with
        ⟨_, unchanged⟩ | ⟨record, published, history⟩
      · exact Or.inl (unchanged ▸ found)
      · rw [history] at found
        rcases List.mem_cons.mp found with same | earlier
        · exact Or.inr ⟨nonce, width, record, rfl, same, published, by simpa only [same] using history⟩
        · exact Or.inl earlier
    · simp only [RawCtxSelectedSealConsumer.sealing, RawCtxSelectedSealConsumer.call,
        RawCtxInterpretedArguments.sealArguments, material, selected, dite_eq_right width,
        simulateQ_pure, map_pure, monitor, StateT.run_pure, mem_support_pure_iff] at supported
      have unchanged : after = before := congrArg Prod.snd supported
      exact Or.inl (unchanged ▸ found)

/-- Once the actual produced frame has a successful writer result, its source API publication contains exactly those bytes, the caller's target ID and the prepared sequence. Encoded sender and target route are separate fields. -/
theorem produced_publication (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (writer : RawCtxMixedShared.Writer) (record : CtxRomRecord) (bytes : Pqxdh.Bytes)
    (written : writer ⟨pending.sequence, pending.context.senderId, record.encode⟩ = some bytes) :
    (writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
      (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments pending)) =
        some ⟨bytes, pending.context.targetId, pending.sequence⟩ := by
  simp only [written, Option.map_some, RawCtxInterpretedArguments.encrypted, RawCtxInterpretedArguments.sealArguments]

/-- The exact local serializer-success premise removes the unmatched-publication case for this produced frame; no generic writer totality or security assumption is inferred. -/
theorem produced_has_publication (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (writer : RawCtxMixedShared.Writer) (record : CtxRomRecord)
    (written : (writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).isSome = true) :
    ∃ bytes, writer ⟨pending.sequence, pending.context.senderId, record.encode⟩ = some bytes ∧
      (writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
        (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments pending)) =
          some ⟨bytes, pending.context.targetId, pending.sequence⟩ := by
  cases present : writer ⟨pending.sequence, pending.context.senderId, record.encode⟩ with
  | none => simp only [present, Option.isSome_none, Bool.false_eq_true] at written
  | some bytes => exact ⟨bytes, rfl, rfl⟩

/-- The complete source send attributes every new selected seal to its actual old-kernel derivation and prepared capability, retaining the advanced kernel and optional writer result even on publication failure. -/
theorem send_provenance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (before after : State) (result : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨
      ∃ pending, RawCtxInterpretedSend.normalBegin kernel context = .requested pending ∧
        let ready := RawCtxInterpretedSend.ready pending
          (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)
        ∃ (actualNonce : NonceOutput) (width : ready.context.associatedData.length = 153) (record : CtxRomRecord),
          ready.material = .hidden actualNonce ∧ entry = ⟨selectedInput actualNonce ready.sequence ready.context width, record⟩ ∧
          result = some (ready.advanced, (writer ⟨ready.sequence, ready.context.senderId, record.encode⟩).map
            (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments ready))) ∧
          after = {before with seals := entry :: before.seals} := by
  rw [RawCtxSelectedSendCompiler.send_cases] at supported
  cases started : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted initial actualContext =>
    simp only [started, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    have unchanged : after = before := congrArg Prod.snd supported
    exact Or.inl (unchanged ▸ found)
  | requested pending =>
    simp only [started, monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨outcome, reached, equal⟩ := supported
    have history : outcome.2 = after := congrArg Prod.snd equal
    have recorded : entry ∈ outcome.2.seals := history.symm ▸ found
    rcases sealing_provenance source.crypto writer
      (RawCtxInterpretedSend.ready pending (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request))
      before outcome.2 outcome.1 reached entry recorded with old | produced
    · exact Or.inl old
    · obtain ⟨actualNonce, width, record, material, entrySame, published, state⟩ := produced
      have finalValue := congrArg Prod.fst equal
      simp only [published, Option.map_some] at finalValue
      exact Or.inr ⟨pending, rfl, actualNonce, width, record, material, entrySame,
        finalValue.symm, history.symm.trans state⟩

/-- A match against a produced seal fixes exactly the nonce, authenticated AD, sequence, encoded sender and protected payload. It supplies no installation/session identity or caller target-ID equality. -/
theorem full_tuple_fields (target : CtxUnclaimedAcceptance.Target) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 153) (record : CtxRomRecord)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal ⟨selectedInput nonce sequence context width, record⟩) :
    target.nonce = nonce ∧ target.context.ad.bytes = context.associatedData ∧
      target.context.ad.seq = sequence.val ∧ target.context.ad.sid = context.senderId.val ∧
      target.record.encode = record.encode := by
  refine ⟨same.1, ?_, ?_, ?_, same.2.2⟩
  · exact congrArg Pqxdh.RecordAD.bytes same.2.1
  · exact congrArg Pqxdh.RecordAD.seq same.2.1
  · exact congrArg Pqxdh.RecordAD.sid same.2.1

/-- Mathematical source instrumentation retains the actual typed cryptographic production together with the unchanged optional writer. The selected key is an interpreter parameter here. -/
noncomputable def production (c : Pqxdh.Crypto) (key : RootOutput) (writer : RawCtxMixedShared.Writer)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 153) : OracleComp CtxRO (CtxRomRecord × Option Pqxdh.Bytes) := do
  let record ← ctxSeal c key (selectedInput nonce sequence context width)
  pure (record, writer ⟨sequence, context.senderId, record.encode⟩)

/-- Erasing only the produced-record annotation is exactly the actual native source seal and writer, before arbitrary shared-ROM interpretation and continuation. -/
theorem production_source (c : Pqxdh.Crypto) (key : RootOutput) (writer : RawCtxMixedShared.Writer)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 153) :
    Prod.snd <$> production c key writer nonce sequence context width =
      simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
        (RawCtxSourceSeal.sealInput (selectedNative key nonce sequence context)) := by
  rw [RawCtxCanonicalSeal.sealInput_typed c writer (selectedNative key nonce sequence context) width]
  obtain ⟨keySame, inputSame⟩ := selected_input key nonce sequence context width
  rw [keySame, inputSame]
  simp only [production, map_bind, map_pure, RawCtxCanonicalSeal.recordFrame, selectedNative]

end BeaconcryptCore.Computational.RawCtxSelectedSealReceipt

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.selected_call
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.selected_production' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.selected_production
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.step_seals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.step_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.monitor_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.monitor_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.sealing_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.sealing_selected
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.sealing_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.sealing_provenance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.produced_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.produced_publication
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.produced_has_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.produced_has_publication
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.send_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.send_provenance
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.full_tuple_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.full_tuple_fields
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.production_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealReceipt.production_source
