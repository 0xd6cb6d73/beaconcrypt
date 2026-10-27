-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer

/-! Retain the exact frame handed to the writer by a source seal, including writer failure. These operational equations add no source nonce invariant or cryptographic security assumption. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog
open CtxRomAuth

abbrev Frame := RawCtxReceive.DecodedFrame

/-- The existing source seal compiled into the mixed primitive interface and logged by the deployment logger. -/
def native (input : RawCtxSourceSend.SealInput) :
    OracleComp RawCtxMixedOwner.NativeSpec (Option Pqxdh.Bytes × List Frame) :=
  PqxdhDeploymentNative.logged (simulateQ (RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift)
    (RawCtxSourceSeal.sealInput input))

set_option backward.isDefEq.respectTransparency false in
/-- Source frame production occurs before the optional writer result, retaining the exact shared cache and arbitrary auxiliary state. -/
theorem native_valid {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length = 281)
    (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (RawCtxMixedShared.sharedImpl c writer kdf) (native input)).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal c (RawCtxCanonicalSeal.sourceKey input) (RawCtxCanonicalSeal.sourceInput input width))).run cache
      let frame := RawCtxCanonicalSeal.recordFrame input result.1
      pure ((writer frame, [frame]), (auxiliary, result.2))) := by
  simp [native, PqxdhDeploymentNative.logged, PqxdhDeploymentNative.frameLog,
    RawCtxSourceSeal.sealInput, QueryImpl.compose, RawCtxMixedOwner.sendLift,
    RawCtxSourceSeal.sealLift, OracleSpec.query, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter, width,
    RawCtxSourceSeal.aeadInput, c.aeadSeal_tag_length, ctxSeal,
    RawCtxCanonicalSeal.sourceKey, RawCtxCanonicalSeal.sourceNonce,
    RawCtxCanonicalSeal.sourceInput, RawCtxCanonicalSeal.sourceContext,
    RawCtxCanonicalSeal.recordFrame, RawCtxSourceSeal.hashInput, outerInput,
    CtxRomRecord.encode, CtxRomRecord.toRecordCipher, Pqxdh.RecordCipher.encode,
    RawCtxSourceSeal.frame, StateT.run_bind, StateT.run_lift, StateT.run_map]

  dsimp only [StateT.run, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl]
  simp [PqxdhDeploymentNative.frameLog, RawCtxMixedOwner.sendLift,
    RawCtxSourceSeal.sealLift, OracleSpec.query, RawCtxMixedShared.sharedAdapter,
    ctxRandomOracle, List.append_assoc]

  simp only [← bind_pure_comp]
  rfl

/-- Invalid AD yields no produced frame under the existing total functional AEAD presentation. -/
theorem native_invalid {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length ≠ 281)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxMixedShared.sharedImpl c writer kdf) (native input)).run state =
      pure ((none, []), state) := by
  simp [native, PqxdhDeploymentNative.logged, PqxdhDeploymentNative.frameLog,
    RawCtxSourceSeal.sealInput, QueryImpl.compose, RawCtxMixedOwner.sendLift,
    RawCtxSourceSeal.sealLift, OracleSpec.query, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter, width, StateT.run_bind, StateT.run_lift, StateT.run_pure]

/-- The typed CTX computation retains the produced frame before applying the optional writer. -/
noncomputable def typed (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) : OracleComp CtxRO (Option Pqxdh.Bytes × List Frame) :=
  if width : input.context.associatedData.length = 281 then do
    let record ← ctxSeal c (RawCtxCanonicalSeal.sourceKey input) (RawCtxCanonicalSeal.sourceInput input width)
    let frame := RawCtxCanonicalSeal.recordFrame input record
    pure (writer frame, [frame])
  else pure (none, [])

/-- The complete native logger equals the typed computation on every AD input, retaining the original auxiliary state and complete hash cache. -/
theorem native_complete {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (RawCtxMixedShared.sharedImpl c writer kdf) (native input)).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ ctxRandomOracle (typed c writer input)).run cache := by
  unfold typed
  split <;> simp_all only [native_valid, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  exact native_invalid c writer kdf input ‹_› (auxiliary, cache)

/-- Erasing just the returned frame list recovers the existing typed source seal, before any interpreter. -/
theorem typed_forget (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    Prod.fst <$> typed c writer input = RawCtxCanonicalSeal.typedSource c writer input := by
  unfold typed RawCtxCanonicalSeal.typedSource
  split <;> simp only [map_bind, map_pure]

open AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open RawCtxSelectedMessageSealing

/-- The selected sealing query returns its actual protected record; the log is formed before applying the original writer. The key is absent from this program. -/
noncomputable def selected (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) :
    OracleComp ReceiveSpec (SealResult × List Frame) :=
  if width : context.associatedData.length = 281 then do
    let reply ← ReceiveSpec.query (.inl (.inr (.inr (selectedInput nonce sequence context width))))
    pure (match reply with
      | none => (.repeatedNonce, [])
      | some record =>
          let frame : Frame := ⟨sequence, context.senderId, record.encode⟩
          (.completed (writer frame), [frame]))
  else pure (.completed none, [])

/-- Known keys keep the original real local seal and route its exact hash to the selected challenger's shared cache. -/
noncomputable def known (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) : OracleComp ReceiveSpec (Option Pqxdh.Bytes × List Frame) :=
  simulateQ AdaptiveCtxSharedTarget.forward (simulateQ hashLift (typed c writer input))

/-- The log carries no hidden key; both branches preserve the original optional writer outcome and explicit selected-nonce stop. -/
noncomputable def call (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    OracleComp Spec (SealResult × List Frame) :=
  simulateQ RawCtxSelectedSealConsumer.liftSelected (match input.material with
    | .hidden nonce => selected writer nonce input.sequence input.context
    | .known material => (fun result => (.completed result.1, result.2)) <$>
        known c writer ⟨material, input.sequence, input.context⟩)

/-- Forgetting only the produced frame restores the exact existing selected callback, including nonce refusal and invalid AD. -/
theorem selected_forget (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) :
    Prod.fst <$> selected writer nonce sequence context =
      RawCtxSelectedMessageSealing.selected writer nonce sequence context := by
  unfold selected RawCtxSelectedMessageSealing.selected
  split <;> simp only [map_bind, map_pure]
  congr 1
  funext reply
  cases reply <;> rfl

/-- The known branch adds only a returned log; it introduces no extra primitive request. -/
theorem known_forget (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    Prod.fst <$> known c writer input = RawCtxSelectedMessageSealing.known c writer input := by
  simp only [known, RawCtxSelectedMessageSealing.known, ← simulateQ_map, typed_forget]

/-- Logging changes neither the existing callback reply nor its oracle query tree. -/
theorem call_forget (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    Prod.fst <$> call c writer input = RawCtxSelectedSealConsumer.call c writer input := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
      simpa only [call, RawCtxSelectedSealConsumer.call, ← simulateQ_map] using
        congrArg (simulateQ RawCtxSelectedSealConsumer.liftSelected)
          (selected_forget writer nonce sequence context)
  | known material =>
      simpa only [call, RawCtxSelectedSealConsumer.call, simulateQ_map, Functor.map_map] using
        congrArg (fun work => simulateQ RawCtxSelectedSealConsumer.liftSelected (SealResult.completed <$> work))
          (known_forget c writer ⟨material, sequence, context⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A fresh selected seal retains the actual challenger-produced frame and complete canonical/dynamic history, even if the writer fails. -/
theorem selected_fresh (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (fresh : nonce ∉ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode c key)
      (call c writer ⟨.hidden nonce, sequence, context⟩)).run before = (do
      let result ← (simulateQ ctxRandomOracle (ctxSeal c key (selectedInput nonce sequence context width))).run before.cache
      let frame : Frame := ⟨sequence, context.senderId, result.1.encode⟩
      pure ((SealResult.completed (writer frame), [frame]),
        RawCtxSelectedSealConsumer.install before
          (RawCtxSharedSourceOpening.retain (before.selected, before.cache)
            (afterSeal (canonicalProjection (before.selected, before.cache))
              (selectedInput nonce sequence context width) result.1 result.2)))) := by
  simp only [call]
  rw [RawCtxSelectedSealConsumer.lifted_complete, RawCtxSelectedSealConsumer.canonical_complete]
  simp only [selected, dite_eq_left width, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  dsimp only [AdaptiveCtxCanonical.canonicalImpl, StateT.run]
  rw [RawCtxSelectedMessageSealing.canonical_fresh c key
    (selectedInput nonce sequence context width) _ fresh]
  simp only [bind_assoc, pure_bind, canonicalProjection, AdaptiveCtxSharedHash.install]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Selected nonce reuse produces an explicit stop and no frame while leaving every dynamic history and the shared cache unchanged. -/
theorem selected_repeat (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (used : nonce ∈ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode c key)
      (call c writer ⟨.hidden nonce, sequence, context⟩)).run before =
        pure ((SealResult.repeatedNonce, []), before) := by
  simp only [call]
  rw [RawCtxSelectedSealConsumer.lifted_complete, RawCtxSelectedSealConsumer.canonical_complete]
  simp only [selected, dite_eq_left width, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  dsimp only [AdaptiveCtxCanonical.canonicalImpl, StateT.run]
  simp [
    AdaptiveCtxCanonical.canonicalCtx, ctxAdversaryImpl, ctxSealOracle, selectedInput, used,
    StateT.run, AdaptiveCtxCanonical.sealPrivateInputs,
    RawCtxSelectedSealConsumer.install, RawCtxSharedSourceOpening.retain, canonicalProjection,
    AdaptiveCtxSharedHash.install, AdaptiveCtxSharedHash.separate]

/-- Known-material sealing keeps the complete source writer, produced frame, shared cache and all dynamic histories, even when its bytes alias the selected key. -/
theorem known_complete (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (material : RatchetMaterial) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (before : SourceState) :
    (simulateQ (sourceImpl real decode c key)
      (call c writer ⟨.known material, sequence, context⟩)).run before =
      (fun result => ((SealResult.completed result.1.1, result.1.2),
        RawCtxSelectedSealConsumer.install before
          (AdaptiveCtxSharedModes.replaceShared (before.selected, before.cache) result.2))) <$>
        (simulateQ AdaptiveCtxSharedTarget.sharedImpl (simulateQ hashLift
          (typed c writer ⟨material, sequence, context⟩))).run
          (before.cache, before.selected.1.publicInputs) := by
  simp only [call]
  rw [RawCtxSelectedSealConsumer.lifted_complete]
  simp only [simulateQ_map, StateT.run_map, known]
  rw [AdaptiveCtxSharedModes.forward_complete]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Projecting only analysis histories recovers the exact known-key computation, retaining its produced frame and entire shared cache. -/
theorem known_cache (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (material : RatchetMaterial) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (before : SourceState) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl real decode c key)
        (call c writer ⟨.known material, sequence, context⟩)).run before =
      (fun result => ((SealResult.completed result.1.1, result.1.2), result.2)) <$>
        (simulateQ ctxRandomOracle (typed c writer ⟨material, sequence, context⟩)).run before.cache := by
  rw [known_complete, ← hash_interpretation]
  have same := congrArg (fun work => (fun result =>
      ((SealResult.completed result.1.1, result.1.2), result.2)) <$> work)
    (AdaptiveCtxSharedTarget.cache_schedule
      (simulateQ hashLift (typed c writer ⟨material, sequence, context⟩))
      (before.cache, before.selected.1.publicInputs))
  simpa only [Functor.map_map, Prod.map_def, id_eq, RawCtxSelectedSealConsumer.install,
    AdaptiveCtxSharedModes.replaceShared] using same

/-- Before the explicit selected-nonce stop, the source seal, optional writer result, produced frame and complete shared cache are identical. -/
theorem selected_cache (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (fresh : nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl true decode c key)
        (call c writer ⟨.hidden nonce, sequence, context⟩)).run before =
      (fun result => ((SealResult.completed result.1.1, result.1.2), result.2)) <$>
        (simulateQ ctxRandomOracle
          (typed c writer (selectedNative key nonce sequence context))).run before.cache := by
  rw [selected_fresh decode c key writer nonce sequence context width before fresh]
  have inputWidth : (selectedNative key nonce sequence context).context.associatedData.length = 281 := width
  rw [typed, dite_eq_left inputWidth, (selected_input key nonce sequence context width).1,
    (selected_input key nonce sequence context width).2]
  simp only [simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  simp only [afterSeal, CtxHandlerState.addSeal, RawCtxCanonicalSeal.recordFrame,
    RawCtxSelectedSealConsumer.install, RawCtxSharedSourceOpening.retain, AdaptiveCtxSharedHash.separate]
  rfl

/-- All source inputs retain the produced frame and cache. Freshness is required only for a selected valid-AD sealing call; known keys and invalid AD keep their original behavior. -/
theorem call_cache (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (before : SourceState)
    (fresh : ∀ nonce, input.material = .hidden nonce → input.context.associatedData.length = 281 →
      nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl true decode c key) (call c writer input)).run before =
      (fun result => ((SealResult.completed result.1.1, result.1.2), result.2)) <$>
        (simulateQ ctxRandomOracle (typed c writer (RawCtxInterpretedArguments.toSealInput
          (RawCtxInterpretedArguments.mapInput (interpret key) input)))).run before.cache := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | known material => exact known_cache true decode c key writer material sequence context before
  | hidden nonce =>
      by_cases width : context.associatedData.length = 281
      · exact selected_cache decode c key writer nonce sequence context width before (fresh nonce rfl width)
      · simp [call, selected, typed, RawCtxInterpretedArguments.toSealInput,
          RawCtxInterpretedArguments.mapInput, width, StateT.run_pure]

/-- The interpreted selected/known callback equals the actual logged native seal, retaining arbitrary auxiliary state and the complete shared cache. It does not assert the required nonce invariant for the global world. -/
theorem native_source {Auxiliary : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : RootOutput) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (before : SourceState) (auxiliary : Auxiliary)
    (fresh : ∀ nonce, input.material = .hidden nonce → input.context.associatedData.length = 281 →
      nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, (auxiliary, result.2.cache))) <$>
      (simulateQ (sourceImpl true decode c key) (call c writer input)).run before =
      (fun result => ((SealResult.completed result.1.1, result.1.2), result.2)) <$>
        (simulateQ (RawCtxMixedShared.sharedImpl c writer kdf)
          (native (RawCtxInterpretedArguments.toSealInput
            (RawCtxInterpretedArguments.mapInput (interpret key) input)))).run (auxiliary, before.cache) := by
  rw [native_complete]
  have same := congrArg (fun work => (fun result => (result.1, (auxiliary, result.2))) <$> work)
    (call_cache decode c key writer input before fresh)
  simpa only [Functor.map_map] using same

/-- Returning a produced-frame log does not change any oracle-query bound. Local AEAD/writer work and interpreter-internal hash sampling are not removed by this transport. -/
theorem call_bound (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (call c writer input).IsQueryBoundP predicate bound ↔
      (RawCtxSelectedSealConsumer.call c writer input).IsQueryBoundP predicate bound := by
  rw [← call_forget c writer input, isQueryBoundP_map_iff]

/-- Each selected seal attempt, including nonce refusal, uses at most one target seal query. A known seal uses at most one explicit shared hash query; neither route adds a raw verification or explicit uniform request. Interpreter-internal random draws remain in that interpreter's ledger. -/
theorem call_bills (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    (call c writer input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (match input.material with | .hidden _ => 0 | .known _ => 1) ∧
    (call c writer input).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (match input.material with | .hidden _ => 1 | .known _ => 0) ∧
    (call c writer input).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0 ∧
    (call c writer input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simp only [call_bound]
  exact ⟨RawCtxSelectedSealConsumer.call_hash c writer input,
    RawCtxSelectedSealConsumer.call_seal c writer input,
    RawCtxSelectedSealConsumer.call_other c writer input⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_invalid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.typed_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.typed_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_repeat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.known_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.selected_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.native_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFrameLog.call_bills
