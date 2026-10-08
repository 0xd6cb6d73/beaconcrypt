-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers
import BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld
import BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer

/-! Concrete labeled opening and sealing services retain the actual optional replies, shared commitment cache and attempted writer frames. The source counter erasure is explicit: the ordinary challenger never supplies secret-dependent primitive instrumentation to the simulator. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices
open PqxdhRecordLiftLoggedAdapters
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Original native operations without the separate World analysis counters. Their full shared cache is retained. -/
noncomputable def native (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) : Native CtxRomAuth.CtxRO.QueryCache :=
  fun query cache => Prod.map id Prod.snd <$>
    (PqxdhDeploymentNative.primitives setup codec query).run ((), cache)

/-- Every complete adaptive native program erases only the analysis counters; its reply and actual shared cache are unchanged. -/
theorem native_counts_erasure (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRecordLiftWorld.Primitive) :
    Prod.map id Prod.snd <$> (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) work).run state =
      (simulateQ (native setup codec) work).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (PqxdhRecordLiftWorld.primitives_forget setup codec) work state

/-- Only the private analysis counters are dropped; the actual writer frame list remains observable to the source publication layer. -/
def eraseCounts (state : PqxdhRecordLiftWorld.Primitive × Frames) : CtxRomAuth.CtxRO.QueryCache × Frames :=
  (state.1.2, state.2)

/-- Complete native logging commutes with counter erasure, including attempted frames whose writer returns None. -/
theorem logged_counts_erasure (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (state : PqxdhRecordLiftWorld.Primitive) (frames : Frames) :
    Prod.map id eraseCounts <$>
      (simulateQ (loggedNative (PqxdhRecordLiftWorld.primitives setup codec)) work).run (state, frames) =
      (simulateQ (loggedNative (native setup codec)) work).run (state.2, frames) := by
  rw [program_logged, program_logged, ← native_counts_erasure setup codec _ state]
  simp only [Functor.map_map, Prod.map_def, id_eq, swapResult, eraseCounts]

/-- Source sealing under its ordinary total AEAD and shared ROM, with the original attempted-frame log kept before the writer result. -/
def sealRom (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxSourceSeal.SealSpec (StateT Frames (OracleComp CtxRomAuth.CtxRO))
  | .inl input => pure (some (crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inl bytes) => StateT.lift (do
      let digest ← CtxRomAuth.CtxRO.query ((), bytes)
      pure (some digest.toList))
  | .inr (.inr frame) => fun frames => pure (writer frame, frames ++ [frame])

/-- The original inner source seal emits exactly its typed record, then logs and invokes the actual writer, even when it fails. -/
theorem sealRom_typed (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length = 153)
    (frames : Frames) :
    (simulateQ (sealRom crypto writer) (RawCtxSourceSeal.sealInput input)).run frames =
      (do
        let record ← CtxRomAuth.ctxSeal crypto (RawCtxCanonicalSeal.sourceKey input)
          (RawCtxCanonicalSeal.sourceInput input width)
        let frame := RawCtxCanonicalSeal.recordFrame input record
        pure (writer frame, frames ++ [frame])) := by
  simp [RawCtxSourceSeal.sealInput, sealRom, OracleSpec.query, RawCtxSourceSeal.aeadInput,
    width, crypto.aeadSeal_tag_length, CtxRomAuth.ctxSeal, RawCtxCanonicalSeal.sourceKey,
    RawCtxCanonicalSeal.sourceNonce, RawCtxCanonicalSeal.sourceInput, RawCtxCanonicalSeal.sourceContext,
    CtxRomAuth.outerInput, RawCtxSourceSeal.hashInput, RawCtxCanonicalSeal.recordFrame,
    CtxRomAuth.CtxRomRecord.encode, CtxRomAuth.CtxRomRecord.toRecordCipher,
    Pqxdh.RecordCipher.encode, RawCtxSourceSeal.frame]
  simp only [StateT.run, bind_pure_comp]

/-- Invalid source AD width returns ordinary failure and performs no writer call. -/
theorem sealRom_invalid (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length ≠ 153)
    (frames : Frames) :
    (simulateQ (sealRom crypto writer) (RawCtxSourceSeal.sealInput input)).run frames =
      pure (none, frames) := by
  simp [RawCtxSourceSeal.sealInput, sealRom, OracleSpec.query, width]

/-- Evaluate the source writer-log program on the same complete shared cache. -/
noncomputable def evaluateRom (work : StateT Frames (OracleComp CtxRomAuth.CtxRO) Result) :
    StateT (CtxRomAuth.CtxRO.QueryCache × Frames) ProbComp Result := fun state =>
  swapResult <$> (simulateQ CtxRomAuth.ctxRandomOracle (work.run state.2)).run state.1

/-- The actual existing send embeddings feed the native sealing, shared hash and writer operations. -/
noncomputable def nativeSeal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl RawCtxSourceSeal.SealSpec (StateT (CtxRomAuth.CtxRO.QueryCache × Frames) ProbComp) :=
  loggedNative (native setup codec) ∘ₛ (RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift)

/-- Each literal native source sealing effect retains the exact ROM and attempted-frame log under its source ROM presentation. -/
theorem nativeSeal_step (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : RawCtxSourceSeal.SealSpec.Domain) (state : CtxRomAuth.CtxRO.QueryCache × Frames) :
    (nativeSeal setup codec query).run state =
      (evaluateRom (sealRom setup.source.crypto codec.frameWrite query)).run state := by
  rcases query with input | (bytes | frame) <;>
    simp only [nativeSeal, QueryImpl.compose, RawCtxMixedOwner.sendLift, RawCtxSourceSeal.sealLift,
      simulateQ_spec_query, sealRom, bind_pure_comp]
  all_goals simp only [StateT.run]
  all_goals simp only [loggedNative, evaluateRom]
  all_goals simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, StateT.run_pure,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, simulateQ_pure, StateT.run_map,
    Functor.map_map]
  case inl =>
    simp only [StateT.run]
    simp only [native, PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_sealing,
      map_pure]
    rfl
  case inr.inl =>
    simp only [StateT.run]
    simp only [native, PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_hash,
      bind_pure_comp, Functor.map_map]
    rfl
  case inr.inr =>
    simp only [StateT.run, simulateQ_map, simulateQ_spec_query, simulateQ_pure]
    change swapResult <$> (((fun reply => (reply, state.2 ++ [frame])) <$>
      native setup codec (.inr (.inr (.inr (.inr frame))))).run state.1) =
      swapResult <$> ((pure (codec.frameWrite frame, state.2 ++ [frame]) :
        StateT CtxRomAuth.CtxRO.QueryCache ProbComp _).run state.1)
    rw [StateT.run_map, StateT.run_pure]
    simp only [StateT.run]
    simp only [native, PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_writing,
      map_pure]
    rfl

/-- Evaluating shared ROM programs preserves the complete adaptive continuation and attempted writer log. -/
theorem evaluateRom_bind {Next : Type}
    (work : StateT Frames (OracleComp CtxRomAuth.CtxRO) Result)
    (next : Result → StateT Frames (OracleComp CtxRomAuth.CtxRO) Next)
    (state : CtxRomAuth.CtxRO.QueryCache × Frames) :
    (evaluateRom (work >>= next)).run state = (do
      let result ← (evaluateRom work).run state
      (evaluateRom (next result.1)).run result.2) := by
  change swapResult <$> (simulateQ CtxRomAuth.ctxRandomOracle ((work >>= next).run state.2)).run state.1 = _
  simp only [StateT.run_bind, simulateQ_bind, map_bind]
  change _ = ((swapResult <$> (simulateQ CtxRomAuth.ctxRandomOracle (work.run state.2)).run state.1) >>=
    fun result => swapResult <$> (simulateQ CtxRomAuth.ctxRandomOracle ((next result.1).run result.2.2)).run result.2.1)
  rw [bind_map_left]
  rfl

/-- Every adaptive source sealing program has the exact shared cache, attempted frames and optional reply of its native execution. -/
theorem nativeSeal_program (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxSourceSeal.SealSpec Result) (state : CtxRomAuth.CtxRO.QueryCache × Frames) :
    (simulateQ (nativeSeal setup codec) work).run state =
      (evaluateRom (simulateQ (sealRom setup.source.crypto codec.frameWrite) work)).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [simulateQ_pure]
      change pure (result, state) = swapResult <$>
        (simulateQ CtxRomAuth.ctxRandomOracle (pure (result, state.2))).run state.1
      simp [swapResult]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evaluateRom_bind]
      rw [nativeSeal_step]
      apply bind_congr
      intro reply
      exact ih reply.1 reply.2

/-- The actual native inner seal preserves its full cache and attempted frame before any optional writer result. -/
theorem nativeSeal_typed (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length = 153)
    (state : CtxRomAuth.CtxRO.QueryCache × Frames) :
    (simulateQ (nativeSeal setup codec) (RawCtxSourceSeal.sealInput input)).run state = (do
      let result ← (simulateQ CtxRomAuth.ctxRandomOracle
        (CtxRomAuth.ctxSeal setup.source.crypto (RawCtxCanonicalSeal.sourceKey input)
          (RawCtxCanonicalSeal.sourceInput input width))).run state.1
      let frame := RawCtxCanonicalSeal.recordFrame input result.1
      pure (codec.frameWrite frame, (result.2, state.2 ++ [frame]))) := by
  rw [nativeSeal_program]
  change swapResult <$> (simulateQ CtxRomAuth.ctxRandomOracle
    ((simulateQ (sealRom setup.source.crypto codec.frameWrite) (RawCtxSourceSeal.sealInput input)).run state.2)).run state.1 = _
  rw [sealRom_typed _ _ _ width]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rfl

open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftProjectionCut
variable {Slot : Type} [DecidableEq Slot]

/-- Routing uses the retained structural coordinate and nonce, without access to the selected key. Known coordinates retain their actual possibly aliased bytes. -/
noncomputable def materialRoute (masked : Mask Slot) (coordinate : Coordinate Slot) :
    RawCtxSelectedMessageKey.Slot :=
  if coordinate = masked.coordinate then .hidden masked.value.2
  else .known (PqxdhRecordLiftMaterialTable.material masked.before coordinate)

/-- Interpreting the one unavailable key recovers the exact material of the complete cached realization. -/
theorem materialRoute_real (masked : Mask Slot) (key : PqxdhSecretInputKdf.RootOutput)
    (coordinate : Coordinate Slot) :
    RawCtxSelectedMessageKey.interpret key (materialRoute masked coordinate) =
      PqxdhRecordLiftMaterialTable.material (realize .key masked key).2.1 coordinate := by
  rw [PqxdhRecordLiftMaskedReads.material_key_read]
  by_cases same : coordinate = masked.coordinate <;>
    simp [materialRoute, same, RawCtxSelectedMessageKey.interpret]

/-- Source chain inputs retain the selected reply's next-chain projection, which does not contain its selected message key. -/
noncomputable def chainRoute (seeds : Seeds Slot) (masked : Mask Slot) (coordinate : Coordinate Slot) : RatchetChain :=
  if PqxdhRecordLiftMaskedReads.Reads coordinate masked.coordinate then
    RawCtxFreshChainCut.concreteChain masked.value.1
  else PqxdhRecordLiftChainTable.chain seeds masked.before coordinate

/-- Every source chain read has the exact key-free routing formula, even when coordinate bytes alias. -/
theorem chainRoute_real (seeds : Seeds Slot) (masked : Mask Slot) (key : PqxdhSecretInputKdf.RootOutput)
    (coordinate : Coordinate Slot) :
    chainRoute seeds masked coordinate =
      PqxdhRecordLiftChainTable.chain seeds (realize .key masked key).2.1 coordinate :=
  (PqxdhRecordLiftMaskedReads.chain_key_read masked key seeds coordinate).symm

/-- The private opening keeps the complete source pending object with key-free chain and material routing. -/
noncomputable def openingRoute (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RawCtxSelectedMessageKey.Slot RawCtxWholeOwner.OpenContext :=
  RawCtxInterpretedOpening.mapOpening (materialRoute masked)
    (RawCtxChainInterpretation.mapOpeningChains (chainRoute seeds masked) (chainRoute seeds masked) pending)

/-- Routing preserves the actual cached/target getters, including absent and mistagged material. -/
theorem openingRoute_getters (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedOpening.sequence (openingRoute seeds masked pending) = RawCtxInterpretedOpening.sequence pending ∧
      RawCtxInterpretedOpening.material (openingRoute seeds masked pending) =
        RawCtxMaterialInterpretation.mapOption (materialRoute masked) <$> RawCtxInterpretedOpening.material pending := by
  simp only [openingRoute, RawCtxInterpretedOpening.sequence_map, RawCtxInterpretedOpening.material_map,
    RawCtxChainInterpretation.opening_sequence_chains, RawCtxChainInterpretation.opening_material_chains, and_self]

/-- Interpreting the selected key supplies exactly the original source opening callback, including its entire native state and optional reply. -/
theorem openingRoute_native {P : Type} (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P)
    (seeds : Seeds Slot) (masked : Mask Slot) (key : PqxdhSecretInputKdf.RootOutput)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    PqxdhRecordLiftNativeAdapters.receiveOpen native
      (RawCtxInterpretedOpening.mapOpening (RawCtxSelectedMessageKey.interpret key) (openingRoute seeds masked pending)) =
    PqxdhRecordLiftNativeAdapters.receiveOpen native
      (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .key masked key).2.1 pending) := by
  apply PqxdhRecordLiftMaskedReads.receive_open_reads
  · rw [RawCtxInterpretedOpening.sequence_map, (openingRoute_getters seeds masked pending).1,
      (PqxdhRecordLiftMaterialTable.opening_getters seeds _ pending).1]
  · rw [RawCtxInterpretedOpening.material_map, (openingRoute_getters seeds masked pending).2,
      (PqxdhRecordLiftMaterialTable.opening_getters seeds _ pending).2, Functor.map_map]
    congr 1
    funext result
    cases result <;> simp [RawCtxMaterialInterpretation.mapOption, materialRoute_real]
  · rfl

open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
open RawCtxSelectedMessageSealing

/-- Known-key local sealing forwards the exact commitment input to the ordinary challenger's existing public ROM. -/
noncomputable def publicRom : QueryImpl CtxRO (OracleComp Spec) :=
  RawCtxSelectedSealConsumer.liftSelected ∘ₛ (AdaptiveCtxSharedTarget.forward ∘ₛ hashLift)

/-- Forwarded local work preserves the entire dynamic component state, including all unrelated histories. -/
theorem publicRom_complete (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp CtxRO Result) (before : SourceState) :
    (simulateQ (sourceImpl real decode crypto key) (simulateQ publicRom work)).run before =
      (fun result => (result.1, RawCtxSelectedSealConsumer.install before
        (replaceShared (before.selected, before.cache) result.2))) <$>
        (simulateQ AdaptiveCtxSharedTarget.sharedImpl (simulateQ hashLift work)).run
          (before.cache, before.selected.1.publicInputs) := by
  simp only [publicRom, QueryImpl.simulateQ_compose]
  rw [RawCtxSelectedSealConsumer.lifted_complete, forward_complete]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Erasing only challenger histories leaves the identical source cache and result of every public ROM continuation. -/
theorem publicRom_cache (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp CtxRO Result) (before : SourceState) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl real decode crypto key) (simulateQ publicRom work)).run before =
      (simulateQ ctxRandomOracle work).run before.cache := by
  rw [publicRom_complete]
  have cached := AdaptiveCtxSharedTarget.cache_schedule (simulateQ hashLift work)
    (before.cache, before.selected.1.publicInputs)
  rw [hash_interpretation] at cached
  simpa only [Functor.map_map, RawCtxSelectedSealConsumer.install, replaceShared, Prod.map_def, id_eq] using cached

/-- Every produced inner record is logged before the optional source writer result, with the unchanged source sequence and sender. -/
def written (writer : RawCtxMixedShared.Writer) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (record : CtxRomRecord) (frames : Frames) : SealResult × Frames :=
  let frame : RawCtxReceive.DecodedFrame := ⟨sequence, context.senderId, record.encode⟩
  (.completed (writer frame), frames ++ [frame])

/-- Key-free ordinary CTX sealing. Nonce refusal is an explicit stop; writer failure remains an ordinary completed None and still logs the attempted frame. -/
noncomputable def sealCall (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext) :
    StateT Frames (OracleComp Spec) SealResult := fun frames =>
  if width : input.context.associatedData.length = 153 then
    match input.material with
    | .hidden nonce => simulateQ RawCtxSelectedSealConsumer.liftSelected (do
        let reply ← ReceiveSpec.query (.inl (.inr (.inr (selectedInput nonce input.sequence input.context width))))
        pure (match reply with
          | none => (.repeatedNonce, frames)
          | some record => written writer input.sequence input.context record frames))
    | .known material => simulateQ publicRom
        ((fun record => written writer input.sequence input.context record frames) <$>
          ctxSeal crypto (RawCtxCanonicalSeal.sourceKey ⟨material, input.sequence, input.context⟩)
            (RawCtxCanonicalSeal.sourceInput ⟨material, input.sequence, input.context⟩ width))
  else pure (.completed none, frames)

/-- Invalid AD gives the literal no-writer source failure and no component query. -/
theorem sealCall_invalid (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (width : input.context.associatedData.length ≠ 153) (frames : Frames) :
    (sealCall crypto writer input).run frames = pure (.completed none, frames) := by
  simp [sealCall, StateT.run, width]

/-- A known-key seal uses unchecked native sealing on its exact key and nonce, with the same cache and attempted frame even on writer failure. -/
theorem sealCall_known_cache (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (writer : RawCtxMixedShared.Writer) (material : RatchetMaterial) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 153)
    (before : SourceState) (frames : Frames) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl real decode crypto key)
        ((sealCall crypto writer ⟨.known material, sequence, context⟩).run frames)).run before =
      (fun result => (written writer sequence context result.1 frames, result.2)) <$>
        (simulateQ ctxRandomOracle
          (ctxSeal crypto (RawCtxCanonicalSeal.sourceKey ⟨material, sequence, context⟩)
            (RawCtxCanonicalSeal.sourceInput ⟨material, sequence, context⟩ width))).run before.cache := by
  change (fun result => (result.1, result.2.cache)) <$>
    (simulateQ (sourceImpl real decode crypto key) (sealCall crypto writer ⟨.known material, sequence, context⟩ frames)).run before = _
  simp only [sealCall, dite_eq_left width]
  rw [publicRom_cache, simulateQ_map, StateT.run_map]

/-- Before the explicit nonce stop, the selected ordinary seal retains every component history, actual source cache and attempted writer frame. -/
theorem sealCall_selected_fresh (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : PqxdhSecretInputKdf.RootOutput) (writer : RawCtxMixedShared.Writer)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 153)
    (before : SourceState) (frames : Frames) (fresh : nonce ∉ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode crypto key)
      ((sealCall crypto writer ⟨.hidden nonce, sequence, context⟩).run frames)).run before = (do
      let result ← (simulateQ ctxRandomOracle (ctxSeal crypto key (selectedInput nonce sequence context width))).run before.cache
      pure (written writer sequence context result.1 frames,
        RawCtxSelectedSealConsumer.install before (RawCtxSharedSourceOpening.retain (before.selected, before.cache)
          (afterSeal (canonicalProjection (before.selected, before.cache))
            (selectedInput nonce sequence context width) result.1 result.2)))) := by
  change (simulateQ (sourceImpl true decode crypto key)
    (sealCall crypto writer ⟨.hidden nonce, sequence, context⟩ frames)).run before = _
  simp only [sealCall, dite_eq_left width]
  rw [RawCtxSelectedSealConsumer.lifted_complete, RawCtxSelectedSealConsumer.canonical_complete]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  simp only [StateT.run, AdaptiveCtxCanonical.canonicalImpl]
  rw [canonical_fresh crypto key (selectedInput nonce sequence context width) _ fresh]
  simp only [bind_assoc, pure_bind, map_bind, map_pure, canonicalProjection]
  rfl

/-- A repeated selected nonce stops before writing, while preserving the complete component state and pending source frame log. -/
theorem sealCall_selected_repeat (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : PqxdhSecretInputKdf.RootOutput) (writer : RawCtxMixedShared.Writer)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 153)
    (before : SourceState) (frames : Frames) (used : nonce ∈ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode crypto key)
      ((sealCall crypto writer ⟨.hidden nonce, sequence, context⟩).run frames)).run before =
      pure ((.repeatedNonce, frames), before) := by
  change (simulateQ (sourceImpl true decode crypto key)
    (sealCall crypto writer ⟨.hidden nonce, sequence, context⟩ frames)).run before = _
  simp only [sealCall, dite_eq_left width]
  rw [RawCtxSelectedSealConsumer.lifted_complete, RawCtxSelectedSealConsumer.canonical_complete]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  simp [StateT.run, AdaptiveCtxCanonical.canonicalImpl, AdaptiveCtxCanonical.canonicalCtx,
    ctxAdversaryImpl, ctxSealOracle, selectedInput, used, canonicalProjection,
    AdaptiveCtxSharedHash.install, AdaptiveCtxCanonical.sealPrivateInputs,
    RawCtxSelectedSealConsumer.install, RawCtxSharedSourceOpening.retain, AdaptiveCtxSharedHash.separate]

/-- Receive-side native work never writes a frame; the complete arbitrary primitive state remains framed by the original pending log. -/
theorem receive_log_program {P : Type} (native : Native P)
    (work : OracleComp RawCtxSourceOpen.NativeSpec Result) (primitive : P) (frames : Frames) :
    (simulateQ (loggedNative native ∘ₛ RawCtxMixedOwner.receiveLift) work).run (primitive, frames) =
      (fun result => (result.1, (result.2, frames))) <$>
        (simulateQ (native ∘ₛ RawCtxMixedOwner.receiveLift) work).run primitive := by
  symm
  apply map_run_simulateQ_eq_of_query_map_eq (native ∘ₛ RawCtxMixedOwner.receiveLift)
    (loggedNative native ∘ₛ RawCtxMixedOwner.receiveLift) (fun state => (state, frames)) _ work primitive
  intro query state
  rcases query with request | (bytes | input) <;>
    simp only [QueryImpl.compose, RawCtxMixedOwner.receiveLift, simulateQ_spec_query]
  all_goals simp only [StateT.run]
  all_goals simp only [loggedNative]
  all_goals simp only [PqxdhDeploymentNative.frameLog, StateT.run_lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map, swapResult]
  all_goals rfl

/-- Removing only the Unit wrapper yields the exact native shared-cache execution for an arbitrary complete continuation. -/
theorem native_unit_erasure (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (cache : CtxRO.QueryCache) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhDeploymentNative.primitives setup codec) work).run ((), cache) =
      (simulateQ (native setup codec) work).run cache := by
  apply map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd _ work ((), cache)
  intro query state
  rcases state with ⟨⟨⟩, cache⟩
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The literal whole source opening callback retains the same pending log and every native state effect. -/
theorem receiveOpen_logged {P : Type} (native : Native P)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (primitive : P) (frames : Frames) :
    (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative (loggedNative native)) pending).run (primitive, frames) =
      (fun result => (result.1, (result.2, frames))) <$>
        (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative native) pending).run primitive := by
  simp only [PqxdhRecordLiftNativeAdapters.receiveOpen, receiveNative, RawCtxMixedOwner.receiveAdapter,
    QueryImpl.simulateQ_compose]
  simpa only [QueryImpl.simulateQ_compose] using receive_log_program
    (Result := core.option.Option RawCtxWholeOwner.Decrypted) native
    (simulateQ RawCtxSourceOpen.nativeAdapter (RawCtxWholeOwner.adapter
      (.inr (RawCtxInterpretedOpening.toNative pending)))) primitive frames

/-- The actual native opening uses the original total shared-ROM/perfect-AEAD source interpreter; only its Unit wrapper is removed. -/
theorem receiveOpen_native (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (cache : CtxRO.QueryCache) :
    (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative (native setup codec)) pending).run cache =
      Prod.map id Prod.snd <$>
        (simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source))
          (RawCtxSourceOpen.ownerAdapter (.inr (RawCtxInterpretedOpening.toNative pending)))).run ((), cache) := by
  simp only [PqxdhRecordLiftNativeAdapters.receiveOpen, receiveNative, RawCtxMixedOwner.receiveAdapter,
    QueryImpl.simulateQ_compose]
  rw [← native_unit_erasure]
  rw [← QueryImpl.simulateQ_compose]
  rw [PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_receive]
  rfl

/-- The selected raw service performs the source payload-parser rejection locally, then forwards the original raw bytes and actual total getters. It never supplies recovered plaintext as target data. -/
noncomputable def openingService (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    OracleComp Spec (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none => pure .None
  | some _ => RawCtxSelectedOpenConsumer.service slot read expected (openingRoute seeds masked pending)

/-- A malformed protected payload reaches no hash or AEAD operation in the actual source callback. -/
theorem native_opening_malformed {A : Type} (crypto : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (malformed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = none)
    (ambient : A) (cache : CtxRO.QueryCache) :
    (simulateQ (RawCtxSharedPrimitive.nativeImpl crypto kdf)
      (RawCtxSourceOpen.ownerAdapter (.inr pending))).run (ambient, cache) =
      pure (.None, (ambient, cache)) := by
  rw [RawCtxSelectedOpenConsumer.native_service]
  cases found : RawCtxWholeOwner.arguments pending with
  | none => rfl
  | some input =>
      have context := (RawCtxWholeOwner.arguments_some pending input found).2.2
      simp only [RawCtxSourceOpen.openInput, context, malformed, simulateQ_pure, StateT.run_pure, map_pure]
      rfl

/-- The actual raw parser/getter service uses at most one selected or known verification query per source opening attempt. -/
theorem openingService_total (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    (openingService slot read expected seeds masked pending).IsTotalQueryBound 1 := by
  unfold openingService
  split
  · trivial
  · exact RawCtxSelectedOpenConsumer.service_total slot read expected _

/-- Actual raw opening adds no selected seal or explicit random request; its internal verification/hash work is billed by the existing dynamic component. -/
theorem openingService_other (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    (openingService slot read expected seeds masked pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (openingService slot read expected seeds masked pending).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  unfold openingService
  split
  · exact ⟨by trivial, by trivial⟩
  · exact RawCtxSelectedOpenConsumer.service_other slot read expected _

/-- Every admitted raw opening, including a malformed payload or missing cached key, returns the actual challenger optional plaintext through the original source API and retains the complete cache and pending writer log. -/
theorem openingService_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat) (expected : Std.U64)
    (seeds : Seeds Slot) (masked : Mask Slot) (key : PqxdhSecretInputKdf.RootOutput)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext)
    (before : SourceState) (frames : Frames)
    (nonempty : pending.context.raw.isEmpty = false)
    (decoded : codec.frameRead pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence) :
    (PqxdhRecordLiftNativeAdapters.receiveOpen (receiveNative (loggedNative (native setup codec)))
      (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .key masked key).2.1 pending)).run (before.cache, frames) =
      (fun result => (result.1, (result.2.cache, frames))) <$>
        (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
          (openingService slot codec.frameRead expected seeds masked pending)).run before := by
  rw [← openingRoute_native _ seeds masked key pending, receiveOpen_logged, receiveOpen_native]
  cases parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none =>
      rw [native_opening_malformed _ _ _ parsed]
      simp only [openingService, parsed, simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | some slices =>
      have preparedRoute : RawCtxInterpretedOpening.sequence (openingRoute seeds masked pending) =
          ok pending.context.frame.sequence := (openingRoute_getters seeds masked pending).1.trans prepared
      rw [RawCtxSelectedOpenConsumer.service_source slot codec.frameRead expected key setup.source.crypto
        (RawCtxSourceHkdf.kdfImpl setup.source) (openingRoute seeds masked pending) () before
        nonempty decoded valid preparedRoute slices parsed]
      simp only [openingService, parsed, Functor.map_map, Prod.map_def, id_eq]

/-- Invalid AD retains the actual cache and pending frames in the native source seal. -/
theorem nativeSeal_invalid (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (input : RawCtxSourceSend.SealInput) (width : input.context.associatedData.length ≠ 153)
    (state : CtxRO.QueryCache × Frames) :
    (simulateQ (nativeSeal setup codec) (RawCtxSourceSeal.sealInput input)).run state = pure (none, state) := by
  rw [nativeSeal_program]
  change swapResult <$> (simulateQ ctxRandomOracle
    ((simulateQ (sealRom setup.source.crypto codec.frameWrite) (RawCtxSourceSeal.sealInput input)).run state.2)).run state.1 = _
  rw [sealRom_invalid _ _ _ width]
  simp [swapResult]

/-- Complete component-state projection keeps its actual result, cache and pending source frame buffer; histories alone are erased. -/
def sealProjection (result : (SealResult × Frames) × SourceState) : SealResult × (CtxRO.QueryCache × Frames) :=
  (result.1.1, (result.2.cache, result.1.2))

/-- Before the separately exposed selected nonce refusal, the key-free service equals the actual native seal with its original writer and full shared cache. Known key aliases carry no nonce premise. -/
theorem sealCall_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (decode : RawDecoder)
    (key : PqxdhSecretInputKdf.RootOutput)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (before : SourceState) (frames : Frames)
    (fresh : ∀ nonce, input.material = .hidden nonce → input.context.associatedData.length = 153 →
      nonce ∉ before.selected.1.usedNonces) :
    sealProjection <$>
      (simulateQ (sourceImpl true decode setup.source.crypto key)
        ((sealCall setup.source.crypto codec.frameWrite input).run frames)).run before =
      Prod.map SealResult.completed id <$>
        (simulateQ (nativeSeal setup codec)
          (RawCtxSourceSeal.sealInput (RawCtxInterpretedArguments.toSealInput
            (RawCtxInterpretedArguments.mapInput (RawCtxSelectedMessageKey.interpret key) input)))).run (before.cache, frames) := by
  by_cases width : input.context.associatedData.length = 153
  · rcases input with ⟨material, sequence, context⟩
    cases material with
    | hidden nonce =>
        rw [sealCall_selected_fresh decode setup.source.crypto key codec.frameWrite nonce sequence context width
          before frames (fresh nonce rfl width)]
        rw [nativeSeal_typed _ _ _ width]
        simp only [RawCtxInterpretedArguments.toSealInput, RawCtxInterpretedArguments.mapInput]
        have keyEq := (selected_input key nonce sequence context width).1
        have inputEq := (selected_input key nonce sequence context width).2
        unfold selectedNative at keyEq inputEq
        rw [keyEq, inputEq]
        simp only [map_bind, map_pure, sealProjection, written, RawCtxSelectedSealConsumer.install,
          RawCtxSharedSourceOpening.retain, AdaptiveCtxSharedHash.separate, afterSeal, Prod.map_def, id_eq]
        rfl
    | known material =>
        have cached := sealCall_known_cache true decode setup.source.crypto key codec.frameWrite
          material sequence context width before frames
        have projected := congrArg (fun work => swapResult <$> work) cached
        rw [nativeSeal_typed _ _ _ width]
        unfold sealProjection
        simpa only [Functor.map_map, sealProjection, swapResult, map_bind, map_pure, written,
          Prod.map_def, id_eq, RawCtxInterpretedArguments.toSealInput, RawCtxInterpretedArguments.mapInput,
          RawCtxSelectedMessageKey.interpret, RawCtxCanonicalSeal.recordFrame, bind_pure_comp] using projected
  · rw [sealCall_invalid _ _ _ width frames, simulateQ_pure, StateT.run_pure, nativeSeal_invalid _ _ _ width]
    simp only [map_pure, sealProjection, Prod.map_def, id_eq]

/-- Each reached seal makes at most one component request, including selected nonce refusal and known writer failure. -/
theorem sealCall_total (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (frames : Frames) : ((sealCall crypto writer input).run frames).IsTotalQueryBound 1 := by
  change (sealCall crypto writer input frames).IsTotalQueryBound 1
  unfold sealCall
  split
  · cases input.material <;>
      simp [publicRom, QueryImpl.compose, RawCtxSelectedSealConsumer.liftSelected,
        AdaptiveCtxSharedTarget.forward, hashLift, ctxSeal, IsTotalQueryBound]
  · trivial

/-- Known seals charge their one public hash; selected attempts charge one ordinary seal even when refused. These are separate actual routes. -/
theorem sealCall_bills (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (frames : Frames) :
    ((sealCall crypto writer input).run frames).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (match input.material with | .hidden _ => 0 | .known _ => 1) ∧
      ((sealCall crypto writer input).run frames).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
        (match input.material with | .hidden _ => 1 | .known _ => 0) := by
  change (sealCall crypto writer input frames).IsQueryBoundP _ _ ∧
    (sealCall crypto writer input frames).IsQueryBoundP _ _
  unfold sealCall
  split
  · cases input.material <;>
      simp [publicRom, QueryImpl.compose, RawCtxSelectedSealConsumer.liftSelected,
        AdaptiveCtxSharedTarget.forward, hashLift, ctxSeal, AdaptiveCtxDynamicKnownBounds.HashRoute,
        AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceHash, AdaptiveCtxQueryBounds.SourceSeal]
  · exact ⟨by trivial, by trivial⟩

/-- Sealing adds no verification attempt or explicit random-byte query. ROM miss sampling remains inside the ordinary component ledger. -/
theorem sealCall_other (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (frames : Frames) :
    ((sealCall crypto writer input).run frames).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0 ∧
      ((sealCall crypto writer input).run frames).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  change (sealCall crypto writer input frames).IsQueryBoundP _ _ ∧
    (sealCall crypto writer input frames).IsQueryBoundP _ _
  unfold sealCall
  split
  · cases input.material <;>
      simp [publicRom, QueryImpl.compose, RawCtxSelectedSealConsumer.liftSelected,
        AdaptiveCtxSharedTarget.forward, hashLift, ctxSeal, AdaptiveCtxDynamicKnownBounds.TargetClass,
        IsRawQuery, AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxQueryBounds.SourceUniform]
  · exact ⟨by trivial, by trivial⟩

/-- Exact API wrapping retains returned writer bytes and source target/sequence without using any key bytes. -/
def sealReply (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) :
    SealResult → Except Unit (Option RawCtxSourceSend.Encrypted)
  | .repeatedNonce => .error ()
  | .completed reply => .ok (reply.map fun ciphertext => ⟨ciphertext, context.targetId, sequence⟩)

/-- The original labeled sealing request is interpreted through the ordinary CTX service. Its sole extra outcome is the explicit outer nonce stop. -/
noncomputable def sealingService (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (masked : Mask Slot) (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext) :
    ExceptT Unit (StateT Frames (OracleComp Spec)) (Option RawCtxSourceSend.Encrypted) :=
  ExceptT.mk (sealReply pending.sequence pending.context <$>
    sealCall crypto writer ⟨materialRoute masked pending.material, pending.sequence, pending.context⟩)

/-- Full callback projection retains the original reply, actual shared cache and pending writer frames. -/
def callbackProjection {Reply : Type} (result : (Reply × Frames) × SourceState) : Reply × (CtxRO.QueryCache × Frames) :=
  (result.1.1, (result.2.cache, result.1.2))

/-- The literal native sealing callback only adds the original optional API metadata to the complete inner seal execution. -/
theorem sendSeal_inner (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext)
    (state : CtxRO.QueryCache × Frames) :
    (PqxdhRecordLiftNativeAdapters.sendSeal (sendNative (loggedNative (native setup codec))) pending).run state =
      Prod.map (Option.map (RawCtxSourceSend.encrypted
        (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending)))) id <$>
        (simulateQ (nativeSeal setup codec) (RawCtxSourceSeal.sealInput
          (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending)))).run state := by
  rw [PqxdhRecordLiftNativeAdapters.send_seal_reply]
  simp only [sendNative, RawCtxMixedOwner.sendAdapter, QueryImpl.compose,
    RawCtxSourceSeal.nativeAdapter, bind_pure_comp]
  simp only [StateT.run_map, nativeSeal, QueryImpl.simulateQ_compose]
  rfl

/-- The labeled sealing callback is the literal native source API before the explicit nonce stop, with actual writer failure, cache effects and attempted frames all retained. -/
theorem sealingService_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (decode : RawDecoder)
    (seeds : Seeds Slot) (masked : Mask Slot) (key : PqxdhSecretInputKdf.RootOutput)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext)
    (before : SourceState) (frames : Frames)
    (fresh : ∀ nonce, materialRoute masked pending.material = .hidden nonce →
      pending.context.associatedData.length = 153 → nonce ∉ before.selected.1.usedNonces) :
    callbackProjection <$>
      (simulateQ (sourceImpl true decode setup.source.crypto key)
        ((sealingService setup.source.crypto codec.frameWrite masked pending).run.run frames)).run before =
      Prod.map (Except.ok (ε := Unit)) id <$>
        (PqxdhRecordLiftNativeAdapters.sendSeal (sendNative (loggedNative (native setup codec)))
          (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .key masked key).2.1 pending)).run (before.cache, frames) := by
  let input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext :=
    ⟨materialRoute masked pending.material, pending.sequence, pending.context⟩
  have inputEq : RawCtxInterpretedArguments.toSealInput
      (RawCtxInterpretedArguments.mapInput (RawCtxSelectedMessageKey.interpret key) input) =
      RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal
        (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .key masked key).2.1 pending)) := by
    simp only [input, RawCtxInterpretedArguments.toSealInput, RawCtxInterpretedArguments.mapInput,
      RawCtxSourceSend.arguments, RawCtxInterpretedSend.nativeSeal, PqxdhRecordLiftMaterialTable.eraseSeal,
      RawCtxInterpretedSend.mapSeal, RawCtxChainSend.nativeSeal]
    rw [materialRoute_real]
  have core := sealCall_source setup codec decode key input before frames fresh
  have wrapped := congrArg (fun work => Prod.map (sealReply pending.sequence pending.context) id <$> work) core
  rw [inputEq] at wrapped
  rw [sendSeal_inner]
  unfold RawCtxSourceSend.encrypted
  simp only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, simulateQ_map, StateT.run_map]
  simpa only [Functor.map_map, Prod.map_def, id_eq, sealProjection, callbackProjection, sealReply,
    input, RawCtxSourceSend.encrypted, RawCtxSourceSend.arguments, RawCtxInterpretedSend.nativeSeal,
    PqxdhRecordLiftMaterialTable.eraseSeal, RawCtxInterpretedSend.mapSeal, RawCtxChainSend.nativeSeal] using wrapped

/-- Selected verification and known-key forwarded hashing each cost at most one request for an actual raw opening. -/
theorem openingService_routes (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (seeds : Seeds Slot) (masked : Mask Slot)
    (pending : PqxdhRecordLiftOpaqueDrivers.LabeledOpening Slot RawCtxWholeOwner.OpenContext) :
    (openingService slot read expected seeds masked pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 1 ∧
      (openingService slot read expected seeds masked pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 :=
  ⟨(openingService_total slot read expected seeds masked pending).isQueryBoundP,
    (openingService_total slot read expected seeds masked pending).isQueryBoundP⟩

/-- API wrapping and explicit stopping introduce no extra query beyond the exact reached seal. -/
theorem sealingService_total (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (masked : Mask Slot) (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext)
    (frames : Frames) : ((sealingService crypto writer masked pending).run.run frames).IsTotalQueryBound 1 := by
  simpa only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, IsTotalQueryBound,
    isQueryBound_map_iff] using sealCall_total crypto writer
      ⟨materialRoute masked pending.material, pending.sequence, pending.context⟩ frames

/-- The labeled source callback retains the actual public-hash and selected-seal budgets; repeated selected nonces remain counted. -/
theorem sealingService_bills (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (masked : Mask Slot) (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext)
    (frames : Frames) :
    ((sealingService crypto writer masked pending).run.run frames).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (match materialRoute masked pending.material with | .hidden _ => 0 | .known _ => 1) ∧
      ((sealingService crypto writer masked pending).run.run frames).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
        (match materialRoute masked pending.material with | .hidden _ => 1 | .known _ => 0) := by
  simpa only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, isQueryBoundP_map_iff] using
    sealCall_bills crypto writer ⟨materialRoute masked pending.material, pending.sequence, pending.context⟩ frames

/-- The final source sealing callback adds no selected verification or explicit uniform query. -/
theorem sealingService_other (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (masked : Mask Slot) (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext)
    (frames : Frames) :
    ((sealingService crypto writer masked pending).run.run frames).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0 ∧
      ((sealingService crypto writer masked pending).run.run frames).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simpa only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, isQueryBoundP_map_iff] using
    sealCall_other crypto writer ⟨materialRoute masked pending.material, pending.sequence, pending.context⟩ frames

/-- Nonce refusal remains an explicit outer stop at the source service boundary and writes no frame. -/
theorem sealingService_repeat (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (decode : RawDecoder) (key : PqxdhSecretInputKdf.RootOutput)
    (masked : Mask Slot) (pending : PqxdhRecordLiftOpaqueDrivers.LabeledSeal Slot RawCtxSourceSend.SealContext)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (selected : materialRoute masked pending.material = .hidden nonce)
    (width : pending.context.associatedData.length = 153) (before : SourceState) (frames : Frames)
    (used : nonce ∈ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode crypto key)
      ((sealingService crypto writer masked pending).run.run frames)).run before =
      pure ((Except.error (), frames), before) := by
  simp only [sealingService, ExceptT.run, ExceptT.mk, StateT.run_map, selected, simulateQ_map, StateT.run_map]
  rw [sealCall_selected_repeat decode crypto key writer nonce pending.sequence pending.context width before frames used]
  simp only [map_pure, sealReply]

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_counts_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_counts_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.logged_counts_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.logged_counts_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealRom_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealRom_typed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealRom_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealRom_invalid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.evaluateRom_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.evaluateRom_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_typed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.materialRoute_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.materialRoute_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.chainRoute_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.chainRoute_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingRoute_getters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingRoute_getters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingRoute_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingRoute_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.publicRom_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.publicRom_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.publicRom_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.publicRom_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_invalid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_known_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_known_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_selected_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_selected_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_selected_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_selected_repeat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receive_log_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receive_log_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_unit_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_unit_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receiveOpen_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receiveOpen_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receiveOpen_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.receiveOpen_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_opening_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.native_opening_malformed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.nativeSeal_invalid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealCall_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sendSeal_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sendSeal_inner

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_routes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.openingService_routes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxServices.sealingService_repeat
