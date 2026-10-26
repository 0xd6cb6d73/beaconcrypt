import BeaconcryptCore.Computational.RawCtxUniversalOpening
import BeaconcryptCore.Computational.RawCtxOpeningOccurrence

/-!
The selected raw opening is exposed as the scalar optional reply expected by the complete source driver. Actual total getters decide whether a callback is reached; the driver remains responsible for its one original finish. Source comparison preserves the shared cache and actual optional plaintext before publication, and uses the original raw/prepared context rather than a recovered plaintext or a fixed-owner assumption.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer
open PqxdhSecretInputKdf RawCtxSelectedMessageKey
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes
open RawCtxSelectedMessageOpening hiding call call_source
open RawCtxInterpretedArguments

/-- Forgetting only component bookkeeping retains the exact source opening reply and the complete shared commitment cache. -/
theorem call_cache (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (input : Input Slot RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : input.context.raw.isEmpty = false) (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (sequenceMatches : input.sequence = input.context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
        (RawCtxUniversalOpening.call slot read expected input)).run state =
      (simulateQ ctxRandomOracle (simulateQ (RawCtxSourceOpen.romAdapter c)
        (RawCtxSourceOpen.openInput (toOpenInput (mapInput (interpret key) input))))).run state.cache := by
  rw [RawCtxUniversalOpening.call_source slot read expected key input c state nonempty decoded valid sequenceMatches slices parsed]
  simp only [Functor.map_map]
  cases material : input.material <;>
    simpa only [retain, entry, material, RawCtxSharedSourceOpening.retain, AdaptiveCtxSharedHash.separate,
      canonicalProjection, AdaptiveCtxSharedHash.install] using
      RawCtxCanonicalOpening.sourceOpening_cache_projection c (toOpenInput (mapInput (interpret key) input))
        (RawCtxCanonicalOpening.selectedTarget (toOpenInput (mapInput (interpret key) input)) slices parsed valid.2.2)
        (canonicalProjection (entry slot input.material state))

/-- A present opaque material comes from the actual total source getters, retaining the prepared sequence and immutable context. -/
theorem arguments_some
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (input : Input Slot RawCtxWholeOwner.OpenContext) (present : openArguments pending = some input) :
    RawCtxInterpretedOpening.material pending = ok (.Some input.material) ∧
      RawCtxInterpretedOpening.sequence pending = ok input.sequence ∧ input.context = pending.context := by
  unfold openArguments at present
  split at present
  · cases present
  · cases Option.some.inj present
    exact ⟨by simpa only [‹(material_total pending).choose = _›] using (material_total pending).choose_spec,
      (sequence_total pending).choose_spec, rfl⟩

noncomputable def service (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (core.option.Option RawCtxWholeOwner.Decrypted) :=
  match openArguments pending with
  | none => pure .None
  | some input => RawCtxSharedOpeningConsumer.apiReply input.sequence input.context <$>
      RawCtxUniversalOpening.call slot read expected input

set_option backward.isDefEq.respectTransparency false in
/-- The literal native owner adapter performs only the reached opening on the same shared cache and retains all unrelated primitive state. -/
theorem native_service {A : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) (ambient : A) (cache : CtxRO.QueryCache) :
    (simulateQ (RawCtxSharedPrimitive.nativeImpl c kdf)
      (RawCtxSourceOpen.ownerAdapter (.inr pending))).run (ambient, cache) =
      match RawCtxWholeOwner.arguments pending with
      | none => pure (.None, (ambient, cache))
      | some input => (fun result =>
          (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context result.1, (ambient, result.2))) <$>
          (simulateQ ctxRandomOracle (simulateQ (RawCtxSourceOpen.romAdapter c)
            (RawCtxSourceOpen.openInput input))).run cache := by
  simp only [RawCtxSourceOpen.ownerAdapter, QueryImpl.compose]
  cases found : RawCtxWholeOwner.arguments pending with
  | none => simp only [RawCtxWholeOwner.adapter, found, simulateQ_pure, StateT.run_pure]
  | some input =>
    rw [RawCtxWholeOwner.adapter_present pending input found]
    simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      RawCtxSourceOpen.nativeAdapter, StateT.run_map]
    rw [RawCtxSharedPrimitive.native_opening_complete]
    simp only [Functor.map_map]
    congr 1
    funext result
    cases result.1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar selected/known service is the literal native source callback on its reached context, preserving the original optional API plaintext and complete source cache before the driver's single finish. -/
theorem service_source {A : Type} (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (simulateQ (RawCtxSharedPrimitive.nativeImpl c kdf)
      (RawCtxSourceOpen.ownerAdapter (.inr (RawCtxInterpretedOpening.toNative
        (RawCtxInterpretedOpening.mapOpening (interpret key) pending))))).run (ambient, state.cache) =
      (fun result => (result.1, (ambient, result.2.cache))) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
          (service slot read expected pending)).run state := by
  rw [native_service, openArguments_native, openArguments_map]
  cases found : openArguments pending with
  | none =>
    simp only [service, found, Option.map_none, simulateQ_pure, StateT.run_pure, map_pure]
  | some input =>
    obtain ⟨_, sequence, context⟩ := arguments_some pending input found
    have sequenceMatches : input.sequence = input.context.frame.sequence := by
      rw [context]
      exact RustM.ok.inj (sequence.symm.trans prepared)
    have exactCall := call_cache slot read expected key input c state
      (by simpa only [context] using nonempty) (by simpa only [context] using decoded)
      (by simpa only [context] using valid) sequenceMatches slices (by simpa only [context] using parsed)
    have mapped := congrArg (fun work => (fun result =>
      (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context result.1, (ambient, result.2))) <$> work) exactCall
    simpa only [service, found, Option.map_some, simulateQ_map, StateT.run_map, Functor.map_map,
      mapInput, toOpenInput] using mapped.symm

/-- Missing or stale material is the actual source no-opening branch and makes no component query. -/
theorem service_missing (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (missing : openArguments pending = none) : service slot read expected pending = pure .None := by
  simp only [service, missing]

/-- Every reached native capability makes at most one actual dynamic component query, including missing material and invalid selected AD. -/
theorem service_total (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :
    (service slot read expected pending).IsTotalQueryBound 1 := by
  unfold service
  split
  · trivial
  · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using RawCtxUniversalOpening.call_bound slot read expected _

set_option backward.isDefEq.respectTransparency false in
/-- The scalar opening adds no sealing or direct uniform request; actual selected/known verification and internal shared-hash work keep their separate component bills. -/
theorem service_other (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :
    (service slot read expected pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (service slot read expected pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  unfold service
  split
  · exact ⟨by trivial, by trivial⟩
  · rename_i input found
    cases material : input.material <;>
      simp only [isQueryBoundP_map_iff, RawCtxUniversalOpening.call, material]
    · split <;> simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxDynamicKnownBounds.UniformRoute,
        AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxQueryBounds.SourceUniform]
    · simp [RawCtxSelectedMessageOpening.call, AdaptiveCtxDynamicKnownBounds.TargetClass,
        AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxQueryBounds.SourceUniform]

end BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.call_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.call_cache
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.arguments_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.arguments_some
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.native_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.native_service
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_missing
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_total
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer.service_other
