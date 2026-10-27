import BeaconcryptCore.Computational.RawCtxSelectedMessageKey
import BeaconcryptCore.Computational.RawCtxSharedSourceOpening
import BeaconcryptCore.Computational.RawCtxSharedOpeningConsumer
import BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds

/-!
The selected material marker is consumed at the native opening interface. The ordinary challenger receives only the original raw bytes; its key-free decoder carries the source nonce, sender pin and associated data. The mathematical native interpretation uses the same hidden message key. All cache and unused replay-dictionary state is retained, including failed commitment or AEAD outcomes.

These equalities require actual reached-frame and selected-context facts before the optional reply. They do not posit a recovered plaintext, independent source keys, reveal safety or a complete source schedule simulation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageOpening
open PqxdhFullSecretInputKdf PqxdhSecretInputKdf RawCtxSelectedMessageKey
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes
open BeaconcryptCore.Refinement.RepresentationBridge BeaconcryptCore.Refinement.ProtocolComposition PqxdhRefinement

def nativeInput (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) : RawCtxWholeOwner.OpenInput :=
  ⟨interpret key (.hidden nonce), sequence, context⟩

/-- The selected native material's first32 bytes are exactly the ordinary challenger key. -/
theorem selected_key (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    RawCtxSourceOpen.sourceKey (nativeInput key nonce sequence context) = key := by
  apply List.Vector.toList_injective
  simp [RawCtxSourceOpen.sourceKey, nativeInput, interpret, RawCtxFreshChainCut.concreteMaterial,
    absMaterial, absBytes, List.map_map, Function.comp_def]

/-- The selected native nonce remains the same final12 bytes; it is not resampled by the opening adapter. -/
theorem selected_nonce (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    RawCtxSourceOpen.sourceNonce (nativeInput key nonce sequence context) = nonce := by
  apply List.Vector.toList_injective
  simp [RawCtxSourceOpen.sourceNonce, nativeInput, interpret, RawCtxFreshChainCut.concreteMaterial,
    absMaterial, absBytes, List.map_map, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-- The selected raw challenger returns exactly the native optional plaintext on the same reached source frame and complete shared state. -/
theorem selected_open (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxSharedModes.State)
    (nonempty : context.raw.isEmpty = false)
    (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (sequenceMatches : sequence = context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (targetImpl true (RawCtxKeyFreeDecoder.decoder nonce expected context.associatedData read) c key
      (.inr context.raw)).run state =
      (fun result => (result.1, RawCtxSharedSourceOpening.retain state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c (nativeInput key nonce sequence context)
          (RawCtxCanonicalOpening.selectedTarget (nativeInput key nonce sequence context)
            slices parsed valid.2.2) (canonicalProjection state) := by
  rw [RawCtxSharedSourceOpening.real_complete]
  have exactDecoder := RawCtxKeyFreeDecoder.decoder_selected (nativeInput key nonce sequence context)
    slices parsed read expected nonempty decoded valid sequenceMatches
  simp only [selected_nonce] at exactDecoder
  have accepted : RawCtxKeyFreeDecoder.decoder nonce expected context.associatedData read context.raw =
      some (RawCtxCanonicalOpening.selectedTarget (nativeInput key nonce sequence context)
        slices parsed valid.2.2) := by
    rw [RawCtxKeyFreeDecoder.target_source, selected_nonce]
    exact exactDecoder
  have opening := RawCtxCanonicalOpening.sourceOpening_canonical c
    (nativeInput key nonce sequence context) slices parsed valid.2.2 _ (canonicalProjection state) accepted
  rw [selected_key] at opening
  exact congrArg (fun work =>
    (fun result => (result.1, RawCtxSharedSourceOpening.retain state result.2)) <$> work) opening.symm

/-- The private native source material is used locally only when it is known; a selected slot forwards the original raw bytes to the ordinary challenger. -/
noncomputable def call (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Pqxdh.Bytes) :=
  match input.material with
  | .hidden _ => AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr input.context.raw))
  | .known value =>
    let native : RawCtxWholeOwner.OpenInput := ⟨value, input.sequence, input.context⟩
    AdaptiveCtxDynamicKnownKeys.Spec.query (.inr ⟨slot, RawCtxSourceOpen.sourceKey native,
      RawCtxKeyFreeDecoder.decoder (RawCtxSourceOpen.sourceNonce native) expected input.context.associatedData read,
      .inr input.context.raw⟩)

set_option backward.isDefEq.respectTransparency false in
/-- All material routes make exactly one private component call before the actual optional plaintext exists. -/
theorem call_bound (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsTotalQueryBound 1 := by
  unfold call
  cases input.material <;> simp [IsTotalQueryBound]

set_option backward.isDefEq.respectTransparency false in
/-- A known material consumes no selected-key verification slot, even when its byte value aliases that key. -/
theorem call_target_bound (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery)
      (match input.material with | .hidden _ => 1 | .known _ => 0) := by
  unfold call
  cases input.material <;> simp only [isQueryBoundP_query_iff, AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery]
  all_goals simp

set_option backward.isDefEq.respectTransparency false in
/-- Every known-material opening retains its possible shared hash request; the selected-key raw oracle accounts for its own private hashing. -/
theorem call_hash_bound (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (match input.material with | .hidden _ => 0 | .known _ => 1) := by
  unfold call
  cases input.material <;> simp [isQueryBoundP_query_iff, AdaptiveCtxDynamicKnownBounds.HashRoute,
    AdaptiveCtxSharedReplayBounds.ModeHash, AdaptiveCtxQueryBounds.SourceWork,
    AdaptiveCtxQueryBounds.SourceUniform, AdaptiveCtxQueryBounds.SourceHash]

/-- Every known native material uses its actual key and nonce with the same raw-source opening and complete cache. -/
theorem known_open (input : RawCtxWholeOwner.OpenInput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxSharedModes.State)
    (nonempty : input.context.raw.isEmpty = false)
    (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (sequenceMatches : input.sequence = input.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    (targetImpl true (RawCtxKeyFreeDecoder.decoder (RawCtxSourceOpen.sourceNonce input) expected
      input.context.associatedData read) c (RawCtxSourceOpen.sourceKey input) (.inr input.context.raw)).run state =
      (fun result => (result.1, RawCtxSharedSourceOpening.retain state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c input
          (RawCtxCanonicalOpening.selectedTarget input slices parsed valid.2.2) (canonicalProjection state) := by
  rw [RawCtxSharedSourceOpening.real_complete]
  have accepted := RawCtxKeyFreeDecoder.decoder_selected input slices parsed read expected nonempty decoded valid sequenceMatches
  rw [← RawCtxKeyFreeDecoder.target_source] at accepted
  rw [RawCtxCanonicalOpening.sourceOpening_canonical c input slices parsed valid.2.2 _ _ accepted]
  rfl

/-- The component history slot follows the actual known/selected material branch. -/
def entry (slot : Nat) (material : Slot) (state : AdaptiveCtxDynamicKnownKeys.SourceState) : AdaptiveCtxSharedModes.State :=
  (match material with | .hidden _ => state.selected | .known _ => state.others slot, state.cache)

def retain (slot : Nat) (material : Slot) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (after : AdaptiveCtxCanonical.CanonicalState) : AdaptiveCtxDynamicKnownKeys.SourceState :=
  let updated := RawCtxSharedSourceOpening.retain (entry slot material state) after
  match material with
  | .hidden _ => { state with selected := updated.1, cache := updated.2 }
  | .known _ => { state with others := Function.update state.others slot updated.1, cache := updated.2 }

set_option backward.isDefEq.respectTransparency false in
/-- The selected material callback preserves the actual opening and every other known-key history. -/
theorem selected_call (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (sequenceMatches : sequence = context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxKeyFreeDecoder.decoder nonce expected context.associatedData read) c key)
      (call slot read expected ⟨.hidden nonce, sequence, context⟩)).run state =
      (fun result => (result.1, retain slot (.hidden nonce) state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c (nativeInput key nonce sequence context)
          (RawCtxCanonicalOpening.selectedTarget (nativeInput key nonce sequence context) slices parsed valid.2.2)
          (canonicalProjection (entry slot (.hidden nonce) state)) := by
  simp only [call, simulateQ_spec_query]
  change (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((localImpl true (RawCtxKeyFreeDecoder.decoder nonce expected context.associatedData read) c key
        (.inr context.raw)).run state.selected)).run state.cache
    pure (result.1.1, { state with selected := result.1.2, cache := result.2 })) = _
  rw [AdaptiveCtxSharedModes.local_from_target, selected_open key nonce sequence context read expected c
    (state.selected, state.cache) nonempty decoded valid sequenceMatches slices parsed]
  simp only [bind_pure_comp, Functor.map_map, AdaptiveCtxSharedModes.dismantle]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Dynamically known material performs its real native opening on the same shared cache even when its bytes equal the selected key. -/
theorem known_call (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (decode : RawDecoder) (material : RatchetMaterial)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (sequenceMatches : sequence = context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key)
      (call slot read expected ⟨.known material, sequence, context⟩)).run state =
      (fun result => (result.1, retain slot (.known material) state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c ⟨material, sequence, context⟩
          (RawCtxCanonicalOpening.selectedTarget ⟨material, sequence, context⟩ slices parsed valid.2.2)
          (canonicalProjection (entry slot (.known material) state)) := by
  simp only [call, simulateQ_spec_query]
  change (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((localImpl true (RawCtxKeyFreeDecoder.decoder (RawCtxSourceOpen.sourceNonce ⟨material, sequence, context⟩)
        expected context.associatedData read) c (RawCtxSourceOpen.sourceKey ⟨material, sequence, context⟩)
        (.inr context.raw)).run (state.others slot))).run state.cache
    pure (result.1.1, { state with others := Function.update state.others slot result.1.2, cache := result.2 })) = _
  rw [AdaptiveCtxSharedModes.local_from_target, known_open ⟨material, sequence, context⟩ read expected c
    (state.others slot, state.cache) nonempty decoded valid sequenceMatches slices parsed]
  simp only [bind_pure_comp, Functor.map_map, AdaptiveCtxSharedModes.dismantle]
  rfl

/-- Both material routes realize one native opening interface; selected context agreement is checked before the actual optional reply. -/
theorem call_source (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (nonce : NonceOutput) (ad : Pqxdh.Bytes)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (selectedContext : ∀ selected, input.material = .hidden selected →
      selected = nonce ∧ input.context.associatedData = ad)
    (nonempty : input.context.raw.isEmpty = false) (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (sequenceMatches : input.sequence = input.context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxKeyFreeDecoder.decoder nonce expected ad read) c key)
      (call slot read expected input)).run state =
      (fun result => (result.1, retain slot input.material state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c (RawCtxInterpretedArguments.toOpenInput
          (RawCtxInterpretedArguments.mapInput (interpret key) input))
          (RawCtxCanonicalOpening.selectedTarget (RawCtxInterpretedArguments.toOpenInput
            (RawCtxInterpretedArguments.mapInput (interpret key) input)) slices parsed valid.2.2)
          (canonicalProjection (entry slot input.material state)) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden selected =>
    obtain ⟨sameNonce, sameAd⟩ := selectedContext selected rfl
    subst nonce
    subst ad
    exact selected_call slot read expected key selected sequence context c state nonempty decoded valid sequenceMatches slices parsed
  | known material =>
    exact known_call slot read expected key _ material sequence context c state nonempty decoded valid sequenceMatches slices parsed

/-- The source's exact getters choose the callback; its actual optional plaintext is wrapped before the native finish. -/
noncomputable def opening (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :=
  RawCtxInterpretedOpening.run (fun material sequence context =>
    RawCtxSharedOpeningConsumer.apiReply sequence context <$> call slot read expected ⟨material, sequence, context⟩) pending

def interpretResult (key : RootOutput)
    (result : RustM (RefinedRatchet RatchetChain RatchetChain Slot × core.option.Option RawCtxWholeOwner.Decrypted)) :
    RustM (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) :=
  (fun published => (ConcreteRatchetKernel.mk (RawCtxMaterialInterpretation.mapRefined (interpret key) published.1),
    published.2)) <$> result

/-- All source finish branches retain the full interpreted kernel, including cached success, future success and optional rollback. -/
theorem finish_source (key : RootOutput)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (sequence : Std.U64) (reply : Option Pqxdh.Bytes) :
    ReceiveOpen.finish (RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending))
      (RawCtxSharedOpeningConsumer.apiReply sequence pending.context reply) =
      interpretResult key (RawCtxInterpretedOpening.finish pending
        (RawCtxSharedOpeningConsumer.apiReply sequence pending.context reply)) := by
  rw [RawCtxInterpretedOpening.native_finish, RawCtxInterpretedOpening.finish_map]
  simp only [interpretResult, Functor.map_map]

/-- The actual selected native getters forward the original raw input and finish with the real challenger reply. -/
theorem opening_present (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (material : Slot) (sequence : Std.U64)
    (selected : RawCtxInterpretedOpening.material pending = ok (.Some material))
    (prepared : RawCtxInterpretedOpening.sequence pending = ok sequence) :
    opening slot read expected pending = (do
      let reply ← call slot read expected ⟨material, sequence, pending.context⟩
      pure (RawCtxInterpretedOpening.finish pending
        (RawCtxSharedOpeningConsumer.apiReply sequence pending.context reply))) := by
  simp only [opening, RawCtxInterpretedOpening.run, selected, prepared,
    RawCtxInterpretedOpening.bindResult, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- The complete dynamic selected/known opening compiler reconstructs actual native publication, original optional plaintext and every shared-history/cache field. -/
theorem present_source (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (nonce : NonceOutput) (ad : Pqxdh.Bytes)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (material : Slot) (sequence : Std.U64)
    (selected : RawCtxInterpretedOpening.material pending = ok (.Some material))
    (prepared : RawCtxInterpretedOpening.sequence pending = ok sequence)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (selectedContext : ∀ selected, material = .hidden selected → selected = nonce ∧ pending.context.associatedData = ad)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (sequenceMatches : sequence = pending.context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (fun result => (interpretResult key result.1, result.2)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxKeyFreeDecoder.decoder nonce expected ad read) c key)
        (opening slot read expected pending)).run state = (do
      let result ← RawCtxCanonicalOpening.sourceOpening c ⟨interpret key material, sequence, pending.context⟩
        (RawCtxCanonicalOpening.selectedTarget ⟨interpret key material, sequence, pending.context⟩ slices parsed valid.2.2)
        (canonicalProjection (entry slot material state))
      pure (ReceiveOpen.finish (RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending))
        (RawCtxSharedOpeningConsumer.apiReply sequence pending.context result.1), retain slot material state result.2)) := by
  rw [opening_present slot read expected pending material sequence selected prepared]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [call_source slot read expected key nonce ad ⟨material, sequence, pending.context⟩ c state
    selectedContext nonempty decoded valid sequenceMatches slices parsed]
  simp only [map_bind, map_pure, bind_map_left, finish_source]
  rfl

/-- Missing or stale cached material returns through the source finish without any cryptographic callback. -/
theorem opening_missing (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (missing : RawCtxInterpretedOpening.material pending = ok .None) :
    opening slot read expected pending = pure (RawCtxInterpretedOpening.finish pending
      (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted)) := by
  simp only [opening, RawCtxInterpretedOpening.run, missing, RawCtxInterpretedOpening.bindResult]

/-- Every represented source capability issues at most one dynamic component call, including all failed native getters and missing slots. -/
theorem opening_bound (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :
    (opening slot read expected pending).IsTotalQueryBound 1 := by
  unfold opening RawCtxInterpretedOpening.run
  cases found : RawCtxInterpretedOpening.material pending with
  | fail error => trivial
  | div => trivial
  | ok value =>
    cases value with
    | none => trivial
    | some material =>
      cases prepared : RawCtxInterpretedOpening.sequence pending with
      | fail error => trivial
      | div => trivial
      | ok sequence =>
        simpa only [RawCtxInterpretedOpening.bindResult, bind_map_left, bind_pure_comp,
          Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff] using
          call_bound slot read expected ⟨material, sequence, pending.context⟩

end BeaconcryptCore.Computational.RawCtxSelectedMessageOpening

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_key

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_nonce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_nonce

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_open

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_target_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_hash_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.known_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.known_open

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.selected_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.known_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.known_call

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.call_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.finish_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_present

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.present_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.present_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_missing

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageOpening.opening_bound
