import BeaconcryptCore.Computational.RawCtxUniversalDecoder

/-!
Every selected-material opening uses one fixed universal decoder, with the original raw frame kept inside the checked private context framing. Actual source getters, caller ownership, optional challenger plaintext and complete cached/future finish remain unchanged. Equal selected derivation addresses need not imply equal owner or AD. Known material keeps its ordinary real native operation on the same shared cache, including byte aliases.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxUniversalOpening
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes
open RawCtxSelectedMessageOpening hiding call selected_call call_source opening opening_present present_source

noncomputable def call (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Pqxdh.Bytes) :=
  match input.material with
  | .hidden nonce =>
    if width : input.context.associatedData.length = 153 then
      AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr
        (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce input.context width))))
    else pure none
  | .known material => RawCtxSelectedMessageOpening.call slot read expected ⟨.known material, input.sequence, input.context⟩

set_option backward.isDefEq.respectTransparency false in
/-- The selected callback retains the actual native optional opening and every other live component history, with no fixed-context agreement premise. -/
theorem selected_call (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (width : context.associatedData.length = 153)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (sequenceMatches : sequence = context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
      (call slot read expected ⟨.hidden nonce, sequence, context⟩)).run state =
      (fun result => (result.1, retain slot (.hidden nonce) state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c (nativeInput key nonce sequence context)
          (RawCtxCanonicalOpening.selectedTarget (nativeInput key nonce sequence context) slices parsed width)
          (canonicalProjection (entry slot (.hidden nonce) state)) := by
  simp only [call, dif_pos width, simulateQ_spec_query]
  change (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((localImpl true (RawCtxUniversalDecoder.decoder read) c key
        (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width)))).run state.selected)).run state.cache
    pure (result.1.1, { state with selected := result.1.2, cache := result.2 })) = _
  rw [AdaptiveCtxSharedModes.local_from_target,
    RawCtxUniversalDecoder.selected_open key nonce sequence context read c
      (state.selected, state.cache) slices width nonempty decoded parsed sequenceMatches]
  simp only [bind_pure_comp, Functor.map_map, AdaptiveCtxSharedModes.dismantle]
  rfl

/-- Both selected and known material realize the same source opening interface under one fixed decoder, retaining source provenance before the reply. -/
theorem call_source (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : input.context.raw.isEmpty = false) (decoded : read input.context.raw = some input.context.frame)
    (valid : RawCtxReceive.ValidFrame expected input.context.associatedData input.context.frame)
    (sequenceMatches : input.sequence = input.context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
      (call slot read expected input)).run state =
      (fun result => (result.1, retain slot input.material state result.2)) <$>
        RawCtxCanonicalOpening.sourceOpening c (RawCtxInterpretedArguments.toOpenInput
          (RawCtxInterpretedArguments.mapInput (interpret key) input))
          (RawCtxCanonicalOpening.selectedTarget (RawCtxInterpretedArguments.toOpenInput
            (RawCtxInterpretedArguments.mapInput (interpret key) input)) slices parsed valid.2.2)
          (canonicalProjection (entry slot input.material state)) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    exact selected_call slot read expected key nonce sequence context c state valid.2.2
      nonempty decoded sequenceMatches slices parsed
  | known material =>
    exact known_call slot read expected key _ material sequence context c state nonempty decoded valid sequenceMatches slices parsed

/-- The source's exact getters choose the callback; its actual optional plaintext is wrapped before the native finish. -/
noncomputable def opening (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext) :=
  RawCtxInterpretedOpening.run (fun material sequence context =>
    RawCtxSharedOpeningConsumer.apiReply sequence context <$> call slot read expected ⟨material, sequence, context⟩) pending

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
    (key : RootOutput)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (material : Slot) (sequence : Std.U64)
    (selected : RawCtxInterpretedOpening.material pending = ok (.Some material))
    (prepared : RawCtxInterpretedOpening.sequence pending = ok sequence)
    (c : Pqxdh.Crypto) (state : AdaptiveCtxDynamicKnownKeys.SourceState)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (sequenceMatches : sequence = pending.context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (fun result => (interpretResult key result.1, result.2)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
        (opening slot read expected pending)).run state = (do
      let result ← RawCtxCanonicalOpening.sourceOpening c ⟨interpret key material, sequence, pending.context⟩
        (RawCtxCanonicalOpening.selectedTarget ⟨interpret key material, sequence, pending.context⟩ slices parsed valid.2.2)
        (canonicalProjection (entry slot material state))
      pure (ReceiveOpen.finish (RawCtxInterpretedOpening.toNative (RawCtxInterpretedOpening.mapOpening (interpret key) pending))
        (RawCtxSharedOpeningConsumer.apiReply sequence pending.context result.1), retain slot material state result.2)) := by
  rw [opening_present slot read expected pending material sequence selected prepared]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [call_source slot read expected key ⟨material, sequence, pending.context⟩ c state
    nonempty decoded valid sequenceMatches slices parsed]
  simp only [map_bind, map_pure, bind_map_left, finish_source]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reached opening makes at most one dynamic component request, including failed AD admission. -/
theorem call_bound (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsTotalQueryBound 1 := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce => simp only [call]; split <;> simp [IsTotalQueryBound]
  | known material => simpa only [call] using RawCtxSelectedMessageOpening.call_bound slot read expected ⟨.known material, sequence, context⟩

set_option backward.isDefEq.respectTransparency false in
/-- Only a selected material consumes a target verification slot; known material retains its explicitly separate local hash work. -/
theorem call_raw (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery)
      (match input.material with | .hidden _ => 1 | .known _ => 0) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    simp only [call]
    split <;> simp [AdaptiveCtxDynamicKnownBounds.TargetClass, IsRawQuery]
  | known value => simpa only [call] using RawCtxSelectedMessageOpening.call_target_bound slot read expected ⟨.known value, sequence, context⟩

set_option backward.isDefEq.respectTransparency false in
/-- Known openings pay their shared hash call, while the ordinary selected component charges its own verification hash. -/
theorem call_hash (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) :
    (call slot read expected input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (match input.material with | .hidden _ => 0 | .known _ => 1) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    simp only [call]
    split <;> simp [AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]
  | known value => simpa only [call] using RawCtxSelectedMessageOpening.call_hash_bound slot read expected ⟨.known value, sequence, context⟩

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

end BeaconcryptCore.Computational.RawCtxUniversalOpening

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.selected_call

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.call_source

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_present

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.present_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.present_source

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.call_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.call_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.call_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.call_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.call_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_missing

/-- info: 'BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxUniversalOpening.opening_bound
