import BeaconcryptCore.Computational.RawCtxSelectedMessageSealing

/-!
The source sealing callback uses the same dynamic-known-key component as raw opening. Known seals remain unchecked native local operations with explicitly forwarded hash calls. Selected seals use the ordinary challenger and propagate its nonce refusal as an explicit stop. The whole shared state, all other histories and the original optional writer result are retained; no source nonce-invariant or probability bound is assumed by these operational equations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSealConsumer
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open RawCtxSelectedMessageSealing

noncomputable def liftSelected : QueryImpl ReceiveSpec (OracleComp Spec) := fun query => Spec.query (.inl query)

def install (before : SourceState) (after : AdaptiveCtxSharedModes.State) : SourceState :=
  { before with selected := after.1, cache := after.2 }

set_option backward.isDefEq.respectTransparency false in
/-- Every forwarded selected request keeps all other dynamically known histories and the identical shared cache. -/
theorem lifted_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (before : SourceState) (query : ReceiveSpec.Domain) (state : AdaptiveCtxSharedModes.State) :
    (fun result => (result.1, install before result.2)) <$>
      (targetImpl real decode c key query).run state =
      ((sourceImpl real decode c key ∘ₛ liftSelected) query).run (install before state) := by
  simp only [QueryImpl.compose, liftSelected, simulateQ_spec_query]
  change _ = (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((AdaptiveCtxSharedModes.localImpl real decode c key query).run state.1)).run state.2
    pure (result.1.1, install before (result.1.2, result.2)))
  rw [AdaptiveCtxSharedModes.local_from_target]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

/-- Arbitrary sealing and public-hash continuations are interpreted by the same selected challenger while all other histories survive. -/
theorem lifted_complete (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (work : OracleComp ReceiveSpec Result) (before : SourceState) :
    (simulateQ (sourceImpl real decode c key) (simulateQ liftSelected work)).run before =
      (fun result => (result.1, install before result.2)) <$>
        (simulateQ (targetImpl real decode c key) work).run (before.selected, before.cache) := by
  rw [← QueryImpl.simulateQ_compose]
  have same := map_run_simulateQ_eq_of_query_map_eq
    (targetImpl real decode c key) (sourceImpl real decode c key ∘ₛ liftSelected)
    (install before) (lifted_step real decode c key before) work (before.selected, before.cache)
  exact same.symm

/-- The real selected component retains its complete canonical state and unchanged unused suffix dictionary across any adaptive callback program. -/
theorem canonical_complete (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (work : OracleComp ReceiveSpec Result) (before : AdaptiveCtxSharedModes.State) :
    (simulateQ (targetImpl true decode c key) work).run before =
      (fun result => (result.1, RawCtxSharedSourceOpening.retain before result.2)) <$>
        (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key) work).run (canonicalProjection before) := by
  have step : ∀ query state,
      (fun result => (result.1, RawCtxSharedSourceOpening.retain before result.2)) <$>
        (AdaptiveCtxCanonical.canonicalImpl decode c key query).run state =
      (targetImpl true decode c key query).run (RawCtxSharedSourceOpening.retain before state) := by
    intro query state
    simpa only [RawCtxSharedSourceOpening.retain, canonicalProjection,
      AdaptiveCtxSharedHash.install_separate] using
      (RawCtxSharedSourceOpening.real_complete decode c key query
        (RawCtxSharedSourceOpening.retain before state)).symm
  exact (map_run_simulateQ_eq_of_query_map_eq
    (AdaptiveCtxCanonical.canonicalImpl decode c key) (targetImpl true decode c key)
    (RawCtxSharedSourceOpening.retain before) step work (canonicalProjection before)).symm

noncomputable def call (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) : OracleComp Spec SealResult :=
  simulateQ liftSelected (match input.material with
    | .hidden nonce => selected writer nonce input.sequence input.context
    | .known material => SealResult.completed <$> known c writer ⟨material, input.sequence, input.context⟩)

/-- The complete selected sealing callback reaches the original native inner seal and writer before the explicit nonce-stop event, preserving every other component history. -/
theorem selected_fresh_call (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (fresh : nonce ∉ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode c key)
      (call c writer ⟨.hidden nonce, sequence, context⟩)).run before = (do
      let result ← (simulateQ ctxRandomOracle (ctxSeal c key (selectedInput nonce sequence context width))).run before.cache
      pure (.completed (writer ⟨sequence, context.senderId, result.1.encode⟩),
        install before (RawCtxSharedSourceOpening.retain (before.selected, before.cache)
          (afterSeal (canonicalProjection (before.selected, before.cache))
            (selectedInput nonce sequence context width) result.1 result.2)))) := by
  simp only [call]
  rw [lifted_complete, canonical_complete, RawCtxSelectedMessageSealing.selected_fresh decode c key writer nonce sequence context width _ fresh]
  simp only [map_bind, map_pure, canonicalProjection, AdaptiveCtxSharedHash.install]

/-- A repeated selected nonce propagates an explicit stop while preserving the entire dynamic state; it is not translated into native writer failure. -/
theorem selected_repeat_call (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (used : nonce ∈ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode c key)
      (call c writer ⟨.hidden nonce, sequence, context⟩)).run before = pure (.repeatedNonce, before) := by
  simp only [call]
  rw [lifted_complete, canonical_complete, RawCtxSelectedMessageSealing.selected_repeat decode c key writer nonce sequence context width _ used]
  simp only [map_pure, install, RawCtxSharedSourceOpening.retain, canonicalProjection,
    AdaptiveCtxSharedHash.separate_install]

/-- A known-material seal retains the actual source writer and shared ROM while leaving all other material histories unchanged, even on nonce reuse or selected-key byte aliases. -/
theorem known_call (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (material : RatchetMaterial) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (before : SourceState) :
    (simulateQ (sourceImpl real decode c key)
      (call c writer ⟨.known material, sequence, context⟩)).run before =
      (fun result => (SealResult.completed result.1,
        install before (AdaptiveCtxSharedModes.replaceShared (before.selected, before.cache) result.2))) <$>
        (simulateQ AdaptiveCtxSharedTarget.sharedImpl (simulateQ hashLift
          (RawCtxCanonicalSeal.typedSource c writer ⟨material, sequence, context⟩))).run
          (before.cache, before.selected.1.publicInputs) := by
  simp only [call]
  rw [lifted_complete]
  simp only [simulateQ_map, StateT.run_map]
  rw [known_complete]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Projecting only bookkeeping fields gives the same selected callback output and complete source hash cache. -/
theorem lifted_cache (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (work : OracleComp ReceiveSpec Result) (before : SourceState) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl real decode c key) (simulateQ liftSelected work)).run before =
      (fun result => (result.1, result.2.2)) <$>
        (simulateQ (targetImpl real decode c key) work).run (before.selected, before.cache) := by
  rw [lifted_complete]
  simp only [Functor.map_map, install]

/-- The known route projects to the exact original unchecked source callback and cache, without imposing selected-nonce freshness on known keys. -/
theorem known_source_cache (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (material : RatchetMaterial) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (before : SourceState) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl real decode c key)
        (call c writer ⟨.known material, sequence, context⟩)).run before =
      (fun result => (SealResult.completed result.1, result.2)) <$>
        (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
          (RawCtxSourceSeal.sealInput ⟨material, sequence, context⟩))).run before.cache := by
  simp only [call]
  rw [lifted_cache]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  have exactSource := congrArg (fun work => (fun result => (SealResult.completed result.1, result.2)) <$> work)
    (RawCtxSelectedMessageSealing.known_source real decode c key writer ⟨material, sequence, context⟩ (before.selected, before.cache))
  simpa only [Functor.map_map] using exactSource

/-- Before the separately recorded selected-nonce stop, the dynamic callback projects to exactly the native source seal, writer and cache. -/
theorem selected_source_cache (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (width : context.associatedData.length = 281)
    (before : SourceState) (fresh : nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl true decode c key)
        (call c writer ⟨.hidden nonce, sequence, context⟩)).run before =
      (fun result => (SealResult.completed result.1, result.2)) <$>
        (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
          (RawCtxSourceSeal.sealInput (selectedNative key nonce sequence context)))).run before.cache := by
  simp only [call]
  rw [lifted_cache, canonical_complete]
  simpa only [Functor.map_map, RawCtxSharedSourceOpening.retain, AdaptiveCtxSharedHash.separate,
    canonicalProjection, AdaptiveCtxSharedHash.install] using
    RawCtxSelectedMessageSealing.selected_source decode c key writer nonce sequence context width
      (canonicalProjection (before.selected, before.cache)) fresh

set_option backward.isDefEq.respectTransparency false in
/-- Forwarding to the selected component preserves the actual query classification and allowance without hiding known local hash work. -/
theorem lifted_bound {Result : Type} (predicate : Spec.Domain → Prop) [DecidablePred predicate]
    (work : OracleComp ReceiveSpec Result) (bound : Nat)
    (bounded : work.IsQueryBoundP (fun query => predicate (.inl query)) bound) :
    (simulateQ liftSelected work).IsQueryBoundP predicate bound := by
  apply RawCtxSourceOpen.simulate_bound liftSelected (fun query => predicate (.inl query)) predicate work bound bounded
  intro query
  simp only [liftSelected, isQueryBoundP_query_iff]
  split <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- Every locally known seal contributes its actual public shared-ROM call; selected seal hashing stays inside the ordinary challenger ledger. -/
theorem call_hash (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    (call c writer input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (match input.material with | .hidden _ => 0 | .known _ => 1) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    simp only [call]
    apply lifted_bound
    simpa only [AdaptiveCtxDynamicKnownBounds.HashRoute] using
      (selected_bills writer nonce sequence context).2.1
  | known value =>
    simp only [call]
    apply lifted_bound
    simpa only [AdaptiveCtxDynamicKnownBounds.HashRoute, isQueryBoundP_map_iff] using
      (known_bills c writer ⟨value, sequence, context⟩).1

set_option backward.isDefEq.respectTransparency false in
/-- A selected seal attempt costs one ordinary sealing query even if refused; known local seals do not consume selected-key sealing queries. -/
theorem call_seal (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    (call c writer input).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (match input.material with | .hidden _ => 1 | .known _ => 0) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    simp only [call]
    apply lifted_bound
    simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass] using
      (selected_bills writer nonce sequence context).1
  | known value =>
    simp only [call]
    apply lifted_bound
    simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass, isQueryBoundP_map_iff] using
      (known_bills c writer ⟨value, sequence, context⟩).2.1

set_option backward.isDefEq.respectTransparency false in
/-- The complete sealing adapter adds no verification attempt or explicit random-byte request; its hash sampling remains billed inside the shared component. -/
theorem call_other (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    (call c writer input).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0 ∧
      (call c writer input).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce =>
    simp only [call]
    constructor
    · apply lifted_bound
      simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass] using
        (selected_bills writer nonce sequence context).2.2.1
    · apply lifted_bound
      simpa only [AdaptiveCtxDynamicKnownBounds.UniformRoute] using
        (selected_bills writer nonce sequence context).2.2.2
  | known value =>
    simp only [call]
    constructor
    · apply lifted_bound
      simpa only [AdaptiveCtxDynamicKnownBounds.TargetClass, isQueryBoundP_map_iff] using
        (known_bills c writer ⟨value, sequence, context⟩).2.2
    · apply lifted_bound
      simpa only [AdaptiveCtxDynamicKnownBounds.UniformRoute, isQueryBoundP_map_iff] using
        known_uniform c writer ⟨value, sequence, context⟩

/-- The all-input source equation requires selected-nonce freshness only when the actual selected seal can issue a challenger query. Known aliases and invalid AD retain their original source behavior. -/
theorem call_source_cache (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (before : SourceState)
    (fresh : ∀ nonce, input.material = .hidden nonce → input.context.associatedData.length = 281 →
      nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl true decode c key) (call c writer input)).run before =
      (fun result => (SealResult.completed result.1, result.2)) <$>
        (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
          (RawCtxSourceSeal.sealInput (RawCtxInterpretedArguments.toSealInput
            (RawCtxInterpretedArguments.mapInput (interpret key) input))))).run before.cache := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | known material => exact known_source_cache true decode c key writer material sequence context before
  | hidden nonce =>
    by_cases width : context.associatedData.length = 281
    · exact selected_source_cache decode c key writer nonce sequence context width before (fresh nonce rfl width)
    · rw [RawCtxCanonicalSeal.sealInput_invalid c writer _ width]
      simp only [call, RawCtxSelectedMessageSealing.selected, width, ↓reduceDIte,
        simulateQ_pure, StateT.run_pure, map_pure]

/-- The outer option is the explicit challenger stop. The inner option is the unaltered source writer result. -/
def reply (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext) :
    SealResult → Option (Option RawCtxSourceSend.Encrypted)
  | .repeatedNonce => none
  | .completed ciphertext => some (ciphertext.map (RawCtxInterpretedArguments.encrypted input))

noncomputable def sealing (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) :
    OracleComp Spec (Option (Option RawCtxSourceSend.Encrypted)) :=
  reply (RawCtxInterpretedArguments.sealArguments pending) <$>
    call c writer (RawCtxInterpretedArguments.sealArguments pending)

/-- Before the explicit nonce stop, the actual pending send returns the original optional encrypted API value and shared source cache. Its target route and sequence come from the native pending capability. -/
theorem sealing_source (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (before : SourceState)
    (fresh : ∀ nonce, pending.material = .hidden nonce → pending.context.associatedData.length = 281 →
      nonce ∉ before.selected.1.usedNonces) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (sourceImpl true decode c key) (sealing c writer pending)).run before =
      (fun result => (some (result.1.map (RawCtxSourceSend.encrypted
        (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal
          (RawCtxInterpretedSend.mapSeal (interpret key) pending))))), result.2)) <$>
        (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
          (RawCtxSourceSeal.sealInput (RawCtxSourceSend.arguments
            (RawCtxInterpretedSend.nativeSeal (RawCtxInterpretedSend.mapSeal (interpret key) pending)))))).run before.cache := by
  have exactSource := congrArg (fun work => (fun result =>
      (reply (RawCtxInterpretedArguments.sealArguments pending) result.1, result.2)) <$> work)
    (call_source_cache decode c key writer (RawCtxInterpretedArguments.sealArguments pending) before fresh)
  have sameEncrypted : RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments pending) =
      RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal
        (RawCtxInterpretedSend.mapSeal (interpret key) pending))) := by
    funext ciphertext
    rfl
  simpa only [sealing, simulateQ_map, StateT.run_map, Functor.map_map, reply, sameEncrypted,
    RawCtxInterpretedArguments.sealArguments_native, RawCtxInterpretedArguments.sealArguments_map] using exactSource

def nativeReply (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (ciphertext : Option Pqxdh.Bytes) : core.option.Option RawCtxSourceSend.Encrypted :=
  match ciphertext with
  | none => .None
  | some bytes => .Some (RawCtxInterpretedArguments.encrypted input bytes)

/-- Actual extracted send finish publishes the complete advanced kernel with the actual optional ciphertext; material interpretation need not be injective. -/
theorem native_finish (key : RootOutput)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (ciphertext : Option Pqxdh.Bytes) :
    SendSeal.finish (RawCtxInterpretedSend.nativeSeal (RawCtxInterpretedSend.mapSeal (interpret key) pending))
      (nativeReply (RawCtxInterpretedArguments.sealArguments pending) ciphertext) =
      (fun result => (ConcreteRatchetKernel.mk (RawCtxMaterialInterpretation.mapRefined (interpret key) result.1), result.2)) <$>
        RawCtxInterpretedSend.finish pending (nativeReply (RawCtxInterpretedArguments.sealArguments pending) ciphertext) := by
  rw [RawCtxInterpretedSend.native_finish, RawCtxInterpretedSend.finish_map]
  simp only [Functor.map_map]

/-- The pending API adapter retains the explicit nonce stop and the whole state, instead of publishing an ordinary failed writer result. -/
theorem sealing_repeat (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (nonce : NonceOutput) (material : pending.material = .hidden nonce)
    (width : pending.context.associatedData.length = 281)
    (before : SourceState) (used : nonce ∈ before.selected.1.usedNonces) :
    (simulateQ (sourceImpl true decode c key) (sealing c writer pending)).run before = pure (none, before) := by
  have arguments : RawCtxInterpretedArguments.sealArguments pending = ⟨.hidden nonce, pending.sequence, pending.context⟩ := by
    simp only [RawCtxInterpretedArguments.sealArguments, material]
  rw [sealing, arguments, simulateQ_map, StateT.run_map,
    selected_repeat_call decode c key writer nonce pending.sequence pending.context width before used]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Wrapping the native pending reply retains all four actual component query classes, including refused selected seals and known shared-hash work. -/
theorem sealing_bills (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) :
    (sealing c writer pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (match pending.material with | .hidden _ => 0 | .known _ => 1) ∧
      (sealing c writer pending).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
        (match pending.material with | .hidden _ => 1 | .known _ => 0) ∧
      (sealing c writer pending).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery) 0 ∧
      (sealing c writer pending).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simpa only [sealing, isQueryBoundP_map_iff, RawCtxInterpretedArguments.sealArguments] using
    And.intro (call_hash c writer (RawCtxInterpretedArguments.sealArguments pending))
      (And.intro (call_seal c writer (RawCtxInterpretedArguments.sealArguments pending))
        (call_other c writer (RawCtxInterpretedArguments.sealArguments pending)))

end BeaconcryptCore.Computational.RawCtxSelectedSealConsumer

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_complete
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.canonical_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.canonical_complete
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_fresh_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_fresh_call
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_repeat_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_repeat_call
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.known_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.known_call
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_cache
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.known_source_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.known_source_cache
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_source_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.selected_source_cache
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.lifted_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_hash
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_seal
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_other
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_source_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.call_source_cache
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_source
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.native_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.native_finish
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_repeat
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSealConsumer.sealing_bills
