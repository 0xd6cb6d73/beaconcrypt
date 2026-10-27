import BeaconcryptCore.Computational.RawCtxSelectedMessageOpening
import BeaconcryptCore.Computational.RawCtxCanonicalSeal

/-!
Known material is sealed locally and every commitment lookup reaches the same selected challenger's public ROM. This local source path does not inherit the selected-key oracle's nonce-reuse rejection. Its exact native writer outcome and shared cache are retained, including writer failure and equal known/selected key bytes. Selected material must instead use the ordinary sealing oracle and its actual nonce-attempt ledger; a repeated selected nonce is an explicit stopping event, not a production rejection rule.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageSealing
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxSharedModes
open AdaptiveCtxSharedTarget

/-- Exact same-input public ROM routing for a locally known source material. -/
noncomputable def hashLift : QueryImpl CtxRO (OracleComp HashSpec) := fun query =>
  HashSpec.query (.inr query)

noncomputable def known (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) : OracleComp ReceiveSpec (Option Pqxdh.Bytes) :=
  simulateQ forward (simulateQ hashLift (RawCtxCanonicalSeal.typedSource c writer input))

/-- The actual local source seal keeps the complete selected state and full shared cache; only its forwarded hash history is appended. -/
theorem known_complete (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (writer : RawCtxMixedShared.Writer) (input : RawCtxSourceSend.SealInput) (before : AdaptiveCtxSharedModes.State) :
    (simulateQ (targetImpl real decode c key) (known c writer input)).run before =
      Prod.map id (replaceShared before) <$>
        (simulateQ sharedImpl (simulateQ hashLift (RawCtxCanonicalSeal.typedSource c writer input))).run
          (before.2, before.1.1.publicInputs) :=
  AdaptiveCtxSharedModes.forward_complete real decode c key before _

/-- Forwarded known-material hashing is the original native hash interpretation at the exact shared cache. -/
theorem hash_interpretation {Result : Type} (work : OracleComp CtxRO Result) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (simulateQ hashLift work)).run cache =
      (simulateQ ctxRandomOracle work).run cache := by
  have exactImpl : hashImpl ∘ₛ hashLift = ctxRandomOracle := by
    funext query
    simp [QueryImpl.compose, hashLift, hashImpl, OracleSpec.query]
  rw [← QueryImpl.simulateQ_compose, exactImpl]

/-- Erasing only added challenger history recovers the actual source sealing callback, including optional writer failure, without any nonce-freshness premise on known keys. -/
theorem known_source (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (writer : RawCtxMixedShared.Writer) (input : RawCtxSourceSend.SealInput) (before : AdaptiveCtxSharedModes.State) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (targetImpl real decode c key) (known c writer input)).run before =
      (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
        (RawCtxSourceSeal.sealInput input))).run before.2 := by
  rw [known_complete, RawCtxCanonicalSeal.sealInput_complete, ← hash_interpretation]
  simpa only [Functor.map_map, Prod.map_def, AdaptiveCtxSharedModes.replaceShared, Function.comp_def, id_eq] using
    cache_schedule (simulateQ hashLift (RawCtxCanonicalSeal.typedSource c writer input))
      (before.2, before.1.1.publicInputs)

set_option backward.isDefEq.respectTransparency false in
/-- Renaming the original source hash queries preserves their actual total allowance. -/
theorem hashLift_bound {Result : Type} (work : OracleComp CtxRO Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (simulateQ hashLift work).IsTotalQueryBound bound := by
  apply bounded.simulateQ_of_step
  intro query
  simp [hashLift, IsTotalQueryBound]

/-- Known-material sealing charges its actual shared-ROM lookup; it never invokes a selected-key seal or raw-opening oracle. -/
theorem known_bills (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    (known c writer input).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash 1 ∧
      (known c writer input).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0 ∧
      (known c writer input).IsQueryBoundP IsRawQuery 0 := by
  unfold known
  refine ⟨forward_bound _ _ _ ?_, forward_bound _ _ _ ?_, forward_bound _ _ _ ?_⟩
  · exact (hashLift_bound _ 1 (RawCtxCanonicalSeal.typedSource_query_bound c writer input)).isQueryBoundP
  · simp only [forward_seal_class]
    exact isQueryBoundP_false _ 0
  · simp only [forward_raw_class]
    exact isQueryBoundP_false _ 0

set_option backward.isDefEq.respectTransparency false in
/-- Local known sealing has no explicit coin request; the shared-ROM challenger separately charges its digest sampling. -/
theorem hashLift_no_uniform {Result : Type} (work : OracleComp CtxRO Result) :
    (simulateQ hashLift work).IsQueryBoundP (HashClass false) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, hashLift,
      isQueryBoundP_query_bind_iff, HashClass, Bool.false_eq_true, not_false_eq_true,
      true_or, ite_false]
    exact ⟨trivial, ih⟩

/-- The actual known-material source path adds zero explicit selected-challenger coins. -/
theorem known_uniform (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) :
    (known c writer input).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform 0 := by
  unfold known
  apply forward_bound
  simpa only [forward_uniform_class] using hashLift_no_uniform (RawCtxCanonicalSeal.typedSource c writer input)

open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey

def selectedInput (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (had : context.associatedData.length = 281) : CtxSealInput :=
  ⟨nonce, ⟨⟨context.associatedData, sequence.val, context.senderId.val⟩,
    had, sequence.bv.isLt, context.senderId.bv.isLt⟩, context.plaintext⟩

def selectedNative (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) : RawCtxSourceSend.SealInput :=
  ⟨interpret key (.hidden nonce), sequence, context⟩

/-- The selected ordinary sealing input retains the same nonce, sequence, sender, AD and actual plaintext while the unavailable key stays in the native interpretation. -/
theorem selected_input (key : RootOutput) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (had : context.associatedData.length = 281) :
    RawCtxCanonicalSeal.sourceKey (selectedNative key nonce sequence context) = key ∧
      RawCtxCanonicalSeal.sourceInput (selectedNative key nonce sequence context) had =
        selectedInput nonce sequence context had := by
  have exactNonce : RawCtxCanonicalSeal.sourceNonce (selectedNative key nonce sequence context) = nonce := by
    apply List.Vector.toList_injective
    simp [RawCtxCanonicalSeal.sourceNonce, selectedNative, interpret, RawCtxFreshChainCut.concreteMaterial,
      BeaconcryptCore.Refinement.RepresentationBridge.absMaterial, PqxdhRefinement.absBytes,
      List.map_map, Function.comp_def]
  constructor
  · apply List.Vector.toList_injective
    simp [RawCtxCanonicalSeal.sourceKey, selectedNative, interpret, RawCtxFreshChainCut.concreteMaterial,
      BeaconcryptCore.Refinement.RepresentationBridge.absMaterial, PqxdhRefinement.absBytes,
      List.map_map, Function.comp_def]
  · simp only [RawCtxCanonicalSeal.sourceInput, exactNonce]
    rfl

/-- Nonce refusal is explicit stopping, distinct from a native writer's ordinary optional result. -/
inductive SealResult where
  | repeatedNonce
  | completed : Option Pqxdh.Bytes → SealResult

/-- The selected key is absent from the actual source sealing adapter. -/
noncomputable def selected (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) : OracleComp ReceiveSpec SealResult :=
  if had : context.associatedData.length = 281 then do
    let reply ← ReceiveSpec.query (.inl (.inr (.inr (selectedInput nonce sequence context had))))
    pure (match reply with
      | none => .repeatedNonce
      | some record => .completed (writer ⟨sequence, context.senderId, record.encode⟩))
  else pure (.completed none)

/-- A completed inner selected seal enters the nonce and record ledger before any optional writer result. -/
def afterSeal (state : AdaptiveCtxCanonical.CanonicalState) (input : CtxSealInput)
    (record : CtxRomRecord) (cache : CtxRO.QueryCache) : AdaptiveCtxCanonical.CanonicalState :=
  ⟨state.ctx.addSeal ⟨input, record⟩ cache, state.rawAttempts,
    CtxSplitCache.outerSuffix input.nonce input.context record.tag :: state.privateInputs⟩

set_option backward.isDefEq.respectTransparency false in
/-- Before actual nonce reuse, the ordinary selected oracle is exactly the source's unchecked inner seal with complete attempt instrumentation. -/
theorem canonical_fresh (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : AdaptiveCtxCanonical.CanonicalState) (fresh : input.nonce ∉ state.ctx.usedNonces) :
    AdaptiveCtxCanonical.canonicalCtx c key (.inr input) state = (do
      let result ← (simulateQ ctxRandomOracle (ctxSeal c key input)).run state.ctx.cache
      pure (some result.1, afterSeal state input result.1 result.2)) := by
  simp only [AdaptiveCtxCanonical.canonicalCtx, ctxAdversaryImpl, QueryImpl.add_apply_inr,
    ctxSealOracle, fresh, ite_false, ctxSeal, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run, bind_assoc, pure_bind,
    afterSeal, AdaptiveCtxCanonical.sealPrivateInputs]
  change _ = (((ctxRandomOracle _ state.ctx.cache) >>= fun result =>
    (pure _ : ProbComp (CtxRomRecord × CtxRO.QueryCache))) >>= fun result => pure _)
  simp only [bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- A first selected-nonce use invokes the actual inner source seal, then the original optional writer, while retaining every ledger and cache field. -/
theorem selected_fresh (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (had : context.associatedData.length = 281)
    (state : AdaptiveCtxCanonical.CanonicalState) (fresh : nonce ∉ state.ctx.usedNonces) :
    (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key) (selected writer nonce sequence context)).run state = (do
      let result ← (simulateQ ctxRandomOracle (ctxSeal c key (selectedInput nonce sequence context had))).run state.ctx.cache
      pure (.completed (writer ⟨sequence, context.senderId, result.1.encode⟩),
        afterSeal state (selectedInput nonce sequence context had) result.1 result.2)) := by
  simp only [selected, dite_eq_left had, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do
    let result ← AdaptiveCtxCanonical.canonicalCtx c key (.inr (selectedInput nonce sequence context had)) state
    pure ((match result.1 with
      | none => SealResult.repeatedNonce
      | some record => .completed (writer ⟨sequence, context.senderId, record.encode⟩)), result.2)) = _
  rw [canonical_fresh c key (selectedInput nonce sequence context had) state fresh]
  simp only [bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Actual selected nonce reuse is a separately visible stopping outcome, never a fabricated native optional failure or a free uncounted source seal. -/
theorem selected_repeat (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (had : context.associatedData.length = 281)
    (state : AdaptiveCtxCanonical.CanonicalState) (used : nonce ∈ state.ctx.usedNonces) :
    (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key) (selected writer nonce sequence context)).run state =
      pure (.repeatedNonce, state) := by
  simp only [selected, dite_eq_left had, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do
    let result ← AdaptiveCtxCanonical.canonicalCtx c key (.inr (selectedInput nonce sequence context had)) state
    pure ((match result.1 with
      | none => SealResult.repeatedNonce
      | some record => .completed (writer ⟨sequence, context.senderId, record.encode⟩)), result.2)) = _
  simp [AdaptiveCtxCanonical.canonicalCtx, ctxAdversaryImpl, ctxSealOracle, selectedInput, used,
    StateT.run, AdaptiveCtxCanonical.sealPrivateInputs]

/-- Before the recorded nonce stop, erasing only analysis histories yields the exact original source callback and shared cache, including optional writer failure. -/
theorem selected_source (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (had : context.associatedData.length = 281)
    (state : AdaptiveCtxCanonical.CanonicalState) (fresh : nonce ∉ state.ctx.usedNonces) :
    (fun result => (result.1, result.2.ctx.cache)) <$>
      (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key)
        (selected writer nonce sequence context)).run state =
      (fun result => (SealResult.completed result.1, result.2)) <$>
        (simulateQ ctxRandomOracle (simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
          (RawCtxSourceSeal.sealInput (selectedNative key nonce sequence context)))).run state.ctx.cache := by
  rw [selected_fresh decode c key writer nonce sequence context had state fresh,
    RawCtxCanonicalSeal.sealInput_typed c writer (selectedNative key nonce sequence context) had,
    (selected_input key nonce sequence context had).1,
    (selected_input key nonce sequence context had).2]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
    afterSeal, CtxHandlerState.addSeal, RawCtxCanonicalSeal.recordFrame, selectedNative]

/-- Every completed selected inner seal records its nonce even when the original frame writer returns None. No failed-publication retry is silently treated as a first seal. -/
theorem selected_ledger (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (had : context.associatedData.length = 281)
    (state : AdaptiveCtxCanonical.CanonicalState) (fresh : nonce ∉ state.ctx.usedNonces)
    (result : SealResult × AdaptiveCtxCanonical.CanonicalState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key)
      (selected writer nonce sequence context)).run state)) :
    result.2.ctx.usedNonces = nonce :: state.ctx.usedNonces ∧
      result.2.rawAttempts = state.rawAttempts ∧
      result.2.ctx.successfulSeals.length = state.ctx.successfulSeals.length + 1 := by
  rw [selected_fresh decode c key writer nonce sequence context had state fresh] at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨record, _, equal⟩
  subst result
  simp [afterSeal, CtxHandlerState.addSeal, selectedInput]

set_option backward.isDefEq.respectTransparency false in
/-- Each reached valid-AD selected seal attempt costs one ordinary seal query, including a refused repeated nonce; it adds no public hash, raw verification or explicit uniform query. -/
theorem selected_bills (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext) :
    (selected writer nonce sequence context).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 ∧
      (selected writer nonce sequence context).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash 0 ∧
      (selected writer nonce sequence context).IsQueryBoundP IsRawQuery 0 ∧
      (selected writer nonce sequence context).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform 0 := by
  unfold selected
  split
  · simp [AdaptiveCtxQueryBounds.SourceSeal,
      AdaptiveCtxQueryBounds.SourceHash, IsRawQuery, AdaptiveCtxQueryBounds.SourceUniform]
  · exact ⟨by trivial, by trivial, by trivial, by trivial⟩

/-- Invalid source AD preserves the actual rejection without invoking the selected oracle or changing any challenger field. -/
theorem selected_invalid (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) (invalid : context.associatedData.length ≠ 281)
    (state : AdaptiveCtxCanonical.CanonicalState) :
    (simulateQ (AdaptiveCtxCanonical.canonicalImpl decode c key)
      (selected writer nonce sequence context)).run state = pure (.completed none, state) ∧
      simulateQ (RawCtxCanonicalSeal.romAdapter c writer)
        (RawCtxSourceSeal.sealInput (selectedNative key nonce sequence context)) = pure none := by
  constructor
  · simp only [selected, dite_eq_right invalid, simulateQ_pure, StateT.run_pure]
  · exact RawCtxCanonicalSeal.sealInput_invalid c writer _ invalid

end BeaconcryptCore.Computational.RawCtxSelectedMessageSealing

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hash_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hash_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hashLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hashLift_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hashLift_no_uniform' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.hashLift_no_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.known_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_input

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.canonical_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.canonical_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_repeat

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_ledger

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageSealing.selected_invalid
