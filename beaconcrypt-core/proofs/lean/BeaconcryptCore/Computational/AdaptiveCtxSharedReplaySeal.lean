import BeaconcryptCore.Computational.AdaptiveCtxSharedReplay
import BeaconcryptCore.Computational.CtxNonceAeadIntCtxt

/-!
The key-free local replay compiler delegates actual ordinary sealing and retains private suffix dictionaries, nonce and seal histories, original optional replies and failed lookup effects. The complete real interpreter reconstructs the ordinary history with both actual nonce gates aligned.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive
open AdaptiveCtxSharedHash (HashSpec)
open AdaptiveCtxSharedReplay

abbrev SealSpec := HashSpec + ModifiedNonceAeadSealSpec

def forwardHash : QueryImpl HashSpec (OracleComp SealSpec) :=
  fun query => SealSpec.query (.inl query)

def baseState (entry : Local) : ModifiedNonceAeadHandlerState :=
  ⟨entry.1.usedNonces,
    entry.1.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal⟩

noncomputable def compiledSeal (input : CtxSealInput) (entry : Local) :
    OracleComp SealSpec (Option CtxRomRecord × Local) := do
  if input.nonce ∈ entry.1.usedNonces then pure (none, entry)
  else
    let base ← SealSpec.query (.inr (CtxSealInput.toModifiedNonceAeadSealInput input))
    match base with
    | none => pure (none, entry)
    | some base =>
      let commitment ← simulateQ forwardHash (localPrivate (outerSuffix input.nonce input.context base.tag) entry)
      let record : CtxRomRecord := ⟨base.body, base.tag, base.tagLength, commitment.1⟩
      pure (some record, { commitment.2.1 with
        usedNonces := input.nonce :: commitment.2.1.usedNonces,
        successfulSeals := ⟨input, record⟩ :: commitment.2.1.successfulSeals }, commitment.2.2)

noncomputable def realImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl SealSpec (StateT ModifiedNonceAeadHandlerState (OracleComp HashSpec)) :=
  fun query state => match query with
  | .inl hash => do
    let answer ← HashSpec.query hash
    pure (answer, state)
  | .inr input =>
    OracleComp.liftComp ((modifiedNonceAeadSealOracle c key input).run state) HashSpec

theorem real_hash (c : Pqxdh.Crypto) (key : CtxKey) (query : HashSpec.Domain)
    (state : ModifiedNonceAeadHandlerState) :
    (realImpl c key (.inl query)).run state = (do
      let answer ← HashSpec.query query
      pure (answer, state)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem forward_hash {Result : Type} (c : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp HashSpec Result) (state : ModifiedNonceAeadHandlerState) :
    (simulateQ (realImpl c key) (simulateQ forwardHash work)).run state =
      (fun answer => (answer, state)) <$> work := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
    simp only [forwardHash, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind]
    simp only [realImpl, StateT.run, bind_assoc, pure_bind]
    exact bind_congr (fun answer => ih answer state)

set_option backward.isDefEq.respectTransparency false in
theorem seal_complete (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (entry : Local) :
    (simulateQ (realImpl c key) (compiledSeal input entry)).run (baseState entry) =
      (fun result => (result, baseState result.2)) <$> localSeal c key input entry := by
  by_cases used : input.nonce ∈ entry.1.usedNonces
  · simp only [compiledSeal, localSeal, used, if_true, simulateQ_pure, StateT.run_pure, map_pure]
  · simp only [compiledSeal, localSeal, used, if_false, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [realImpl, StateT.run, modifiedNonceAeadSealOracle, baseState,
      CtxSealInput.toModifiedNonceAeadSealInput, used, if_false, OracleComp.liftComp_pure, pure_bind]
    change (simulateQ (realImpl c key) _).run _ = _
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, forward_hash, Functor.map_map]
    simp only [localPrivate, bind_pure_comp, Functor.map_map, List.map_cons,
      ModifiedNonceAeadHandlerState.addSeal, CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal,
      CtxSealInput.toModifiedNonceAeadSealInput, CtxRomRecord.toModifiedNonceAeadCiphertext]

noncomputable def compiledImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT Local (OracleComp SealSpec)) := fun query entry =>
  match query with
  | .inl (.inl coin) => do
    let answer ← SealSpec.query (.inl (.inl coin))
    pure (answer, entry)
  | .inl (.inr (.inl hash)) => do
    let answer ← SealSpec.query (.inl (.inr hash))
    pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2)
  | .inl (.inr (.inr input)) => compiledSeal input entry
  | .inr raw => simulateQ forwardHash (localRaw decode raw entry)

set_option backward.isDefEq.respectTransparency false in
theorem local_complete (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : Local) :
    (simulateQ (realImpl c key) ((compiledImpl decode query).run entry)).run (baseState entry) =
      (fun result => (result, baseState result.2)) <$> (localImpl decode c key query).run entry := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      change (simulateQ (realImpl c key) (do
        let answer ← SealSpec.query (.inl (.inl coin))
        pure (answer, entry))).run _ = _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, real_hash,
        simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      simp only [localImpl, StateT.run, bind_pure_comp, Functor.map_map]
    | inr query =>
      cases query with
      | inl hash =>
        change (simulateQ (realImpl c key) (do
          let answer ← SealSpec.query (.inl (.inr hash))
          pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2))).run _ = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, real_hash,
          simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
        simp only [localImpl, StateT.run, bind_pure_comp, Functor.map_map, baseState]
      | inr input => exact seal_complete c key input entry
  | inr raw =>
    change (simulateQ (realImpl c key) (simulateQ forwardHash (localRaw decode raw entry))).run _ = _
    rw [forward_hash]
    cases parsed : decode raw <;>
      simp only [localImpl, StateT.run, localRaw, parsed, map_pure, localPrivate,
        bind_pure_comp, Functor.map_map, baseState]

def attach (entry : Local) : Local × ModifiedNonceAeadHandlerState := (entry, baseState entry)

noncomputable def linkedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT (Local × ModifiedNonceAeadHandlerState) (OracleComp HashSpec)) :=
  ((realImpl c key).mapStateTBase (compiledImpl decode)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
theorem linked_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : Local) :
    Prod.map id attach <$> (localImpl decode c key query).run entry =
      (linkedImpl decode c key query).run (attach entry) := by
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (realImpl c key) ((compiledImpl decode query).run entry)).run (baseState entry)
  rw [local_complete]
  simp only [Functor.map_map, Prod.map_def, id_eq, attach]

theorem linked_schedule (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (entry : Local) :
    Prod.map id attach <$> (simulateQ (localImpl decode c key) client).run entry =
      (simulateQ (linkedImpl decode c key) client).run (attach entry) :=
  map_run_simulateQ_eq_of_query_map_eq (localImpl decode c key) (linkedImpl decode c key)
    attach (linked_step decode c key) client entry

end BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.real_hash' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.real_hash

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.forward_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.forward_hash

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.seal_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.seal_complete

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.local_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.local_complete

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplaySeal.linked_schedule
