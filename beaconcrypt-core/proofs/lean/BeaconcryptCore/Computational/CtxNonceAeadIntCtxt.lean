import BeaconcryptCore.Computational.CtxHonestTagSampling
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Modified nonce-AEAD INT-CTXT reduction for CTX

This module defines the nonce-rejecting associated-data AEAD integrity game used by the modified-CTX reduction.
It projects the retained `C || T` portion of every successful CTX seal and target into that primitive game and constructs the corresponding forgery adversary.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxNonceAeadIntCtxt

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling

/-- One nonce-respecting modified nonce-AEAD encryption request. -/
structure ModifiedNonceAeadSealInput where
  nonce : CtxNonce
  ad : Pqxdh.Bytes
  plaintext : Pqxdh.Bytes
deriving DecidableEq

/-- Detached modified nonce-AEAD ciphertext with the protocol tag width. -/
structure ModifiedNonceAeadCiphertext where
  body : Pqxdh.Bytes
  tag : Pqxdh.Bytes
  tagLength : tag.length = 16
deriving DecidableEq

/-- One successful primitive encryption query and its exact response. -/
structure ModifiedNonceAeadSuccessfulSeal where
  input : ModifiedNonceAeadSealInput
  ciphertext : ModifiedNonceAeadCiphertext
deriving DecidableEq

/-- A candidate strong ciphertext forgery. -/
structure ModifiedNonceAeadForgery where
  nonce : CtxNonce
  ad : Pqxdh.Bytes
  ciphertext : ModifiedNonceAeadCiphertext
deriving DecidableEq

/-- Nonce-rejecting chosen-plaintext primitive encryption interface. -/
abbrev ModifiedNonceAeadSealSpec :=
  (ModifiedNonceAeadSealInput →ₒ Option ModifiedNonceAeadCiphertext)

/-- Primitive forgers receive private randomness and the encryption interface. -/
abbrev ModifiedNonceAeadAdversarySpec :=
  unifSpec + ModifiedNonceAeadSealSpec

/-- An adaptive modified nonce-AEAD ciphertext forger. -/
structure ModifiedNonceAeadAdversary where
  main : OracleComp ModifiedNonceAeadAdversarySpec ModifiedNonceAeadForgery

/-- Private nonce and successful-encryption history of the primitive challenger. -/
structure ModifiedNonceAeadHandlerState where
  usedNonces : List CtxNonce
  successfulSeals : List ModifiedNonceAeadSuccessfulSeal

/-- Empty primitive encryption history. -/
def emptyModifiedNonceAeadHandlerState : ModifiedNonceAeadHandlerState :=
  ⟨[], []⟩

/-- Record one successful primitive encryption response. -/
def ModifiedNonceAeadHandlerState.addSeal
    (state : ModifiedNonceAeadHandlerState)
    (entry : ModifiedNonceAeadSuccessfulSeal) :
    ModifiedNonceAeadHandlerState :=
  ⟨entry.input.nonce :: state.usedNonces,
    entry :: state.successfulSeals⟩

/-- The primitive challenger rejects reused nonces and otherwise returns `aeadSeal`. -/
noncomputable def modifiedNonceAeadSealOracle
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ModifiedNonceAeadSealSpec
      (StateT ModifiedNonceAeadHandlerState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else
      let base := c.aeadSeal key.toList input.nonce.toList
        input.ad input.plaintext
      let ciphertext : ModifiedNonceAeadCiphertext :=
        ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _⟩
      pure (some ciphertext,
        state.addSeal ⟨input, ciphertext⟩)

/-- Run equation for one primitive sealing call. -/
theorem modifiedNonceAeadSealOracle_run
    (c : Pqxdh.Crypto) (key : CtxKey)
    (input : ModifiedNonceAeadSealInput)
    (state : ModifiedNonceAeadHandlerState) :
    (modifiedNonceAeadSealOracle c key input).run state =
      if input.nonce ∈ state.usedNonces then
        pure (none, state)
      else
        let base := c.aeadSeal key.toList input.nonce.toList
          input.ad input.plaintext
        let ciphertext : ModifiedNonceAeadCiphertext :=
          ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _⟩
        pure (some ciphertext,
          state.addSeal ⟨input, ciphertext⟩) := by
  rfl

/-- Full primitive challenger: transparent randomness plus nonce-rejecting encryption. -/
noncomputable def modifiedNonceAeadINTCTXTImpl
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ModifiedNonceAeadAdversarySpec
      (StateT ModifiedNonceAeadHandlerState ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ModifiedNonceAeadHandlerState ProbComp) +
    modifiedNonceAeadSealOracle c key

/-- A primitive forgery is fresh when its complete nonce/AD/ciphertext tuple was never returned. -/
def ModifiedNonceAeadFresh
    (history : List ModifiedNonceAeadSuccessfulSeal)
    (forgery : ModifiedNonceAeadForgery) : Prop :=
  ∀ entry ∈ history,
    ¬(forgery.nonce = entry.input.nonce ∧
      forgery.ad = entry.input.ad ∧
      forgery.ciphertext = entry.ciphertext)

/-- Primitive transcript immediately before the local final opening. -/
structure ModifiedNonceAeadBeforeVerify where
  key : CtxKey
  forgery : ModifiedNonceAeadForgery
  successfulSeals : List ModifiedNonceAeadSuccessfulSeal
  usedNonces : List CtxNonce

/-- Modified nonce-AEAD INT-CTXT winning event. -/
def ModifiedNonceAeadINTCTXTWin (c : Pqxdh.Crypto)
    (before : ModifiedNonceAeadBeforeVerify) : Prop :=
  c.aeadOpen before.key.toList before.forgery.nonce.toList
      before.forgery.ad before.forgery.ciphertext.body
      before.forgery.ciphertext.tag ≠ none ∧
    ModifiedNonceAeadFresh before.successfulSeals before.forgery

/-- Fixed-key primitive transcript immediately before final opening. -/
noncomputable def modifiedNonceAeadINTCTXTBeforeVerifyInner
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary)
    (key : CtxKey) : ProbComp ModifiedNonceAeadBeforeVerify := do
  let (forgery, state) ←
    (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      adversary.main).run emptyModifiedNonceAeadHandlerState
  pure ⟨key, forgery, state.successfulSeals, state.usedNonces⟩

/-- Uniform-key modified nonce-AEAD INT-CTXT experiment. -/
noncomputable def modifiedNonceAeadINTCTXTGame
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary) :
    ProbComp ModifiedNonceAeadBeforeVerify := do
  let key ← $ᵗ CtxKey
  modifiedNonceAeadINTCTXTBeforeVerifyInner c adversary key

/-- Modified nonce-AEAD INT-CTXT advantage. -/
noncomputable def modifiedNonceAeadINTCTXTAdvantage
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary) : ℝ≥0∞ :=
  Pr[ModifiedNonceAeadINTCTXTWin c |
    modifiedNonceAeadINTCTXTGame c adversary]

/-- Project a CTX sealing request to its primitive retained-base request. -/
def CtxSealInput.toModifiedNonceAeadSealInput
    (input : CtxSealInput) : ModifiedNonceAeadSealInput :=
  ⟨input.nonce, input.context.ad.bytes, input.plaintext⟩

@[simp] theorem toModifiedNonceAeadSealInput_nonce
    (input : CtxSealInput) :
    (CtxSealInput.toModifiedNonceAeadSealInput input).nonce = input.nonce :=
  rfl

@[simp] theorem toModifiedNonceAeadSealInput_ad
    (input : CtxSealInput) :
    (CtxSealInput.toModifiedNonceAeadSealInput input).ad =
      input.context.ad.bytes :=
  rfl

@[simp] theorem toModifiedNonceAeadSealInput_plaintext
    (input : CtxSealInput) :
    (CtxSealInput.toModifiedNonceAeadSealInput input).plaintext =
      input.plaintext :=
  rfl

/-- Primitive sealing run equation specialized to a projected CTX request. -/
theorem modifiedNonceAeadSealOracle_run_ctx
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : ModifiedNonceAeadHandlerState) :
    (modifiedNonceAeadSealOracle c key
      (CtxSealInput.toModifiedNonceAeadSealInput input)).run state =
      if input.nonce ∈ state.usedNonces then
        pure (none, state)
      else
        let base := c.aeadSeal key.toList input.nonce.toList
          input.context.ad.bytes input.plaintext
        let ciphertext : ModifiedNonceAeadCiphertext :=
          ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _⟩
        pure (some ciphertext,
          state.addSeal
            ⟨CtxSealInput.toModifiedNonceAeadSealInput input,
              ciphertext⟩) := by
  rw [modifiedNonceAeadSealOracle_run]
  simp only [toModifiedNonceAeadSealInput_nonce,
    toModifiedNonceAeadSealInput_ad,
    toModifiedNonceAeadSealInput_plaintext]

/-- Project a CTX record to the retained detached primitive ciphertext. -/
def CtxRomRecord.toModifiedNonceAeadCiphertext
    (record : CtxRomRecord) : ModifiedNonceAeadCiphertext :=
  ⟨record.body, record.tag, record.tagLength⟩

/-- Project a successful CTX seal to its primitive encryption history entry. -/
def CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal
    (entry : CtxSuccessfulSeal) : ModifiedNonceAeadSuccessfulSeal :=
  ⟨CtxSealInput.toModifiedNonceAeadSealInput entry.input,
    CtxRomRecord.toModifiedNonceAeadCiphertext entry.record⟩

/-- Project a CTX target to its retained-base primitive forgery. -/
def CtxAliasTarget.toModifiedNonceAeadForgery
    (target : CtxAliasTarget) : ModifiedNonceAeadForgery :=
  ⟨target.nonce, target.context.ad.bytes,
    CtxRomRecord.toModifiedNonceAeadCiphertext target.record⟩

/-- Project the complete CTX pre-verification transcript to the primitive transcript. -/
def ctxBeforeVerifyToModifiedNonceAead
    (before : CtxBeforeVerify) : ModifiedNonceAeadBeforeVerify :=
  ⟨before.key, CtxAliasTarget.toModifiedNonceAeadForgery before.target,
    before.successfulSeals.map
      CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal,
    before.usedNonces⟩

/-- Fresh accepted retained-base branch of the explicit independent-tag CTX game. -/
def CtxFreshAcceptedRetainedBase (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) : Prop :=
  c.aeadOpen before.key.toList before.target.nonce.toList
      before.target.context.ad.bytes before.target.record.body
      before.target.record.tag = some before.target.claimedPlaintext ∧
    ModifiedNonceAeadFresh
      (before.successfulSeals.map
        CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal)
      (CtxAliasTarget.toModifiedNonceAeadForgery before.target)

/-- Every fresh accepted retained CTX base is a primitive INT-CTXT win. -/
theorem ctxFreshAcceptedRetainedBase_implies_modifiedNonceAeadINTCTXTWin
    (c : Pqxdh.Crypto) (before : CtxBeforeVerify)
    (hwin : CtxFreshAcceptedRetainedBase c before) :
    ModifiedNonceAeadINTCTXTWin c
      (ctxBeforeVerifyToModifiedNonceAead before) := by
  refine ⟨?_, hwin.2⟩
  change c.aeadOpen before.key.toList before.target.nonce.toList
      before.target.context.ad.bytes before.target.record.body
      before.target.record.tag ≠ none
  rw [hwin.1]
  simp

/-- Project a direct-sampling CTX handler state to the primitive challenger history. -/
def ctxIndependentTagStateToModifiedNonceAead
    (state : CtxIndependentTagState) : ModifiedNonceAeadHandlerState :=
  ⟨state.usedNonces,
    state.successfulSeals.map
      CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal⟩

/-- Lift one private uniform CTX digest into the primitive adversary interface. -/
noncomputable def modifiedNonceAeadDigest :
    OracleComp ModifiedNonceAeadAdversarySpec CtxDigest :=
  OracleComp.liftComp ($ᵗ CtxDigest) ModifiedNonceAeadAdversarySpec

/-- Make one primitive encryption query through the right-hand interface. -/
def queryModifiedNonceAeadSeal (input : ModifiedNonceAeadSealInput) :
    OracleComp ModifiedNonceAeadAdversarySpec
      (Option ModifiedNonceAeadCiphertext) :=
  liftM (ModifiedNonceAeadAdversarySpec.query (.inr input))

/-- Simulate one public ROM call without making a primitive encryption query. -/
noncomputable def ctxRetainedBasePublicOracle :
    QueryImpl CtxRO
      (StateT CtxIndependentTagState
        (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun query state =>
    OracleComp.liftComp
      ((ctxIndependentPublicOracle query).run state)
      ModifiedNonceAeadAdversarySpec

/-- Simulate one CTX seal using exactly one primitive encryption query when its nonce is fresh. -/
noncomputable def ctxRetainedBaseSealOracle :
    QueryImpl CtxSealSpec
      (StateT CtxIndependentTagState
        (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let primitiveInput :=
        CtxSealInput.toModifiedNonceAeadSealInput input
      let base ← queryModifiedNonceAeadSeal primitiveInput
      match base with
      | none => pure (none, state)
      | some ciphertext => do
          let commit ← modifiedNonceAeadDigest
          let suffix := outerSuffix input.nonce input.context ciphertext.tag
          let cache := cacheSuffix state.cache suffix commit
          let record : CtxRomRecord :=
            ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, commit⟩
          pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- CTX interface implemented inside the retained-base primitive forger. -/
noncomputable def ctxRetainedBaseReductionImpl :
    QueryImpl CtxAdversarySpec
      (StateT CtxIndependentTagState
        (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  ctxRetainedBasePublicOracle + ctxRetainedBaseSealOracle

/-- Retained-base reduction from a CTX adversary to a primitive ciphertext forger. -/
noncomputable def ctxRetainedBaseReduction
    (adversary : CtxAdversary) : ModifiedNonceAeadAdversary where
  main := do
    let (target, _) ←
      (simulateQ ctxRetainedBaseReductionImpl adversary.main).run
        emptyCtxIndependentTagState
    pure (CtxAliasTarget.toModifiedNonceAeadForgery target)

/-- Interpret the reduction's primitive calls and flatten both handler states. -/
noncomputable def ctxRetainedBaseCombinedImpl
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec
      (StateT (CtxIndependentTagState × ModifiedNonceAeadHandlerState)
        ProbComp) :=
  ((modifiedNonceAeadINTCTXTImpl c key).mapStateTBase
    ctxRetainedBaseReductionImpl).flattenStateT

/-- Identify source CTX seal queries for exact reduction accounting. -/
def IsCtxSealQuery : CtxAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsCtxSealQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Identify primitive seal queries made by the retained-base forger. -/
def IsModifiedNonceAeadSealQuery :
    ModifiedNonceAeadAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsModifiedNonceAeadSealQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Primitive-side shorthand for a sealing-query bound. -/
def ModifiedNonceAeadAdversary.MakesAtMostSealQueries
    (adversary : ModifiedNonceAeadAdversary) (qE : ℕ) : Prop :=
  adversary.main.IsQueryBoundP IsModifiedNonceAeadSealQuery qE

/-- Lifted private randomness makes no primitive seal query. -/
theorem liftProbComp_no_modifiedNonceAeadSealQueries
    {α : Type} (oa : ProbComp α) :
    (OracleComp.liftComp oa ModifiedNonceAeadAdversarySpec).IsQueryBoundP
      IsModifiedNonceAeadSealQuery 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind query rest ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM (ModifiedNonceAeadAdversarySpec.query (.inl query)) >>= fun response =>
          OracleComp.liftComp (rest response) ModifiedNonceAeadAdversarySpec)).IsQueryBoundP
        IsModifiedNonceAeadSealQuery 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨by simp [IsModifiedNonceAeadSealQuery], fun response => by
        simpa [IsModifiedNonceAeadSealQuery] using ih response⟩

/-- Each source seal step makes at most one primitive seal query; public steps make none. -/
theorem ctxRetainedBaseReductionImpl_seal_query_bound_step
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState) :
    ((ctxRetainedBaseReductionImpl query).run state).IsQueryBoundP
      IsModifiedNonceAeadSealQuery
      (if IsCtxSealQuery query then 1 else 0) := by
  rcases query with query | input
  · simp only [ctxRetainedBaseReductionImpl, QueryImpl.add_apply_inl,
      IsCtxSealQuery, if_false]
    exact liftProbComp_no_modifiedNonceAeadSealQueries
      ((ctxIndependentPublicOracle query).run state)
  · by_cases hused : input.nonce ∈ state.usedNonces
    · simp only [ctxRetainedBaseReductionImpl, QueryImpl.add_apply_inr,
        IsCtxSealQuery, if_true]
      unfold ctxRetainedBaseSealOracle
      simp [StateT.run, hused]
    · simp only [ctxRetainedBaseReductionImpl, QueryImpl.add_apply_inr,
        ctxRetainedBaseSealOracle, IsCtxSealQuery, if_true, hused,
        if_false, StateT.run]
      unfold queryModifiedNonceAeadSeal
      refine OracleComp.isQueryBoundP_bind (n := 1) (m := 0) ?_ ?_
      · exact (OracleComp.isQueryBoundP_query_iff
          (spec := ModifiedNonceAeadAdversarySpec)
          (p := IsModifiedNonceAeadSealQuery)
          (.inr (CtxSealInput.toModifiedNonceAeadSealInput input)) 1).2
            (fun _ => by omega)
      · intro base _
        cases base with
        | none => simp
        | some ciphertext =>
            exact (OracleComp.isQueryBoundP_map_iff
              modifiedNonceAeadDigest _ 0).mpr
                (liftProbComp_no_modifiedNonceAeadSealQueries
                  ($ᵗ CtxDigest))

/-- The retained-base forger preserves every source sealing-query bound. -/
theorem ctxRetainedBaseReduction_seal_query_bound
    (adversary : CtxAdversary) (qE : ℕ)
    (hbound : adversary.main.IsQueryBoundP IsCtxSealQuery qE) :
    (ctxRetainedBaseReduction adversary).MakesAtMostSealQueries qE := by
  unfold ModifiedNonceAeadAdversary.MakesAtMostSealQueries
    ctxRetainedBaseReduction
  simp only [bind_pure_comp]
  rw [OracleComp.isQueryBoundP_map_iff]
  exact hbound.simulateQ_run_StateT_of_step
    ctxRetainedBaseReductionImpl_seal_query_bound_step
    emptyCtxIndependentTagState

/-- Interpreting a reduction-side primitive query invokes the primitive sealing oracle. -/
theorem simulateQ_queryModifiedNonceAeadSeal
    (c : Pqxdh.Crypto) (key : CtxKey)
    (input : ModifiedNonceAeadSealInput) :
    simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        (queryModifiedNonceAeadSeal input) =
      modifiedNonceAeadSealOracle c key input := by
  unfold modifiedNonceAeadINTCTXTImpl queryModifiedNonceAeadSeal
  simp

/-- Interpreting reduction-side digest sampling preserves the primitive state. -/
theorem simulateQ_modifiedNonceAeadDigest
    (c : Pqxdh.Crypto) (key : CtxKey) :
    simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        modifiedNonceAeadDigest =
      (liftM ($ᵗ CtxDigest) :
        StateT ModifiedNonceAeadHandlerState ProbComp CtxDigest) := by
  unfold modifiedNonceAeadINTCTXTImpl modifiedNonceAeadDigest
  rw [QueryImpl.simulateQ_add_liftComp_left]
  simp

/-- Running a mapped lifted digest sample leaves an arbitrary state unchanged. -/
theorem map_lift_ctxDigest_run {σ β : Type}
    (f : CtxDigest → β) (state : σ) :
    ((f <$> (liftM ($ᵗ CtxDigest) :
      StateT σ ProbComp CtxDigest))).run state =
      (fun digest => (f digest, state)) <$> ($ᵗ CtxDigest) := by
  simp [StateT.run_map, StateT.run_monadLift,
    bind_pure_comp, Functor.map_map]

/-- Application-normal-form companion of `map_lift_ctxDigest_run`. -/
theorem map_lift_ctxDigest_apply {σ β : Type}
    (f : CtxDigest → β) (state : σ) :
    ((f <$> (liftM ($ᵗ CtxDigest) :
      StateT σ ProbComp CtxDigest)) : StateT σ ProbComp β) state =
      (fun digest => (f digest, state)) <$> ($ᵗ CtxDigest) := by
  exact map_lift_ctxDigest_run f state

/-- Public CTX queries leave the primitive state unchanged under the exact projection. -/
theorem ctxRetainedBasePublicOracle_projection
    (c : Pqxdh.Crypto) (key : CtxKey) (query : CtxRO.Domain)
    (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxIndependentPublicOracle query).run state =
      (ctxRetainedBaseCombinedImpl c key (.inl query)).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  unfold ctxRetainedBaseCombinedImpl ctxRetainedBaseReductionImpl
    ctxRetainedBasePublicOracle
  change _ =
    (fun result => (result.1.1, result.1.2, result.2)) <$>
      (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        (liftM ((ctxIndependentPublicOracle query).run state))).run
          (ctxIndependentTagStateToModifiedNonceAead state)
  unfold modifiedNonceAeadINTCTXTImpl
  rw [QueryImpl.simulateQ_add_liftM_left]
  unfold ctxIndependentPublicOracle
  rw [simulateQ_liftTarget]
  rw [simulateQ_ofLift_eq_self]
  rw [OracleComp.liftM_run_StateT]
  simp only [bind_pure_comp]
  simp only [StateT.run, Functor.map_map]
  change
    (fun result : CtxDigest × CtxRO.QueryCache =>
      let next := state.addPublic query.2
        { state.cache with publicCache := result.2 }
      (result.1, next,
        ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxRandomOracle query).run state.cache.publicCache =
      (fun result : CtxDigest × CtxRO.QueryCache =>
        let next := state.addPublic query.2
          { state.cache with publicCache := result.2 }
        (result.1, next,
          ctxIndependentTagStateToModifiedNonceAead state)) <$>
        (ctxRandomOracle query).run state.cache.publicCache
  congr 1

/-- A direct-sampling CTX seal is exactly one primitive seal followed by one private digest. -/
theorem ctxRetainedBaseSealOracle_projection
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxDirectSampleKeyFreeSealOracle c key input).run state =
      (ctxRetainedBaseCombinedImpl c key (.inr input)).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  unfold ctxRetainedBaseCombinedImpl ctxRetainedBaseReductionImpl
  change _ =
    (fun result => (result.1.1, result.1.2, result.2)) <$>
      (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        ((ctxRetainedBaseSealOracle input).run state)).run
          (ctxIndependentTagStateToModifiedNonceAead state)
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle
      ctxRetainedBaseSealOracle
    simp [StateT.run, hused]
    rfl
  · unfold ctxDirectSampleKeyFreeSealOracle
      ctxRetainedBaseSealOracle
    simp only [StateT.run, hused, if_false]
    rw [simulateQ_bind, simulateQ_queryModifiedNonceAeadSeal]
    change _ = _ <$>
      ((modifiedNonceAeadSealOracle c key
        (CtxSealInput.toModifiedNonceAeadSealInput input)).run
          (ctxIndependentTagStateToModifiedNonceAead state) >>= fun result => _)
    rw [modifiedNonceAeadSealOracle_run_ctx]
    simp only [ctxIndependentTagStateToModifiedNonceAead,
      hused, if_false, pure_bind]
    rw [simulateQ_bind, simulateQ_modifiedNonceAeadDigest]
    simp only [simulateQ_pure]
    simp only [bind_pure_comp, Functor.map_map]
    rw [map_lift_ctxDigest_apply]
    rw [Functor.map_map]
    apply congrArg (fun f : CtxDigest →
        Option CtxRomRecord ×
          (CtxIndependentTagState × ModifiedNonceAeadHandlerState) =>
      f <$> ($ᵗ CtxDigest))
    funext commit
    rfl

/-- Every direct-sampling CTX query projects to the flattened retained-base reduction. -/
theorem ctxRetainedBaseCombinedImpl_projection
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxDirectSampleIndependentTagImpl c key query).run state =
      (ctxRetainedBaseCombinedImpl c key query).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  rcases query with query | input
  · exact ctxRetainedBasePublicOracle_projection c key query state
  · exact ctxRetainedBaseSealOracle_projection c key input state

/-- The complete adaptive reduction run is the exact projected direct-sampling CTX run. -/
theorem ctxRetainedBaseCombinedImpl_run_projection
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Prod.map id
        (fun state =>
          (state, ctxIndependentTagStateToModifiedNonceAead state)) <$>
        (simulateQ (ctxDirectSampleIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState =
      (simulateQ (ctxRetainedBaseCombinedImpl c key)
        adversary.main).run
          (emptyCtxIndependentTagState,
            emptyModifiedNonceAeadHandlerState) := by
  simpa [ctxIndependentTagStateToModifiedNonceAead,
    emptyCtxIndependentTagState,
    emptyModifiedNonceAeadHandlerState] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ctxDirectSampleIndependentTagImpl c key)
      (ctxRetainedBaseCombinedImpl c key)
      (fun state =>
        (state, ctxIndependentTagStateToModifiedNonceAead state))
      (ctxRetainedBaseCombinedImpl_projection c key)
      adversary.main emptyCtxIndependentTagState

/-- Interpreting the reduction's nested CTX run yields the exact direct CTX transcript. -/
theorem ctxRetainedBaseNestedRun_eq_direct
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      ((simulateQ ctxRetainedBaseReductionImpl adversary.main).run
        emptyCtxIndependentTagState)).run
        emptyModifiedNonceAeadHandlerState =
      (fun result : CtxAliasTarget × CtxIndependentTagState =>
        ((result.1, result.2),
          ctxIndependentTagStateToModifiedNonceAead result.2)) <$>
        (simulateQ (ctxDirectSampleIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState := by
  calc
    _ = (fun result : CtxAliasTarget ×
          (CtxIndependentTagState × ModifiedNonceAeadHandlerState) =>
          ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (ctxRetainedBaseCombinedImpl c key)
          adversary.main).run
            (emptyCtxIndependentTagState,
              emptyModifiedNonceAeadHandlerState) :=
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
        (modifiedNonceAeadINTCTXTImpl c key)
        ctxRetainedBaseReductionImpl adversary.main
        emptyCtxIndependentTagState
        emptyModifiedNonceAeadHandlerState
    _ = _ := by
      rw [← ctxRetainedBaseCombinedImpl_run_projection c key adversary]
      simp only [Functor.map_map]
      apply congrArg (fun f :
          (CtxAliasTarget × CtxIndependentTagState) →
            ((CtxAliasTarget × CtxIndependentTagState) ×
              ModifiedNonceAeadHandlerState) =>
        f <$> (simulateQ (ctxDirectSampleIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState)
      funext result
      rfl

/-- The primitive challenger sees exactly the retained target and projected seal history. -/
theorem ctxRetainedBaseReduction_run_eq_direct
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (ctxRetainedBaseReduction adversary).main).run
        emptyModifiedNonceAeadHandlerState =
      (fun result : CtxAliasTarget × CtxIndependentTagState =>
        (CtxAliasTarget.toModifiedNonceAeadForgery result.1,
          ctxIndependentTagStateToModifiedNonceAead result.2)) <$>
        (simulateQ (ctxDirectSampleIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState := by
  unfold ctxRetainedBaseReduction
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure]
  rw [ctxRetainedBaseNestedRun_eq_direct]
  simp only [bind_pure_comp, Functor.map_map]

/-- At fixed key, the primitive transcript is exactly the retained direct CTX transcript. -/
theorem modifiedNonceAeadINTCTXTBeforeVerifyInner_reduction_eq_direct
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    modifiedNonceAeadINTCTXTBeforeVerifyInner c
        (ctxRetainedBaseReduction adversary) key =
      (fun result : CtxBeforeVerify × SplitCache =>
        ctxBeforeVerifyToModifiedNonceAead result.1) <$>
        ctxDirectSampleIndependentTagBeforeVerifyInner c adversary key := by
  unfold modifiedNonceAeadINTCTXTBeforeVerifyInner
    ctxDirectSampleIndependentTagBeforeVerifyInner
  rw [ctxRetainedBaseReduction_run_eq_direct]
  simp only [bind_pure_comp, Functor.map_map]
  apply congrArg (fun f :
      (CtxAliasTarget × CtxIndependentTagState) →
        ModifiedNonceAeadBeforeVerify =>
    f <$> (simulateQ (ctxDirectSampleIndependentTagImpl c key)
      adversary.main).run emptyCtxIndependentTagState)
  funext result
  rfl

/-- The complete primitive reduction game is the mapped direct independent-tag game. -/
theorem modifiedNonceAeadINTCTXTGame_reduction_eq_direct
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    modifiedNonceAeadINTCTXTGame c
        (ctxRetainedBaseReduction adversary) =
      (fun result : CtxBeforeVerify × SplitCache =>
        ctxBeforeVerifyToModifiedNonceAead result.1) <$>
        ctxDirectSampleIndependentTagGame c adversary := by
  unfold modifiedNonceAeadINTCTXTGame
    ctxDirectSampleIndependentTagGame
  simp only [map_bind]
  apply bind_congr
  intro key
  exact modifiedNonceAeadINTCTXTBeforeVerifyInner_reduction_eq_direct
    c key adversary

/-- Every fresh retained-base acceptance is charged to the constructed INT-CTXT forger. -/
theorem ctxFreshAcceptedRetainedBaseProbability_le_intCtxtAdvantage
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[fun result : CtxBeforeVerify × SplitCache =>
        CtxFreshAcceptedRetainedBase c result.1 |
      ctxDirectSampleIndependentTagGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
        (ctxRetainedBaseReduction adversary) := by
  unfold modifiedNonceAeadINTCTXTAdvantage
  rw [modifiedNonceAeadINTCTXTGame_reduction_eq_direct,
    probEvent_map]
  apply probEvent_mono''
  intro result hretained
  exact ctxFreshAcceptedRetainedBase_implies_modifiedNonceAeadINTCTXTWin
    c result.1 hretained

end BeaconcryptCore.Computational.CtxNonceAeadIntCtxt
