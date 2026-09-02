import BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation

/-!
# Computational privacy of modified CTX

This module gives the confidentiality half of the modified-CTX component a bounded Boolean game.
The real experiment samples one uniform 256-bit CTX key and exposes the canonical shared lazy random oracle together with nonce-respecting sealing.
The ideal experiment keeps the public lazy random oracle and nonce-reuse leakage, but replaces every fresh record by an independently sampled length-matched body, 16-byte base tag, and 64-byte outer commitment.

The proof is deliberately component-local.
ProVerif remains responsible for protocol schedules, state, secrecy queries, and correspondence arguments.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxComputationalPrivacy

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling CtxNonceAeadIntCtxt CtxNonceAeadIndDollar
  CtxNonceAeadIndDollarValidation

/-- A Boolean CTX privacy adversary with separate public-ROM and sealing-query bounds. -/
structure CtxPrivacyAdversary (qH qE : ℕ) where
  /-- Adaptive public-ROM and nonce-respecting chosen-plaintext computation. -/
  main : OracleComp CtxAdversarySpec Bool
  /-- At most `qH` public random-oracle queries are made. -/
  publicQueryBound : main.IsQueryBoundP IsCtxPublicQuery qH
  /-- At most `qE` chosen-plaintext sealing queries are made. -/
  sealQueryBound : main.IsQueryBoundP IsCtxSealQuery qE

/-- Fixed-key real privacy experiment over the canonical shared lazy random oracle. -/
noncomputable def ctxPrivacyRealExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let result ←
    (simulateQ (ctxAdversaryImpl c key) adversary.main).run
      emptyCtxHandlerState
  pure result.1

/-- Real modified-CTX privacy game with one uniform hidden 256-bit key. -/
noncomputable def ctxPrivacyRealGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxPrivacyRealExpInner c key adversary

/-- Ideal nonce-respecting CTX sealing.

Repeated nonces are rejected before any sample is drawn.
A fresh request receives one uniform body with the plaintext length, one independent uniform 16-byte tag, and one independent uniform 64-byte outer commitment.
The suffix-cache update is private bookkeeping used by later exact-game projections; public random-oracle calls use the disjoint canonical public cache.
-/
noncomputable def ctxPrivacyIdealSealOracle :
    QueryImpl CtxSealSpec (StateT CtxIndependentTagState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commit ← $ᵗ CtxDigest
      let suffix := outerSuffix input.nonce input.context tag.toList
      let cache := cacheSuffix state.cache suffix commit
      let record : CtxRomRecord :=
        ⟨body.toList, tag.toList, tag.toList_length, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- Ideal CTX interface: a consistent public lazy random oracle plus ideal fresh records. -/
noncomputable def ctxPrivacyIdealImpl :
    QueryImpl CtxAdversarySpec
      (StateT CtxIndependentTagState ProbComp) :=
  ctxIndependentPublicOracle + ctxPrivacyIdealSealOracle

/-- Explicit ideal CTX privacy game. -/
noncomputable def ctxPrivacyIdealGame
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp Bool := do
  let result ←
    (simulateQ ctxPrivacyIdealImpl adversary.main).run
      emptyCtxIndependentTagState
  pure result.1

/-- Modified-CTX privacy advantage on the final Boolean decision. -/
noncomputable def ctxPrivacyAdvantage
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ℝ :=
  (ctxPrivacyRealGame c adversary).boolDistAdvantage
    (ctxPrivacyIdealGame adversary)

/-- The real public branch is exactly the canonical shared lazy-ROM handler. -/
theorem ctxPrivacyRealImpl_public
    (c : Pqxdh.Crypto) (key : CtxKey) (query : CtxRO.Domain) :
    ctxAdversaryImpl c key (.inl query) = ctxPublicOracle query := by
  rfl

/-- The real sealing branch is exactly modeled nonce-AEAD sealing followed by the shared ROM. -/
theorem ctxPrivacyRealImpl_seal
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) :
    ctxAdversaryImpl c key (.inr input) = ctxSealOracle c key input := by
  rfl

/-- The ideal public branch remains the canonical consistent lazy random oracle. -/
theorem ctxPrivacyIdealImpl_public (query : CtxRO.Domain) :
    ctxPrivacyIdealImpl (.inl query) = ctxIndependentPublicOracle query := by
  rfl

/-- A repeated ideal nonce is rejected before any body, tag, or commitment sample. -/
theorem ctxPrivacyIdealSealOracle_run_of_used
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (hused : input.nonce ∈ state.usedNonces) :
    (ctxPrivacyIdealSealOracle input).run state = pure (none, state) := by
  unfold ctxPrivacyIdealSealOracle
  simp [StateT.run, hused]

/-- A fresh ideal nonce draws the length-matched body, tag, and commitment exactly once each. -/
theorem ctxPrivacyIdealSealOracle_run_of_fresh
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (hfresh : input.nonce ∉ state.usedNonces) :
    (ctxPrivacyIdealSealOracle input).run state = (do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commit ← $ᵗ CtxDigest
      let suffix := outerSuffix input.nonce input.context tag.toList
      let cache := cacheSuffix state.cache suffix commit
      let record : CtxRomRecord :=
        ⟨body.toList, tag.toList, tag.toList_length, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)) := by
  unfold ctxPrivacyIdealSealOracle
  simp [StateT.run, hfresh]

/-- The real game samples its hidden key once, outside the complete adaptive execution. -/
theorem ctxPrivacyRealGame_eq
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyRealGame c adversary =
      ($ᵗ CtxKey >>= fun key => ctxPrivacyRealExpInner c key adversary) := by
  rfl

/-- The ideal game exposes only the adversary's final Boolean result. -/
theorem ctxPrivacyIdealGame_eq
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyIdealGame adversary =
      Prod.fst <$>
        (simulateQ ctxPrivacyIdealImpl adversary.main).run
          emptyCtxIndependentTagState := by
  simp [ctxPrivacyIdealGame, bind_pure_comp]

end BeaconcryptCore.Computational.CtxComputationalPrivacy
