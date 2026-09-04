import BeaconcryptCore.Computational.CtxPrefixIsolation

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxSealSampling

open CtxRomAuth CtxPrefixIsolation

/-- A successful sealing transition that samples its outer digest directly and installs it in the shared cache without first consulting that cache.

This is sound only when the outer input is fresh. -/
noncomputable def ctxDirectSampleSealOracle (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxSealSpec (StateT CtxHandlerState ProbComp) := fun input state =>
  if input.nonce ∈ state.usedNonces then
    pure (none, state)
  else do
    let base := c.aeadSeal key.toList input.nonce.toList
      input.context.ad.bytes input.plaintext
    let query : CtxRO.Domain :=
      ((), outerInput key input.nonce input.context base.2)
    let commit ← $ᵗ CtxDigest
    let cache := state.cache.cacheQuery query commit
    let record : CtxRomRecord :=
      ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
    pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- Before public-prefix bad, nonce freshness implies freshness of the corresponding honest outer ROM input.

Cache provenance handles all possible cache origins. -/
theorem ctxSeal_query_fresh_of_good_unused (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxHandlerState)
    (hinvariant : state.Invariant key)
    (hflag : CtxPrefixFlagInvariant key (state, false))
    (hunused : input.nonce ∉ state.usedNonces) :
    state.cache ((), outerInput key input.nonce input.context
      (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
        input.plaintext).2) = none := by
  by_contra hhit
  rcases hinvariant.2.2 _ hhit with hpublic | hseal
  · have hprefix : SecretPrefixQuery key
        (outerInput key input.nonce input.context
          (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
            input.plaintext).2) :=
      secretPrefixQuery_outerInput key input.nonce input.context _
    have hbad : false = true := hflag.mpr ⟨_, hpublic, hprefix⟩
    simp at hbad
  · obtain ⟨entry, hentry, houter⟩ := hseal
    obtain ⟨hmaterial, _, _⟩ := Pqxdh.ctxPreimage_inj
      (recordWf key input.nonce input.context)
      (recordWf key entry.input.nonce entry.input.context)
      (c.aeadSeal_tag_length _ _ _ _) entry.record.tagLength houter
    have hnonceLists : input.nonce.toList = entry.input.nonce.toList :=
      congrArg Prod.snd hmaterial
    have hnonce : input.nonce = entry.input.nonce :=
      List.Vector.toList_injective hnonceLists
    apply hunused
    rw [hnonce]
    exact hinvariant.1 entry hentry

/-- On a good invariant state, the lazy-ROM sealing step is exactly direct digest sampling. -/
theorem ctxSealOracle_eq_directSample_of_good (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxHandlerState)
    (hinvariant : state.Invariant key)
    (hflag : CtxPrefixFlagInvariant key (state, false)) :
    (ctxSealOracle c key input).run state =
      (ctxDirectSampleSealOracle c key input).run state := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · change (if input.nonce ∈ state.usedNonces then pure (none, state) else _) =
      (if input.nonce ∈ state.usedNonces then pure (none, state) else _)
    rw [if_pos hused, if_pos hused]
  · have hfresh := ctxSeal_query_fresh_of_good_unused c key input state
      hinvariant hflag hused
    change (if input.nonce ∈ state.usedNonces then pure (none, state) else _) =
      (if input.nonce ∈ state.usedNonces then pure (none, state) else _)
    rw [if_neg hused, if_neg hused]
    rw [ctxRandomOracle,
      QueryImpl.withCaching_run_none uniformSampleImpl hfresh]
    rw [bind_map_left]
    rfl

end BeaconcryptCore.Computational.CtxSealSampling
