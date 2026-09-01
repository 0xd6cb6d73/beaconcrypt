import BeaconcryptCore.Computational.CtxAuthClassification
import Examples.CommitmentScheme.Common
import Mathlib.Data.Fintype.BigOperators

/-!
# Random-oracle alias bound for modified CTX

This module gives the modified CTX construction a scheme-specific adaptive random-oracle game.
The adversary receives a public byte-string random oracle and a sealing oracle under one hidden 32-byte key.
The sealing oracle rejects repeated 12-byte nonces, calls the modeled base AEAD on `RecordAD.bytes`, retains its 16-byte tag, and queries the shared random oracle at the exact `Pqxdh.ctxPreimage` containing the complete context.
Honest sealing calls, public adversary calls, and the final private verification call use one lazy random-oracle cache.

The proved game hop separates every accepted context-alias replay into an alias-gated target input already present in that shared cache or one fresh 512-bit digest guess.
The handler records successful seals and public inputs alongside the cache and maintains a provenance invariant through every adaptive query.
Nonce uniqueness and exact `ctxPreimage` injectivity rule out an honest origin for an alias target, so every remaining hit is a public query carrying the hidden key as its first 32 bytes.
The next reduction step must bound that secret-prefix event through base-AEAD IND$ privacy before composing the retained-base authenticity branch.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxRomAuth

/-- A protocol-width byte string. -/
abbrev FixedBytes (n : Nat) := List.Vector UInt8 n

/-- The hidden ChaCha20-Poly1305 key. -/
abbrev CtxKey := FixedBytes 32

/-- The protocol nonce. -/
abbrev CtxNonce := FixedBytes 12

/-- A BLAKE2b-512-sized random-oracle response. -/
abbrev CtxDigest := FixedBytes 64

/-- The ROM is indexed by the exact byte serialization consumed by `Pqxdh.ctxPreimage`. -/
abbrev CtxRO := (Unit × Pqxdh.Bytes →ₒ CtxDigest)

/-- Lazy shared-ROM implementation. -/
@[inline, reducible] def ctxRandomOracle :
    QueryImpl CtxRO (StateT CtxRO.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

/-- Associated data restricted to the protocol widths. -/
structure CtxRecordContext where
  /-- The complete modified-CTX record context. -/
  ad : Pqxdh.RecordAD
  /-- Base associated data has BeaconCrypt's fixed width. -/
  bytesLength : ad.bytes.length = 153
  /-- Sequence serialization is injective at the protocol width. -/
  seqRange : ad.seq < 2 ^ 64
  /-- Sender serialization is injective at the protocol width. -/
  sidRange : ad.sid < 2 ^ 64
deriving DecidableEq

/-- One chosen-plaintext sealing input under the fixed hidden key. -/
structure CtxSealInput where
  /-- The 12-byte IETF nonce. -/
  nonce : CtxNonce
  /-- The complete record context. -/
  context : CtxRecordContext
  /-- The base-AEAD plaintext. -/
  plaintext : Pqxdh.Bytes
deriving DecidableEq

/-- A structured modified-CTX record with the actual protocol fields and fixed tag/commitment widths. -/
structure CtxRomRecord where
  /-- The base-AEAD ciphertext body. -/
  body : Pqxdh.Bytes
  /-- The retained base-AEAD tag. -/
  tag : Pqxdh.Bytes
  /-- The retained tag has the modeled ChaCha20-Poly1305 width. -/
  tagLength : tag.length = 16
  /-- The outer random-oracle response. -/
  commit : CtxDigest
deriving DecidableEq

/-- The ideal-model `RecordCipher` represented by a ROM record. -/
def CtxRomRecord.toRecordCipher (record : CtxRomRecord) : Pqxdh.RecordCipher :=
  ⟨record.body, record.tag, record.commit.toList⟩

/-- The actual raw `C || T || T*` payload represented by a ROM record. -/
def CtxRomRecord.encode (record : CtxRomRecord) : Pqxdh.Bytes :=
  record.toRecordCipher.encode

@[simp] theorem ctxDigest_toList_length (digest : CtxDigest) :
    digest.toList.length = 64 :=
  digest.toList_length

/-- Every typed ROM record round-trips through the actual ideal-model parser. -/
@[simp] theorem decodeRecord_romRecord (record : CtxRomRecord) :
    Pqxdh.decodeRecord record.encode = some record.toRecordCipher := by
  exact Pqxdh.decodeRecord_encode record.toRecordCipher record.tagLength
    (ctxDigest_toList_length record.commit)

/-- Exact well-formedness evidence for a typed key, nonce, and record context. -/
def recordWf (key : CtxKey) (nonce : CtxNonce)
    (context : CtxRecordContext) :
    Pqxdh.RecordWf (key.toList, nonce.toList) context.ad :=
  ⟨key.toList_length, nonce.toList_length, context.bytesLength,
    context.seqRange, context.sidRange⟩

/-- Exact serialized outer-hash input of BeaconCrypt's modified CTX construction. -/
def outerInput (key : CtxKey) (nonce : CtxNonce)
    (context : CtxRecordContext) (baseTag : Pqxdh.Bytes) : Pqxdh.Bytes :=
  Pqxdh.ctxPreimage (key.toList, nonce.toList) context.ad baseTag

@[simp] theorem outerInput_take_key (key : CtxKey) (nonce : CtxNonce)
    (context : CtxRecordContext) (tag : Pqxdh.Bytes) :
    (outerInput key nonce context tag).take 32 = key.toList := by
  simp [outerInput, Pqxdh.ctxPreimage]

/-- Modified-CTX sealing is the actual base AEAD call followed by a shared-ROM query. -/
def ctxSeal (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) :
    OracleComp CtxRO CtxRomRecord := do
  let base := c.aeadSeal key.toList input.nonce.toList
    input.context.ad.bytes input.plaintext
  let commit ← CtxRO.query ((), outerInput key input.nonce input.context base.2)
  pure ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩

/-- A final target context and structured raw record. -/
structure CtxAliasTarget where
  /-- The target base-AEAD nonce. -/
  nonce : CtxNonce
  /-- The target complete context. -/
  context : CtxRecordContext
  /-- The target `C || T || T*` record. -/
  record : CtxRomRecord
  /-- The plaintext claimed for base-AEAD acceptance. -/
  claimedPlaintext : Pqxdh.Bytes
deriving DecidableEq

/-- The chosen-plaintext sealing interface rejects repeated nonces under the sampled hidden key. -/
abbrev CtxSealSpec := (CtxSealInput →ₒ Option CtxRomRecord)

/-- The adversary sees the public ROM and the nonce-rejecting CTX sealing interface. -/
abbrev CtxAdversarySpec := CtxRO + CtxSealSpec

/-- An adaptive multi-query modified-CTX adversary. -/
structure CtxAdversary where
  /-- The adversary's public-oracle computation and final forgery. -/
  main : OracleComp CtxAdversarySpec CtxAliasTarget

/-- One successful nonce-respecting sealing call, including the exact structured output. -/
structure CtxSuccessfulSeal where
  input : CtxSealInput
  record : CtxRomRecord
deriving DecidableEq

/-- Complete private state of the shared-ROM adversary handler. -/
structure CtxHandlerState where
  cache : CtxRO.QueryCache
  usedNonces : List CtxNonce
  successfulSeals : List CtxSuccessfulSeal
  publicInputs : List Pqxdh.Bytes

/-- Initially the ROM and all handler histories are empty. -/
def emptyCtxHandlerState : CtxHandlerState :=
  ⟨∅, [], [], []⟩

/-- Every successful seal nonce remains marked used. -/
def CtxHandlerState.SealsMarkedUsed (state : CtxHandlerState) : Prop :=
  ∀ entry ∈ state.successfulSeals, entry.input.nonce ∈ state.usedNonces

/-- Successful sealing calls have pairwise-distinct nonces. -/
def CtxHandlerState.UniqueSealNonces (state : CtxHandlerState) : Prop :=
  ∀ left ∈ state.successfulSeals, ∀ right ∈ state.successfulSeals,
    left.input.nonce = right.input.nonce → left = right

/-- Every shared-cache entry came either from a public call or an exact successful seal input. -/
def CtxHandlerState.CacheProvenance (key : CtxKey)
    (state : CtxHandlerState) : Prop :=
  ∀ input, state.cache ((), input) ≠ none →
    input ∈ state.publicInputs ∨
      ∃ entry ∈ state.successfulSeals,
        input = outerInput key entry.input.nonce entry.input.context entry.record.tag

/-- The cache-provenance and nonce-history invariant. -/
def CtxHandlerState.Invariant (key : CtxKey) (state : CtxHandlerState) : Prop :=
  state.SealsMarkedUsed ∧ state.UniqueSealNonces ∧ state.CacheProvenance key

/-- Add one public input after its query has been answered. -/
def CtxHandlerState.addPublic (state : CtxHandlerState)
    (input : Pqxdh.Bytes) (cache : CtxRO.QueryCache) : CtxHandlerState :=
  { state with cache := cache, publicInputs := input :: state.publicInputs }

/-- Add one successful seal after its private outer query has been answered. -/
def CtxHandlerState.addSeal (state : CtxHandlerState)
    (entry : CtxSuccessfulSeal) (cache : CtxRO.QueryCache) : CtxHandlerState :=
  { state with
    cache := cache
    usedNonces := entry.input.nonce :: state.usedNonces
    successfulSeals := entry :: state.successfulSeals }

/-- A single lazy-ROM step can add no cache-domain point other than its query. -/
theorem ctxRandomOracle_cache_origin (query : CtxRO.Domain)
    (cache : CtxRO.QueryCache) (result : CtxDigest × CtxRO.QueryCache)
    (hresult : result ∈ support ((ctxRandomOracle query).run cache))
    (candidate : CtxRO.Domain) (hhit : result.2 candidate ≠ none) :
    cache candidate ≠ none ∨ candidate = query := by
  cases hquery : cache query with
  | some digest =>
      rw [ctxRandomOracle, QueryImpl.withCaching_run_some _ hquery,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl hhit
  | none =>
      rw [ctxRandomOracle, QueryImpl.withCaching_run_none _ hquery,
        support_map] at hresult
      obtain ⟨digest, _, rfl⟩ := hresult
      by_cases heq : candidate = query
      · exact Or.inr heq
      · exact Or.inl (by
          simpa only [QueryCache.cacheQuery_of_ne cache digest heq] using hhit)

/-- Public-ROM step that records the exact byte input alongside the shared cache. -/
noncomputable def ctxPublicOracle :
    QueryImpl CtxRO (StateT CtxHandlerState ProbComp) := fun query state => do
  let (digest, cache) ← (ctxRandomOracle query).run state.cache
  pure (digest, state.addPublic query.2 cache)

/-- Nonce-respecting sealing step over the same shared lazy cache. -/
noncomputable def ctxSealOracle (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxSealSpec (StateT CtxHandlerState ProbComp) := fun input state =>
  if input.nonce ∈ state.usedNonces then
    pure (none, state)
  else do
    let base := c.aeadSeal key.toList input.nonce.toList
      input.context.ad.bytes input.plaintext
    let query := ((), outerInput key input.nonce input.context base.2)
    let (commit, cache) ← (ctxRandomOracle query).run state.cache
    let record : CtxRomRecord :=
      ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
    pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- Forward public ROM calls and handle sealing calls in one explicit shared-cache state. -/
noncomputable def ctxAdversaryImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT CtxHandlerState ProbComp) :=
  ctxPublicOracle + ctxSealOracle c key

@[simp] theorem emptyCtxHandlerState_invariant (key : CtxKey) :
    emptyCtxHandlerState.Invariant key := by
  simp [CtxHandlerState.Invariant, CtxHandlerState.SealsMarkedUsed,
    CtxHandlerState.UniqueSealNonces, CtxHandlerState.CacheProvenance,
    emptyCtxHandlerState]

/-- A public query preserves all handler-state invariants. -/
theorem ctxPublicOracle_preserves_invariant (key : CtxKey)
    (query : CtxRO.Domain) (state : CtxHandlerState)
    (hinvariant : state.Invariant key)
    (result : CtxDigest × CtxHandlerState)
    (hresult : result ∈ support ((ctxPublicOracle query).run state)) :
    result.2.Invariant key := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache >>= fun oracleResult =>
      pure (oracleResult.1, state.addPublic query.2 oracleResult.2)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, horacle, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rcases hinvariant with ⟨hmarked, hunique, hprovenance⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [CtxHandlerState.SealsMarkedUsed, CtxHandlerState.addPublic] using hmarked
  · simpa [CtxHandlerState.UniqueSealNonces, CtxHandlerState.addPublic] using hunique
  · intro input hhit
    rcases ctxRandomOracle_cache_origin query state.cache oracleResult horacle
      ((), input) hhit with hold | hnew
    · rcases hprovenance input hold with hpublic | hseal
      · exact Or.inl (by
          simp only [CtxHandlerState.addPublic, List.mem_cons]
          exact Or.inr hpublic)
      · exact Or.inr (by simpa only [CtxHandlerState.addPublic] using hseal)
    · left
      have hinput : input = query.2 := congrArg Prod.snd hnew
      simp [CtxHandlerState.addPublic, hinput]

/-- A nonce-rejected or successful sealing query preserves all handler-state invariants. -/
theorem ctxSealOracle_preserves_invariant (c : Pqxdh.Crypto)
    (key : CtxKey) (input : CtxSealInput) (state : CtxHandlerState)
    (hinvariant : state.Invariant key)
    (result : Option CtxRomRecord × CtxHandlerState)
    (hresult : result ∈ support ((ctxSealOracle c key input).run state)) :
    result.2.Invariant key := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · change result ∈ support
      (if input.nonce ∈ state.usedNonces then pure (none, state) else _) at hresult
    rw [if_pos hused, support_pure, Set.mem_singleton_iff] at hresult
    simpa [hresult] using hinvariant
  · let base := c.aeadSeal key.toList input.nonce.toList
      input.context.ad.bytes input.plaintext
    let query : CtxRO.Domain :=
      ((), outerInput key input.nonce input.context base.2)
    change result ∈ support
      (if input.nonce ∈ state.usedNonces then pure (none, state) else
        (ctxRandomOracle query).run state.cache >>= fun oracleResult =>
          let record : CtxRomRecord :=
            ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, oracleResult.1⟩
          pure (some record,
            state.addSeal ⟨input, record⟩ oracleResult.2)) at hresult
    rw [if_neg hused, mem_support_bind_iff] at hresult
    obtain ⟨oracleResult, horacle, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    let record : CtxRomRecord :=
      ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, oracleResult.1⟩
    rcases hinvariant with ⟨hmarked, hunique, hprovenance⟩
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      simp only [CtxHandlerState.addSeal, List.mem_cons] at hentry ⊢
      rcases hentry with hnew | hold
      · subst entry
        exact Or.inl rfl
      · exact Or.inr (hmarked entry hold)
    · intro left hleft right hright hnonce
      simp only [CtxHandlerState.addSeal, List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft <;> rcases hright with hright | hright
      · simp [hleft, hright]
      · subst left
        exfalso
        apply hused
        rw [hnonce]
        exact hmarked right hright
      · subst right
        exfalso
        apply hused
        rw [← hnonce]
        exact hmarked left hleft
      · exact hunique left hleft right hright hnonce
    · intro candidate hhit
      rcases ctxRandomOracle_cache_origin query state.cache oracleResult horacle
        ((), candidate) hhit with hold | hnew
      · rcases hprovenance candidate hold with hpublic | hseal
        · exact Or.inl (by simpa only [CtxHandlerState.addSeal] using hpublic)
        · rcases hseal with ⟨entry, hentry, heq⟩
          exact Or.inr ⟨entry, by
            simpa only [CtxHandlerState.addSeal, List.mem_cons] using Or.inr hentry,
            heq⟩
      · right
        refine ⟨⟨input, record⟩, ?_, ?_⟩
        · exact List.Mem.head _
        · have hcand : candidate = query.2 := congrArg Prod.snd hnew
          simpa [query, record, base] using hcand

/-- The complete explicit adversary handler preserves the invariant query by query. -/
theorem ctxAdversaryImpl_preserves_invariant (c : Pqxdh.Crypto)
    (key : CtxKey) :
    QueryImpl.PreservesInv (ctxAdversaryImpl c key)
      (CtxHandlerState.Invariant key) := by
  intro query state hinvariant result hresult
  cases query with
  | inl publicQuery =>
      exact ctxPublicOracle_preserves_invariant key publicQuery state
        hinvariant result hresult
  | inr sealInput =>
      exact ctxSealOracle_preserves_invariant c key sealInput state
        hinvariant result hresult

/-- The invariant lifts through every adaptive public/sealing strategy. -/
theorem ctxAdversary_run_invariant (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × CtxHandlerState)
    (hresult : result ∈ support
      ((simulateQ (ctxAdversaryImpl c key) adversary.main).run
        emptyCtxHandlerState)) :
    result.2.Invariant key := by
  exact OracleComp.simulateQ_run_preservesInv
    (ctxAdversaryImpl c key) (CtxHandlerState.Invariant key)
    (ctxAdversaryImpl_preserves_invariant c key)
    adversary.main emptyCtxHandlerState (emptyCtxHandlerState_invariant key)
    result hresult

/-- A successful seal has the retained base projection required by the final alias target. -/
def CtxAliasTarget.matchesSuccessfulSeal (target : CtxAliasTarget)
    (entry : CtxSuccessfulSeal) : Prop :=
  target.nonce = entry.input.nonce ∧
    target.context.ad.bytes = entry.input.context.ad.bytes ∧
    target.record.body = entry.record.body ∧
    target.record.tag = entry.record.tag ∧
    target.context.ad ≠ entry.input.context.ad

/-- A successful seal has the same complete authentication tuple as the target. -/
def CtxAliasTarget.sameFullTupleAsSuccessfulSeal (target : CtxAliasTarget)
    (entry : CtxSuccessfulSeal) : Prop :=
  target.nonce = entry.input.nonce ∧
    target.context.ad = entry.input.context.ad ∧
    target.record.encode = entry.record.encode

/-- State immediately before the private final verifier query. -/
structure CtxBeforeVerify where
  key : CtxKey
  target : CtxAliasTarget
  successfulSeals : List CtxSuccessfulSeal
  usedNonces : List CtxNonce
  publicInputs : List Pqxdh.Bytes

/-- A full-fresh alias replay against the actual successful sealing-query history. -/
def CtxFullAliasShape (before : CtxBeforeVerify) : Prop :=
  (∀ entry ∈ before.successfulSeals,
      ¬ before.target.sameFullTupleAsSuccessfulSeal entry) ∧
    ∃ entry ∈ before.successfulSeals,
      before.target.matchesSuccessfulSeal entry

/-- Exact target outer-hash input. -/
def CtxBeforeVerify.targetInput (before : CtxBeforeVerify) : Pqxdh.Bytes :=
  outerInput before.key before.target.nonce before.target.context
    before.target.record.tag

/-- The adversary explicitly queried the exact target transcript before verification. -/
def CtxPublicTargetQueried (before : CtxBeforeVerify) : Prop :=
  before.targetInput ∈ before.publicInputs

/-- A public query exposed the hidden 32-byte key prefix. -/
def CtxSecretPrefixQueried (before : CtxBeforeVerify) : Prop :=
  ∃ input ∈ before.publicInputs, input.take 32 = before.key.toList

/-- Reachable-state invariant projected onto the public pre-verification output and cache. -/
def CtxBeforeVerify.Invariant (before : CtxBeforeVerify)
    (cache : CtxRO.QueryCache) : Prop :=
  (∀ entry ∈ before.successfulSeals, entry.input.nonce ∈ before.usedNonces) ∧
    (∀ left ∈ before.successfulSeals, ∀ right ∈ before.successfulSeals,
      left.input.nonce = right.input.nonce → left = right) ∧
    (∀ input, cache ((), input) ≠ none →
      input ∈ before.publicInputs ∨
        ∃ entry ∈ before.successfulSeals,
          input = outerInput before.key entry.input.nonce entry.input.context
            entry.record.tag)

/-- Run the adversary under a fixed hidden key and return the shared cache explicitly. -/
noncomputable def ctxBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × CtxRO.QueryCache) := do
  let (target, state) ←
    (simulateQ (ctxAdversaryImpl c key) adversary.main).run emptyCtxHandlerState
  pure (⟨key, target, state.successfulSeals, state.usedNonces,
    state.publicInputs⟩, state.cache)

/-- The fixed-key generated output satisfies cache provenance and nonce uniqueness. -/
theorem ctxBeforeVerifyInner_invariant (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey)
    (result : CtxBeforeVerify × CtxRO.QueryCache)
    (hresult : result ∈ support (ctxBeforeVerifyInner c adversary key)) :
    result.1.Invariant result.2 := by
  unfold ctxBeforeVerifyInner at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨stateResult, hstate, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  simpa [CtxBeforeVerify.Invariant, CtxHandlerState.Invariant,
    CtxHandlerState.SealsMarkedUsed, CtxHandlerState.UniqueSealNonces,
    CtxHandlerState.CacheProvenance] using
    ctxAdversary_run_invariant c key adversary stateResult hstate

/-- Sample the hidden key and expose the shared lazy-ROM cache after all public and honest pre-verification calls. -/
noncomputable def ctxBeforeVerifyGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × CtxRO.QueryCache) := do
  let key ← $ᵗ CtxKey
  ctxBeforeVerifyInner c adversary key

/-- Every generated pre-verification output satisfies cache provenance and nonce uniqueness. -/
theorem ctxBeforeVerifyGame_invariant (c : Pqxdh.Crypto)
    (adversary : CtxAdversary)
    (result : CtxBeforeVerify × CtxRO.QueryCache)
    (hresult : result ∈ support (ctxBeforeVerifyGame c adversary)) :
    result.1.Invariant result.2 := by
  unfold ctxBeforeVerifyGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨key, _, hresult⟩ := hresult
  exact ctxBeforeVerifyInner_invariant c adversary key result hresult

/-- Exact public target queries necessarily expose the hidden-key prefix. -/
theorem publicTargetQueried_implies_secretPrefixQueried
    (before : CtxBeforeVerify) (hpublic : CtxPublicTargetQueried before) :
    CtxSecretPrefixQueried before := by
  refine ⟨before.targetInput, hpublic, ?_⟩
  exact outerInput_take_key before.key before.target.nonce
    before.target.context before.target.record.tag

/-- Nonce uniqueness and transcript injectivity exclude private honest target-cache hits for a full alias. -/
theorem fullAliasShape_excludes_honestTarget
    (before : CtxBeforeVerify) (cache : CtxRO.QueryCache)
    (hinvariant : before.Invariant cache)
    (halias : CtxFullAliasShape before) :
    ¬ ∃ honest ∈ before.successfulSeals,
      before.targetInput = outerInput before.key honest.input.nonce
        honest.input.context honest.record.tag := by
  rintro ⟨honest, hhonest, houter⟩
  obtain ⟨source, hsourceMem, hsourceMatch⟩ := halias.2
  obtain ⟨hmaterial, hcontext, _⟩ := Pqxdh.ctxPreimage_inj
    (recordWf before.key before.target.nonce before.target.context)
    (recordWf before.key honest.input.nonce honest.input.context)
    before.target.record.tagLength honest.record.tagLength houter
  have hnonceLists : before.target.nonce.toList = honest.input.nonce.toList :=
    congrArg Prod.snd hmaterial
  have hnonce : before.target.nonce = honest.input.nonce :=
    List.Vector.toList_injective hnonceLists
  have hsame : honest = source :=
    hinvariant.2.1 honest hhonest source hsourceMem
      (hnonce.symm.trans hsourceMatch.1)
  subst source
  exact hsourceMatch.2.2.2.2 hcontext

/-- On every invariant state, an alias-gated cache hit is an exact public target query. -/
theorem aliasCacheHit_implies_publicTargetQueried
    (before : CtxBeforeVerify) (cache : CtxRO.QueryCache)
    (hinvariant : before.Invariant cache)
    (halias : CtxFullAliasShape before)
    (hhit : cache ((), before.targetInput) ≠ none) :
    CtxPublicTargetQueried before := by
  rcases hinvariant.2.2 before.targetInput hhit with hpublic | hhonest
  · exact hpublic
  · exact absurd hhonest
      (fullAliasShape_excludes_honestTarget before cache hinvariant halias)

/-- Generated-game cache provenance: an alias-gated hit is an exact public target query. -/
theorem generated_aliasCacheHit_implies_publicTargetQueried
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (result : CtxBeforeVerify × CtxRO.QueryCache)
    (hresult : result ∈ support (ctxBeforeVerifyGame c adversary))
    (halias : CtxFullAliasShape result.1)
    (hhit : result.2 ((), result.1.targetInput) ≠ none) :
    CtxPublicTargetQueried result.1 := by
  exact aliasCacheHit_implies_publicTargetQueried result.1 result.2
    (ctxBeforeVerifyGame_invariant c adversary result hresult) halias hhit

/-- Generated-game cache provenance continued: the public target query exposes the hidden-key prefix. -/
theorem generated_aliasCacheHit_implies_secretPrefixQueried
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (result : CtxBeforeVerify × CtxRO.QueryCache)
    (hresult : result ∈ support (ctxBeforeVerifyGame c adversary))
    (halias : CtxFullAliasShape result.1)
    (hhit : result.2 ((), result.1.targetInput) ≠ none) :
    CtxSecretPrefixQueried result.1 := by
  apply publicTargetQueried_implies_secretPrefixQueried
  exact generated_aliasCacheHit_implies_publicTargetQueried c adversary
    result hresult halias hhit

/-- Complete acceptance event for a full-fresh alias replay at one proposed ROM response. -/
def CtxAcceptedFullAliasReplayAt (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  CtxFullAliasShape before ∧
    before.target.record.commit = expected ∧
    c.aeadOpen before.key.toList before.target.nonce.toList
      before.target.context.ad.bytes before.target.record.body
      before.target.record.tag = some before.target.claimedPlaintext

/-- The private verifier performs exactly one final shared-ROM call and then the actual base-AEAD acceptance test. -/
noncomputable def ctxFreshAliasVerifier (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) : OracleComp CtxRO Bool := do
  let expected ← CtxRO.query ((), before.targetInput)
  pure (@decide (CtxAcceptedFullAliasReplayAt c before expected)
    (Classical.propDecidable _))

/-- Fresh-cache branch of the nonce-respecting chosen-plaintext modified-CTX game. -/
noncomputable def ctxFreshAliasGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (Bool × CtxRO.QueryCache) := do
  let (before, cache) ← ctxBeforeVerifyGame c adversary
  if cache ((), before.targetInput) = none then
    simulateQ uniformSampleImpl
      ((simulateQ CtxRO.cachingOracle (ctxFreshAliasVerifier c before)).run cache)
  else
    pure (false, cache)

/-- Complete alias game without discarding target-cache hits. -/
noncomputable def ctxAliasGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (Bool × CtxRO.QueryCache) := do
  let (before, cache) ← ctxBeforeVerifyGame c adversary
  simulateQ uniformSampleImpl
    ((simulateQ CtxRO.cachingOracle (ctxFreshAliasVerifier c before)).run cache)

/-- Probability that a full alias target's exact outer-hash input is already in the shared cache before private verification. -/
noncomputable def ctxAliasTargetCacheHitProbability (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ℝ≥0∞ :=
  Pr[fun p => CtxFullAliasShape p.1 ∧
    p.2 ((), p.1.targetInput) ≠ none |
    ctxBeforeVerifyGame c adversary]

/-- Probability that a public ROM query carries the hidden key as its first 32 bytes. -/
noncomputable def ctxSecretPrefixQueriedProbability (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ℝ≥0∞ :=
  Pr[fun p => CtxSecretPrefixQueried p.1 |
    ctxBeforeVerifyGame c adversary]

/-- Every alias-gated target-cache hit reduces pointwise to a public hidden-key-prefix query. -/
theorem ctxAliasTargetCacheHitProbability_le_secretPrefixQueriedProbability
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    ctxAliasTargetCacheHitProbability c adversary ≤
      ctxSecretPrefixQueriedProbability c adversary := by
  unfold ctxAliasTargetCacheHitProbability ctxSecretPrefixQueriedProbability
  apply probEvent_mono
  intro result hresult hbad
  exact generated_aliasCacheHit_implies_secretPrefixQueried c adversary
    result hresult hbad.1 hbad.2

open scoped Classical in
/-- At a cache-fresh target input, the complete scheme-specific verifier accepts with at most one inverse digest-space factor. -/
theorem ctxFreshAliasVerifier_le_inv (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) (cache : CtxRO.QueryCache)
    (hfresh : cache ((), before.targetInput) = none) :
    Pr[fun z => z.1 = true |
      (simulateQ CtxRO.cachingOracle (ctxFreshAliasVerifier c before)).run cache] ≤
        (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  simpa only [ctxFreshAliasVerifier] using
    probEvent_from_fresh_query_le_inv
      (M := Unit) (S := Pqxdh.Bytes) (C := CtxDigest)
      (t := ((), before.targetInput)) (target := before.target.record.commit)
      (cache₀ := cache) hfresh
      (cont := fun expected => pure (@decide
        (CtxAcceptedFullAliasReplayAt c before expected)
        (Classical.propDecidable _))) (by
        intro actual hactual
        simp [CtxAcceptedFullAliasReplayAt, simulateQ_pure,
          StateT.run_pure, Ne.symm hactual])

/-- A cache-fresh full alias replay pays one inverse digest-space factor, independently of the number of sealing calls. -/
theorem ctxFreshAliasGame_le_inv (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxFreshAliasGame c adversary] ≤
      (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  unfold ctxFreshAliasGame
  refine probEvent_bind_le_of_forall_le fun p hp => ?_
  rcases p with ⟨before, cache⟩
  simp only
  by_cases hfresh : cache ((), before.targetInput) = none
  · rw [if_pos hfresh, uniformSampleImpl.probEvent_simulateQ]
    exact ctxFreshAliasVerifier_le_inv c before cache hfresh
  · rw [if_neg hfresh]
    simp only [probEvent_pure, Bool.false_eq_true, if_false]
    exact bot_le

theorem ctxDigest_card : Fintype.card CtxDigest = 2 ^ 512 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 64 = (2 ^ 8) ^ 64 := by norm_num
    _ = 2 ^ (8 * 64) := by rw [pow_mul]
    _ = 2 ^ 512 := by norm_num

/-- The fresh-alias bound with the BLAKE2b-512 width exposed numerically. -/
theorem ctxFreshAliasGame_le_inv_512 (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxFreshAliasGame c adversary] ≤
      (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  simpa only [ctxDigest_card] using ctxFreshAliasGame_le_inv c adversary

/-- Every accepted alias replay is charged either to a pre-verification exact-target cache hit or to one fresh 512-bit digest guess. -/
theorem ctxAliasGameProbability_le_cacheHit_add_inv (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxAliasGame c adversary] ≤
      ctxAliasTargetCacheHitProbability c adversary +
        (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  unfold ctxAliasGame ctxAliasTargetCacheHitProbability
  refine probEvent_bind_le_probEvent_add (p := fun p :
      CtxBeforeVerify × CtxRO.QueryCache =>
    CtxFullAliasShape p.1 ∧
      p.2 ((), p.1.targetInput) ≠ none) ?_
  intro p hp hnotBad
  rcases p with ⟨before, cache⟩
  by_cases halias : CtxFullAliasShape before
  · rw [uniformSampleImpl.probEvent_simulateQ]
    apply ctxFreshAliasVerifier_le_inv
    by_contra hhit
    exact hnotBad ⟨halias, hhit⟩
  · have hzero :
        Pr[fun z => z.1 = true |
          simulateQ uniformSampleImpl
            ((simulateQ CtxRO.cachingOracle
              (ctxFreshAliasVerifier c before)).run cache)] = 0 := by
      set_option maxRecDepth 100000 in
        simp [ctxFreshAliasVerifier, CtxAcceptedFullAliasReplayAt, halias]
    rw [hzero]
    exact bot_le

/-- The complete split with the BLAKE2b-512 width exposed numerically. -/
theorem ctxAliasGameProbability_le_cacheHit_add_inv_512
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxAliasGame c adversary] ≤
      ctxAliasTargetCacheHitProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  simpa only [ctxDigest_card] using
    ctxAliasGameProbability_le_cacheHit_add_inv c adversary

/-- Complete reduction seam: alias acceptance is charged to a public hidden-key-prefix query plus one fresh digest guess. -/
theorem ctxAliasGameProbability_le_secretPrefix_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxAliasGame c adversary] ≤
      ctxSecretPrefixQueriedProbability c adversary +
        (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  exact (ctxAliasGameProbability_le_cacheHit_add_inv c adversary).trans
    (add_le_add
      (ctxAliasTargetCacheHitProbability_le_secretPrefixQueriedProbability
        c adversary) (le_refl _))

/-- The typed one-key ROM alias-game split with the 512-bit digest width exposed numerically. -/
theorem ctxAliasGameProbability_le_secretPrefix_add_inv_512
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[fun z => z.1 = true | ctxAliasGame c adversary] ≤
      ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  simpa only [ctxDigest_card] using
    ctxAliasGameProbability_le_secretPrefix_add_inv c adversary

end BeaconcryptCore.Computational.CtxRomAuth
