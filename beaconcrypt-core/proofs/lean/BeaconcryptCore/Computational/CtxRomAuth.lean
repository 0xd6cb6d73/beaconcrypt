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
The cache-hit event deliberately still includes both public adversary queries and honest sealing queries.
The next reduction step must use nonce enforcement and transcript injectivity to eliminate honest-query hits before charging the remainder to a secret-key-prefix public query.
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

/-- Stateful CTX sealing handler in which a nonce is consumed at most once under the fixed hidden key. -/
def ctxSealOracle (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxSealSpec (StateT (List CtxNonce) (OracleComp CtxRO)) := fun input used =>
  if input.nonce ∈ used then
    pure (none, used)
  else do
    let record ← ctxSeal c key input
    pure (some record, input.nonce :: used)

/-- Forward public ROM calls and handle sealing calls while keeping nonce state private. -/
def ctxAdversaryImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT (List CtxNonce) (OracleComp CtxRO)) :=
  (QueryImpl.id' CtxRO).liftTarget (StateT (List CtxNonce) (OracleComp CtxRO)) +
    ctxSealOracle c key

/-- A logged interface entry is a successful honest seal matching the target's retained base projection under a distinct complete CTX context. -/
def CtxAliasTarget.matchesSealEntry (target : CtxAliasTarget)
    (entry : (i : CtxAdversarySpec.Domain) × CtxAdversarySpec.Range i) : Prop :=
  match entry with
  | ⟨.inl _, _⟩ => False
  | ⟨.inr _, none⟩ => False
  | ⟨.inr source, some honest⟩ =>
      target.nonce = source.nonce ∧
        target.context.ad.bytes = source.context.ad.bytes ∧
        target.record.body = honest.body ∧
        target.record.tag = honest.tag ∧
        target.context.ad ≠ source.context.ad

/-- A logged interface entry has the same complete authentication tuple as the target. -/
def CtxAliasTarget.sameFullTupleAsSealEntry (target : CtxAliasTarget)
    (entry : (i : CtxAdversarySpec.Domain) × CtxAdversarySpec.Range i) : Prop :=
  match entry with
  | ⟨.inl _, _⟩ => False
  | ⟨.inr _, none⟩ => False
  | ⟨.inr source, some honest⟩ =>
      target.nonce = source.nonce ∧
        target.context.ad = source.context.ad ∧
        target.record.encode = honest.encode

/-- State immediately before the private final verifier query. -/
structure CtxBeforeVerify where
  /-- The sampled hidden key. -/
  key : CtxKey
  /-- The adversary's final target. -/
  target : CtxAliasTarget
  /-- Public ROM calls and sealing calls with their responses, excluding internal honest ROM calls. -/
  interfaceLog : QueryLog CtxAdversarySpec
  /-- Private nonce state after the adversary terminates. -/
  usedNonces : List CtxNonce

/-- A full-fresh alias replay against the actual successful sealing-query history. -/
def CtxFullAliasShape (before : CtxBeforeVerify) : Prop :=
  (∀ entry ∈ before.interfaceLog,
      ¬ before.target.sameFullTupleAsSealEntry entry) ∧
    ∃ entry ∈ before.interfaceLog, before.target.matchesSealEntry entry

/-- Exact target outer-hash input. -/
def CtxBeforeVerify.targetInput (before : CtxBeforeVerify) : Pqxdh.Bytes :=
  outerInput before.key before.target.nonce before.target.context
    before.target.record.tag

/-- Run the adversary, log only its public interface calls, and leave internal honest outer-hash calls unlogged. -/
def ctxBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    OracleComp CtxRO CtxBeforeVerify := do
  let ((target, interfaceLog), usedNonces) ←
    (simulateQ (ctxAdversaryImpl c key).withLogging adversary.main).run.run []
  pure ⟨key, target, interfaceLog, usedNonces⟩

/-- Sample the hidden key and expose the shared lazy-ROM cache after all public and honest pre-verification calls. -/
noncomputable def ctxBeforeVerifyGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × CtxRO.QueryCache) := do
  let key ← $ᵗ CtxKey
  (simulateQ ctxRandomOracle (ctxBeforeVerifyInner c adversary key)).run ∅

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

end BeaconcryptCore.Computational.CtxRomAuth
