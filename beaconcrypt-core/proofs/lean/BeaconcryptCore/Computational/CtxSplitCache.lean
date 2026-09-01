import BeaconcryptCore.Computational.CtxPrefixIsolation

/-!
# Exact split-cache projection for modified CTX

This module factors the canonical random-oracle cache into two disjoint views.
The public cache keeps complete byte-string inputs outside the hidden-key-prefix domain, while the secret cache indexes hidden-key-prefix entries only by the key-free suffix following the 32-byte key.
Merging the projection recovers the canonical cache extensionally, and projecting a normalized split cache is an exact inverse.
-/

open OracleComp OracleSpec

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxSplitCache

open CtxRomAuth CtxPrefixIsolation

/-- Random-oracle addresses after removing the fixed 32-byte secret-key prefix. -/
abbrev CtxSuffixRO := (Pqxdh.Bytes →ₒ CtxDigest)

/-- Remove the 32-byte candidate-key prefix from a complete random-oracle input. -/
def secretSuffix (input : Pqxdh.Bytes) : Pqxdh.Bytes :=
  input.drop 32

/-- Reconstruct a hidden-key-prefix address from its key-free suffix. -/
def secretAddress (key : CtxKey) (suffix : Pqxdh.Bytes) : Pqxdh.Bytes :=
  key.toList ++ suffix

/-- The exact key-free suffix `N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid)` used by modified CTX. -/
def outerSuffix (nonce : CtxNonce) (context : CtxRecordContext)
    (tag : Pqxdh.Bytes) : Pqxdh.Bytes :=
  nonce.toList ++ context.ad.bytes ++ tag ++ Pqxdh.LE64 context.ad.seq ++
    Pqxdh.LE64 context.ad.sid

/-- The canonical outer input is exactly the key prefix followed by `outerSuffix`. -/
theorem outerInput_eq_secretAddress_outerSuffix (key : CtxKey)
    (nonce : CtxNonce) (context : CtxRecordContext) (tag : Pqxdh.Bytes) :
    outerInput key nonce context tag =
      secretAddress key (outerSuffix nonce context tag) := by
  simp [outerInput, Pqxdh.ctxPreimage, secretAddress, outerSuffix]

/-- At the retained-tag width, the key-free suffix has exactly 197 bytes. -/
theorem outerSuffix_length (nonce : CtxNonce) (context : CtxRecordContext)
    (tag : Pqxdh.Bytes) (htag : tag.length = 16) :
    (outerSuffix nonce context tag).length = 197 := by
  simp [outerSuffix, context.bytesLength, htag]

/-- Every reconstructed secret address is in the hidden-key-prefix domain. -/
@[simp] theorem secretPrefixQuery_secretAddress (key : CtxKey)
    (suffix : Pqxdh.Bytes) :
    SecretPrefixQuery key (secretAddress key suffix) := by
  simp [SecretPrefixQuery, secretAddress, key.toList_length]

/-- Removing the prefix just installed by `secretAddress` recovers the suffix. -/
@[simp] theorem secretSuffix_secretAddress (key : CtxKey)
    (suffix : Pqxdh.Bytes) :
    secretSuffix (secretAddress key suffix) = suffix := by
  simp [secretSuffix, secretAddress, key.toList_length]

/-- Every input in the hidden-key-prefix domain is exactly its prefix followed by its suffix. -/
theorem secretAddress_secretSuffix (key : CtxKey) (input : Pqxdh.Bytes)
    (hprefix : SecretPrefixQuery key input) :
    secretAddress key (secretSuffix input) = input := by
  calc
    secretAddress key (secretSuffix input) = input.take 32 ++ input.drop 32 := by
      rw [secretAddress, secretSuffix, hprefix]
    _ = input := List.take_append_drop 32 input

/-- Removing the key prefix from an honest outer input yields its exact protocol suffix. -/
theorem secretSuffix_outerInput (key : CtxKey) (nonce : CtxNonce)
    (context : CtxRecordContext) (tag : Pqxdh.Bytes) :
    secretSuffix (outerInput key nonce context tag) =
      outerSuffix nonce context tag := by
  rw [outerInput_eq_secretAddress_outerSuffix, secretSuffix_secretAddress]

/-- Public and hidden-prefix portions of one canonical random-oracle cache. -/
@[ext] structure SplitCache where
  /-- Complete public inputs outside the secret-prefix domain. -/
  publicCache : CtxRO.QueryCache
  /-- Hidden-prefix inputs indexed only by the suffix after the key. -/
  suffixCache : CtxSuffixRO.QueryCache

/-- Look up a canonical query through the split representation. -/
def SplitCache.lookup (key : CtxKey) (cache : SplitCache)
    (query : CtxRO.Domain) : Option CtxDigest :=
  if SecretPrefixQuery key query.2 then
    cache.suffixCache (secretSuffix query.2)
  else
    cache.publicCache query

/-- Merge a split cache back into the canonical cache type. -/
def SplitCache.merge (key : CtxKey) (cache : SplitCache) :
    CtxRO.QueryCache :=
  cache.lookup key

/-- Project a canonical cache into its public and hidden-prefix suffix portions. -/
def splitCtxCache (key : CtxKey) (cache : CtxRO.QueryCache) : SplitCache where
  publicCache := fun query =>
    if SecretPrefixQuery key query.2 then none else cache query
  suffixCache := fun suffix => cache ((), secretAddress key suffix)

/-- Split caches are normalized when the public component contains no secret-prefix entry. -/
def SplitCache.Normalized (key : CtxKey) (cache : SplitCache) : Prop :=
  ∀ query, SecretPrefixQuery key query.2 → cache.publicCache query = none

/-- Every canonical projection is normalized by construction. -/
theorem splitCtxCache_normalized (key : CtxKey) (cache : CtxRO.QueryCache) :
    (splitCtxCache key cache).Normalized key := by
  intro query hprefix
  simp [splitCtxCache, hprefix]

/-- Looking up through a canonical projection returns the original cached answer exactly. -/
theorem splitCtxCache_lookup (key : CtxKey) (cache : CtxRO.QueryCache)
    (query : CtxRO.Domain) :
    (splitCtxCache key cache).lookup key query = cache query := by
  rcases query with ⟨queryUnit, input⟩
  cases queryUnit
  by_cases hprefix : SecretPrefixQuery key input
  · simp [SplitCache.lookup, splitCtxCache, hprefix]
    rw [secretAddress_secretSuffix key input hprefix]
  · simp [SplitCache.lookup, splitCtxCache, hprefix]

/-- Merging a canonical projection is extensionally the original cache. -/
theorem merge_splitCtxCache (key : CtxKey) (cache : CtxRO.QueryCache) :
    (splitCtxCache key cache).merge key = cache := by
  apply QueryCache.ext
  intro query
  exact splitCtxCache_lookup key cache query

/-- Projecting a normalized split cache after merging it is an exact inverse. -/
theorem splitCtxCache_merge (key : CtxKey) (cache : SplitCache)
    (hnormalized : cache.Normalized key) :
    splitCtxCache key (cache.merge key) = cache := by
  apply SplitCache.ext
  · funext query
    by_cases hprefix : SecretPrefixQuery key query.2
    · simpa [splitCtxCache, hprefix] using (hnormalized query hprefix).symm
    · simp [splitCtxCache, SplitCache.merge, SplitCache.lookup, hprefix]
  · funext suffix
    simp [splitCtxCache, SplitCache.merge, SplitCache.lookup]
    rw [secretSuffix_secretAddress]

/-- The empty canonical cache projects to two empty caches. -/
@[simp] theorem splitCtxCache_empty (key : CtxKey) :
    splitCtxCache key (∅ : CtxRO.QueryCache) =
      ⟨(∅ : CtxRO.QueryCache), (∅ : CtxSuffixRO.QueryCache)⟩ := by
  apply SplitCache.ext
  · funext query
    simp [splitCtxCache]
  · funext suffix
    simp [splitCtxCache]

end BeaconcryptCore.Computational.CtxSplitCache
