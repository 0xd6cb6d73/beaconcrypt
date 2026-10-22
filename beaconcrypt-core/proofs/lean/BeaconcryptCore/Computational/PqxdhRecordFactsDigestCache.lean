-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw

/-! Canonical private/shared lazy-cache packing for the actual CTX source state. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate materialAt)
open PqxdhRecordFactsPrivateCacheSourceDraw (HashInput Spec compileSeal compileKeyedSeal compileHiddenSeal evaluate)
open PqxdhRecordFactsPrivateCacheFresh (sealResult)
variable {n : Nat}

abbrev Cache (n : Nat) := (HashInput n →ₒ CtxDigest).QueryCache

/-- The entire canonical combined cache, with exact private suffix addresses and original shared hash bytes. -/
def cacheOf (state : CtxPrivate n) : Cache n := QueryCache.ofFn fun
  | .inl (label, suffix) => (state.keys label).2 suffix
  | .inr bytes => state.base.primitive.2 ((), bytes)

/-- Source initialization gives the ordinary empty combined lazy cache. -/
theorem cacheOf_initial : cacheOf (PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial : CtxPrivate n)) = ∅ := by
  apply QueryCache.ext
  intro query
  cases query <;> rfl

/-- The hidden writer buffer has no effect on either half of the combined digest cache. -/
theorem cacheOf_pending (state : CtxPrivate n) (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    cacheOf { state with base := { state.base with pending := frames } } = cacheOf state := rfl

/-- The source's complete keyed poststate after the exposed seal sample. -/
noncomputable def sealedState (state : CtxPrivate n) (label : Label n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (digest : CtxDigest) : CtxPrivate n :=
  (PqxdhRecordFactsPrivateCacheFamily.localLens label).set state
    (sealResult input body tag width digest (state.keys label, state.base.primitive.2)).2

/-- The full source poststate's combined cache is exactly the ordinary single-point cache update. -/
theorem cacheOf_sealed (state : CtxPrivate n) (label : Label n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (digest : CtxDigest) :
    cacheOf (sealedState state label input body tag width digest) =
      (cacheOf state).cacheQuery (.inl (label, outerSuffix input.nonce input.context tag)) digest := by
  refine QueryCache.ext (fun query => ?_)
  cases query with
  | inr bytes => simp [cacheOf, sealedState, PqxdhRecordFactsPrivateCacheFamily.localLens, sealResult,
      QueryCache.cacheQuery]
  | inl address =>
      rcases address with ⟨other, suffix⟩
      by_cases same : other = label
      · subst other
        simp only [cacheOf, sealedState, PqxdhRecordFactsPrivateCacheFamily.localLens, sealResult,
          Function.update_self, QueryCache.toFn_ofFn]
        by_cases sameSuffix : suffix = outerSuffix input.nonce input.context tag
        · subst suffix; simp
        · simp [QueryCache.cacheQuery, sameSuffix, cacheOf]
      · simp [cacheOf, sealedState, PqxdhRecordFactsPrivateCacheFamily.localLens, sealResult,
          QueryCache.cacheQuery, same]

/-- Replace only the original shared ROM, retaining primitive counters and every private coordinate entry. -/
def withShared (state : CtxPrivate n) (cache : CtxRO.QueryCache) : CtxPrivate n :=
  { state with base := { state.base with primitive := (state.base.primitive.1, cache) } }

/-- An arbitrary base-state update frames the private half; the ordinary half reads its exact new shared cache. -/
theorem cacheOf_base (state : CtxPrivate n) (base : PqxdhRecordLiftProtocol.Private n) :
    cacheOf { state with base := base } =
      QueryCache.ofFn (fun query => match query with
      | .inl (label, suffix) => (state.keys label).2 suffix
      | .inr bytes => base.primitive.2 ((), bytes)) := rfl

/-- A base update that preserves the shared ROM preserves the complete combined cache. -/
theorem cacheOf_base_frame (state : CtxPrivate n) (base : PqxdhRecordLiftProtocol.Private n)
    (same : base.primitive.2 = state.base.primitive.2) :
    cacheOf { state with base := base } = cacheOf state := by
  refine QueryCache.ext (fun query => ?_)
  cases query with
  | inl address => rfl
  | inr bytes => simp only [cacheOf, QueryCache.toFn_ofFn, same]

/-- One ordinary shared-cache update is exactly the corresponding combined ordinary-address update. -/
theorem cacheOf_shared_query (state : CtxPrivate n) (bytes : Pqxdh.Bytes) (digest : CtxDigest) :
    cacheOf (withShared state (state.base.primitive.2.cacheQuery ((), bytes) digest)) =
      (cacheOf state).cacheQuery (.inr bytes) digest := by
  refine QueryCache.ext (fun query => ?_)
  cases query with
  | inl address => simp [cacheOf, withShared, QueryCache.cacheQuery]
  | inr other =>
      by_cases same : other = bytes
      · subst other; simp [cacheOf, withShared]
      · simp [cacheOf, withShared, QueryCache.cacheQuery, same]

end BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_pending' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_pending
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_sealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_sealed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_base' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_base
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_base_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_base_frame
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_shared_query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache.cacheOf_shared_query
