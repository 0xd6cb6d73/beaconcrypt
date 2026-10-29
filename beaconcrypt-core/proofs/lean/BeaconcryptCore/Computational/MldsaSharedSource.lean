-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaSharedNative
import BeaconcryptCore.Computational.RawCtxSourceHkdf

/-!
The shared authentication/record interface specialized to the actual source HKDF callback. Cache persistence is proved from that callback's definition, rather than imposed on an arbitrary stateful KDF. Every reached hash value is therefore retained across arbitrary source authentication, KDF, AEAD, writer and record-hash interleavings, including rejected operations.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.MldsaSharedSource

open CtxRomAuth
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)

noncomputable def implementation {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl MldsaSharedNative.Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  MldsaSharedNative.primitives source.crypto writer (RawCtxSourceHkdf.kdfImpl source)

private theorem pure_cache {Auxiliary Reply : Type} (value : Reply)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Reply × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support (pure (value, state) : ProbComp _)) : state.2 ≤ result.2.2 := by
  simp only [support_pure, Set.mem_singleton_iff] at supported
  rw [supported]

/-- Actual source primitives preserve every earlier authentication/record hash receipt. -/
theorem query_cache_persists {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((implementation source writer query).run state)) :
    state.2 ≤ result.2.2 := by
  rcases query with query | (request | (sealed | (opened | (bytes | frame))))
  · change result ∈ support ((fun inner => (inner.1, (state.1, inner.2))) <$>
      (ctxRandomOracle query).run state.2) at supported
    rw [support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact QueryImpl.withCaching_cache_le (uniformSampleImpl : QueryImpl CtxRO ProbComp) _ _ _ member
  · exact pure_cache _ state result supported
  · exact pure_cache _ state result supported
  · exact pure_cache _ state result supported
  · change result ∈ support
      ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
        (.inr (.inr (.inr (.inl bytes))))).run state) at supported
    rw [RawCtxMixedShared.shared_hash] at supported
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, member, same⟩ := supported
    rw [same]
    exact (MldsaSharedAuthentication.query_cached bytes state.2 inner member).1
  · exact pure_cache _ state result supported

/-- An arbitrary complete private source schedule retains the same hash receipts without a cache-preserving-KDF assumption. -/
theorem program_cache_persists {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp MldsaSharedNative.Spec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Result × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation source writer) work).run state)) :
    state.2 ≤ result.2.2 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value => exact pure_cache value state result supported
  | query_bind query next ih =>
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, first, rest⟩ := supported
    exact (query_cache_persists source writer query state step first).trans
      (ih step.1 step.2 result rest)

private theorem pure_auxiliary {Auxiliary Reply : Type} (value : Reply)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Reply × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support (pure (value, state) : ProbComp _)) : result.2.1 = state.1 := by
  simp only [support_pure, Set.mem_singleton_iff] at supported
  rw [supported]

/-- Concrete source primitives cannot erase or rewrite the separate signing-history component. -/
theorem query_auxiliary_unchanged {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((implementation source writer query).run state)) :
    result.2.1 = state.1 := by
  rcases query with query | (request | (sealed | (opened | (bytes | frame))))
  · change result ∈ support ((fun inner => (inner.1, (state.1, inner.2))) <$>
      (ctxRandomOracle query).run state.2) at supported
    rw [support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    rfl
  · exact pure_auxiliary _ state result supported
  · exact pure_auxiliary _ state result supported
  · exact pure_auxiliary _ state result supported
  · change result ∈ support
      ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
        (.inr (.inr (.inr (.inl bytes))))).run state) at supported
    rw [RawCtxMixedShared.shared_hash] at supported
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, member, same⟩ := supported
    exact congrArg (fun output => output.2.1) same
  · exact pure_auxiliary _ state result supported

/-- Any complete auth/record/KDF source schedule retains every previously logged signing attempt. -/
theorem program_auxiliary_unchanged {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp MldsaSharedNative.Spec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : Result × RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : result ∈ support ((simulateQ (implementation source writer) work).run state)) :
    result.2.1 = state.1 := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value => exact pure_auxiliary value state result supported
  | query_bind query next ih =>
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, first, rest⟩ := supported
    exact (ih step.1 step.2 result rest).trans
      (query_auxiliary_unchanged source writer query state step first)

end BeaconcryptCore.Computational.MldsaSharedSource

/-- info: 'BeaconcryptCore.Computational.MldsaSharedSource.query_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedSource.query_cache_persists
/-- info: 'BeaconcryptCore.Computational.MldsaSharedSource.program_cache_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedSource.program_cache_persists
/-- info: 'BeaconcryptCore.Computational.MldsaSharedSource.query_auxiliary_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedSource.query_auxiliary_unchanged
/-- info: 'BeaconcryptCore.Computational.MldsaSharedSource.program_auxiliary_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.MldsaSharedSource.program_auxiliary_unchanged
