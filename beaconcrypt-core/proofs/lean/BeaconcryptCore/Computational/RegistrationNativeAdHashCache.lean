-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion
import BeaconcryptCore.Computational.RegistrationServerSdkSource
import BeaconcryptCore.Computational.RegistrationAdHashAgreement

/-! The actual Server AD callback uses the same global hash cache as Init authentication, response authentication and records. These receipts retain the literal callback result and both native/platform poststates, then expose the digest consumed by the owned continuation. No cache entry, successful admission or AD value is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeAdHashCache
open PqxdhRecordLiftInterface
open RegistrationWorldAgreement (State)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {n : Nat} {Auxiliary Platform : Type}

/-- The instrumented World hash has its literal result in the one reached primitive cache. -/
theorem effects_hash_cached (bytes : Pqxdh.Bytes) (before after : PqxdhRecordLiftWorld.State n)
    (digest : CtxRomAuth.CtxDigest)
    (supported : (digest, after) ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) :
    before.primitive.2 ≤ after.primitive.2 ∧ after.primitive.2 ((), bytes) = some digest := by
  have projected : (digest, RegistrationWorldAuthentication.project after) ∈ support
      (Prod.map id RegistrationWorldAuthentication.project <$>
        ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) :=
    by
      rw [support_map]
      exact ⟨(digest, after), supported, rfl⟩
  rw [RegistrationWorldAuthentication.hash_project, support_map] at projected
  obtain ⟨inner, queried, same⟩ := projected
  have digestEq : inner.1 = digest := congrArg Prod.fst same
  have cacheEq : inner.2 = after.primitive.2 := congrArg (fun result => result.2.2) same
  have cached := MldsaSharedAuthentication.query_cached bytes before.primitive.2 inner queried
  simpa only [digestEq, cacheEq] using cached

/-- The real Server World lens keeps that same cache receipt, including actual sampling charges. -/
theorem world_hash_cached (bytes : Pqxdh.Bytes) (before after : State n Auxiliary)
    (digest : CtxRomAuth.CtxDigest)
    (supported : (digest, after) ∈ support ((RegistrationWorldServerCompletion.capability (.hash bytes)).run before)) :
    before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
      after.world.1.primitive.2 ((), bytes) = some digest := by
  simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact effects_hash_cached bytes before.world.1 inner.2 inner.1 called

/-- The actual non-platform Server AD phase retains the real selected hash result and complete reached cache. -/
theorem world_ad_hash_cached (pending : registration.ServerAdHash)
    (before after : State n Auxiliary) (initial : registration.ServerInitialKdf)
    (supported : (.ok (.Ok initial), after) ∈ support
      ((RegistrationWorldServerCompletion.adHash pending).run before)) :
    ∃ digest : CtxRomAuth.CtxDigest,
      pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) ∧
      before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
      after.world.1.primitive.2 ((), absBytes pending.input) = some digest := by
  cases requested : pending.request with
  | fail error | div => simp [RegistrationWorldServerCompletion.adHash, requested, StateT.run_pure] at supported
  | ok request =>
    simp only [RegistrationWorldServerCompletion.adHash, requested, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨middle, called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    have calledAt : (middle.1, after) ∈ support
        ((RegistrationWorldServerCompletion.capability (.hash (hashBytes request))).run before) := by
      have same : middle = (middle.1, after) := Prod.ext rfl returned.2.symm
      exact same ▸ called
    have cached := world_hash_cached (hashBytes request) before after middle.1 calledAt
    have requestSame : request = .Single pending.input.to_slice := RustM.ok.inj requested.symm
    have bytes : hashBytes request = absBytes pending.input := by
      simp only [requestSame, hashBytes, TranscriptAuthParts.absSlice, Std.Array.to_slice, absBytes]
    refine ⟨middle.1, returned.1.symm, cached.1, ?_⟩
    rw [← bytes]
    exact cached.2

/-- The real SDK lens preserves the earlier AD cache receipt and literal consumed core digest. -/
theorem sdk_ad_hash_cached (pending : registration.ServerAdHash)
    (before after : RegistrationServerFrontendCompiler.State n) (initial : registration.ServerInitialKdf)
    (supported : (.ok (.Ok initial), after) ∈ support
      ((RegistrationServerSdkSource.adHash pending).run before)) :
    ∃ digest : CtxRomAuth.CtxDigest,
      pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) ∧
      before.world.world.1.primitive.2 ≤ after.world.world.1.primitive.2 ∧
      after.world.world.1.primitive.2 ((), absBytes pending.input) = some digest := by
  simp only [RegistrationServerSdkSource.adHash, RegistrationServerSdkSource.world,
    StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have replyEq : inner.1 = .ok (.Ok initial) := congrArg Prod.fst same
  have cacheEq : inner.2.world.1.primitive.2 = after.world.world.1.primitive.2 :=
    congrArg (fun value => value.2.world.world.1.primitive.2) same
  obtain ⟨digest, resumed, extended, cached⟩ := world_ad_hash_cached pending before.world inner.2 initial
    (by simpa only [StateT.run, ← replyEq, Prod.mk.eta] using called)
  exact ⟨digest, resumed, by simpa only [cacheEq] using extended, by simpa only [cacheEq] using cached⟩

/-- Interpreting the real hash sampler in external state retains its actual reached World cache entry. -/
theorem platform_hash_cached (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (bytes : Pqxdh.Bytes) (before after : State n Auxiliary) (previous next : Platform)
    (digest : CtxRomAuth.CtxDigest)
    (supported : ((digest, after), next) ∈ support
      (((RegistrationNativePlatformServerCompletion.capability coins (.hash bytes)).run before).run previous)) :
    before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
      after.world.1.primitive.2 ((), bytes) = some digest := by
  have actual : (digest, after) ∈ support ((RegistrationWorldServerCompletion.capability (.hash bytes)).run before) := by
    apply OracleComp.support_simulateQ_run'_subset coins _ previous
    rw [StateT.run'_eq, support_map]
    exact ⟨((digest, after), next), supported, rfl⟩
  exact world_hash_cached bytes before after digest actual

/-- Successful actual Server AD hashing consumes exactly the digest cached for the selected 2638-byte transcript. -/
theorem platform_ad_hash_cached (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (pending : registration.ServerAdHash) (before after : State n Auxiliary) (previous next : Platform)
    (initial : registration.ServerInitialKdf)
    (supported : ((.ok (.Ok initial), after), next) ∈ support
      (((RegistrationNativePlatformServerCompletion.adHash coins pending).run before).run previous)) :
    ∃ digest : CtxRomAuth.CtxDigest,
      pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) ∧
      before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
      after.world.1.primitive.2 ((), absBytes pending.input) = some digest := by
  obtain ⟨request, reply, requested, hashed, resumed⟩ := RegistrationServerAdHash.state_hash_receipt
    (fun request => do
      let digest ← RegistrationNativePlatformServerCompletion.capability coins (.hash (hashBytes request))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))) pending before after previous next initial supported
  simp only [StateT.run_bind, mem_support_bind_iff] at hashed
  obtain ⟨middle, called, returned⟩ := hashed
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
    Option.some.injEq] at returned
  have calledAt : ((middle.1.1, after), next) ∈ support
      (((RegistrationNativePlatformServerCompletion.capability coins (.hash (hashBytes request))).run before).run previous) := by
    have same : middle = ((middle.1.1, after), next) :=
      Prod.ext (Prod.ext rfl returned.1.2.symm) returned.2.symm
    exact same ▸ called
  have cached := platform_hash_cached coins (hashBytes request) before after previous next middle.1.1 calledAt
  have requestSame : request = .Single pending.input.to_slice := RustM.ok.inj requested.symm
  have bytes : hashBytes request = absBytes pending.input := by
    simp only [requestSame, hashBytes, TranscriptAuthParts.absSlice, Std.Array.to_slice, absBytes]
  refine ⟨middle.1.1, ?_, cached.1, ?_⟩
  · exact returned.1.1 ▸ resumed
  · rw [← bytes]
    exact cached.2

end BeaconcryptCore.Computational.RegistrationNativeAdHashCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.effects_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.effects_hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.world_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.world_hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.platform_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.platform_hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.platform_ad_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.platform_ad_hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.world_ad_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.world_ad_hash_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAdHashCache.sdk_ad_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAdHashCache.sdk_ad_hash_cached
