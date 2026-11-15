-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAdHashCache

/-! Private proof data for the actual AD phase before a source Build's first-record leaf. It adds no public stage or callback. Producers must retain its real callback support, not infer it from admission or a later opening. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut
variable {n : Nat} {Platform Auxiliary : Type}

structure Cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache) where
  pendingAd : registration.ServerAdHash
  beforeHash : RegistrationWorldAgreement.State n Auxiliary
  afterHash : RegistrationWorldAgreement.State n Auxiliary
  previous : Platform
  next : Platform
  selected : registration.begin_server_completion control pin availability token.agreement application = .ok (.Ok pendingAd)
  called : ((.ok (.Ok initial), afterHash), next) ∈ support
    (((RegistrationNativePlatformServerCompletion.adHash coins pendingAd).run beforeHash).run previous)
  cacheExtension : afterHash.world.1.primitive.2 ≤ cache

/-- The literal callback supplies its actual consumed digest in the same later cache. -/
theorem cached (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : Cut (n := n) (Auxiliary := Auxiliary) coins token control pin availability application initial cache) :
    ∃ digest : CtxRomAuth.CtxDigest,
      cut.pendingAd.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) ∧
      cache ((), absBytes cut.pendingAd.input) = some digest := by
  obtain ⟨digest, resumed, _extended, present⟩ := RegistrationNativeAdHashCache.platform_ad_hash_cached
    coins cut.pendingAd cut.beforeHash cut.afterHash cut.previous cut.next initial cut.called
  exact ⟨digest, resumed, cut.cacheExtension present⟩

/-- A literal successful hash query and the owned continuation reconstruct that exact AD callback, preserving both native and platform states. -/
def of_hash (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache) (pending : registration.ServerAdHash)
    (beforeHash afterHash : RegistrationWorldAgreement.State n Auxiliary)
    (previous next : Platform) (request : registration.HashRequest) (digest : CtxRomAuth.CtxDigest)
    (selected : registration.begin_server_completion control pin availability token.agreement application = .ok (.Ok pending))
    (requested : pending.request = .ok request)
    (resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial))
    (called : ((digest, afterHash), next) ∈ support
      (((RegistrationNativePlatformServerCompletion.capability coins
        (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))).run beforeHash).run previous))
    (extension : afterHash.world.1.primitive.2 ≤ cache) :
    Cut (n := n) (Auxiliary := Auxiliary) coins token control pin availability application initial cache := by
  refine ⟨pending, beforeHash, afterHash, previous, next, selected, ?_, extension⟩
  simp only [RegistrationNativePlatformServerCompletion.adHash,
    RegistrationNativePlatformServerCompletion.adHashWith, RegistrationServerAdHash.runWith,
    requested, StateT.run_bind, mem_support_bind_iff]
  refine ⟨((.Some (RegistrationAuthenticationShared.digestArray digest), afterHash), next), ?_, ?_⟩
  · exact ⟨((digest, afterHash), next), called, by simp only [StateT.run_pure,
      support_pure, Set.mem_singleton_iff]⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, resumed]

/-- Later actual cache growth preserves the same pending value and callback states. -/
def extend (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache later : CtxRomAuth.CtxRO.QueryCache)
    (cut : Cut (n := n) (Auxiliary := Auxiliary) coins token control pin availability application initial cache)
    (extension : cache ≤ later) :
    Cut (n := n) (Auxiliary := Auxiliary) coins token control pin availability application initial later :=
  { cut with cacheExtension := cut.cacheExtension.trans extension }

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut.cached
