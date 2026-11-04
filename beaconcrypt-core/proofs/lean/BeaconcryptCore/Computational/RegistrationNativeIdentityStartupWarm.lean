-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache

/-! The actual one-input startup provenance determines its literal cache shape. The retained digest is kept exactly, without a freshness/uniformity premise or an empty-cache reset. This supplies the warm-start hypothesis of the shared physical-cache birthday theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm
open RegistrationNativePlatformCtxProvenance (Provenance)
open RegistrationNativePlatformCtxBirthdayCache (Warm)
variable {I KemSK : Type} {base : OracleSpec I} {n : Nat} {source : RegistrationNativeMldsa.Source}

/-- No cache input outside a single known anchor implies an actual empty or singleton cache. -/
theorem of_provenance (cache : CtxRomAuth.CtxRO.QueryCache) (anchor : Pqxdh.Bytes)
    (known : Provenance (cache, [anchor])) : Warm cache := by
  have absent (bytes : Pqxdh.Bytes) (different : bytes ≠ anchor) : cache ((), bytes) = none := by
    by_contra present
    exact different (List.mem_singleton.mp (known bytes present))
  cases found : cache ((), anchor) with
  | none =>
    left
    apply QueryCache.ext
    rintro ⟨tag, bytes⟩
    cases tag
    by_cases same : bytes = anchor
    · subst bytes; exact found
    · exact absent bytes same
  | some digest =>
    right
    refine ⟨((), anchor), digest, ?_⟩
    apply QueryCache.ext
    rintro ⟨tag, bytes⟩
    cases tag
    by_cases same : bytes = anchor
    · subst bytes
      rw [QueryCache.cacheQuery_self]
      exact found
    · rw [QueryCache.cacheQuery_of_ne _ _ (fun equal => same (congrArg Prod.snd equal))]
      exact absent bytes same

/-- Complete successful native startup supplies the exact warm cache used by all later callbacks. -/
theorem start (setup : PqxdhServerAuthExperiment.Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Warm (RegistrationNativeWorldCache.cache initial.state) :=
  of_provenance _ (absBytes initial.credential.publicKey)
    (RegistrationNativeIdentityStartupJournal.start setup ensureInit identityIndex serverKeyId initial reached)

end BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm.of_provenance' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm.of_provenance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityStartupWarm.start
