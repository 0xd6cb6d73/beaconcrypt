-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
/-! Actual local source realization preserves each installation classifier through common effects, routed KEM callbacks and external platform coins. Every original query/reply and mutable platform poststate remains represented; the transport assumes no complete callback or resource law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall LocalInstall)
open PqxdhRecordLiftInterface (Role)
variable {n : Nat} {KemSK Platform A : Type}

/-- Exact local routing preserves each actual installation request and its original reply. -/
theorem local_bound (role : Role) (selected : Bool)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) role) cap) :
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap :=
  RegistrationNativeSecretWordAtomInstallPredicate.local_bound role selected work cap bounded

private theorem routed_free (role : Role)
    (work : OracleComp (RegistrationNativeSecretWordKemInterface.Routed KemSK) A) :
    (simulateQ (RegistrationNativeSecretWordInterface.routedKem (n := n)) work).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeSecretWordInterface.routedKem, GlobalInstall, isQueryBoundP_query_iff]

/-- Actual source local/common/KEM/coin realization retains the original installation allowance. -/
theorem base_bound (role : Role) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicInstallLocal.LocalInstall (KemSK := KemSK) role) cap) :
    (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base candidate) work).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with (message | (message | common) | kem) | coin
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      GlobalInstall, RegistrationNativePlatformPublicInstallLocal.LocalInstall, RegistrationNativePairedSafe.GlobalInstall,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      GlobalInstall, RegistrationNativePlatformPublicInstallLocal.LocalInstall, RegistrationNativePairedSafe.GlobalInstall,
      isQueryBoundP_query_iff]
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      GlobalInstall, RegistrationNativePlatformPublicInstallLocal.LocalInstall, RegistrationNativePairedSafe.GlobalInstall,
      isQueryBoundP_query_iff]
    intro installed
    rw [ite_eq_left installed]
    decide
  · simpa only [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativePlatformPublicInstallLocal.LocalInstall, RegistrationNativePairedSafe.GlobalInstall, ite_false] using
      routed_free (n := n) role (RegistrationNativeSecretWordKemInterface.realize candidate kem)
  · simp [RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativeSecretWordFrontend.effect,
      GlobalInstall, RegistrationNativePlatformPublicInstallLocal.LocalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
      isQueryBoundP_query_iff]

/-- External platform samplers retain their complete returned state and issue no installation. -/
theorem platform_zero (role : Role) (work : StateT Platform ProbComp A) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect, GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
    RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.local_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.base_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.base_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport.platform_zero
