-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallPredicate

/-! Native publication compilation introduces hash and coin effects only. The current-Env Common service therefore preserves the exact role-installation bill of its open paired program, retaining all chronological signing receipts and native failure continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativePairedServerService (Common)
open RegistrationNativeSecretWordInterface (LocalSpec effect)
open RegistrationNativeSecretWordAtomInstallCaps (Install InstallEnv)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value Auxiliary : Type}

private theorem coins_free (role : Role) (work : ProbComp Value) :
    (PqxdhDeploymentEnvironment.coins (n := n) work).IsQueryBoundP (InstallEnv role) 0 := by
  unfold PqxdhDeploymentEnvironment.coins
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [PqxdhDeploymentEnvironment.coinFx, InstallEnv, isQueryBoundP_query_iff]

private theorem primitive_free (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) :
    (PqxdhDeploymentEnvironment.primFwd (n := n) source.crypto source query).IsQueryBoundP (InstallEnv role) 0 := by
  rcases query with request | (bytes | input)
  all_goals simp [PqxdhDeploymentEnvironment.primFwd, PqxdhDeploymentEnvironment.request,
    InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem shared_free (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain) :
    (RegistrationBoundSourceCompiler.sharedCompiler (n := n) source writer query).IsQueryBoundP (InstallEnv role) 0 := by
  cases query with
  | inl query => simp [RegistrationBoundSourceCompiler.sharedCompiler, PqxdhDeploymentEnvironment.request,
      InstallEnv, isQueryBoundP_query_iff]
  | inr query =>
      simp only [RegistrationBoundSourceCompiler.sharedCompiler, PqxdhDeploymentEnvironment.sharedFwd,
        QueryImpl.compose]
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro request
      exact primitive_free role source request

private theorem raw_free (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RegistrationRawSealBridge.Spec.Domain) :
    (RegistrationBoundSourceCompiler.rawCompiler (n := n) source writer query).IsQueryBoundP (InstallEnv role) 0 := by
  simp only [RegistrationBoundSourceCompiler.rawCompiler, QueryImpl.compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro request
  exact shared_free role source writer request

/-- Every actual primitive, shared hash and ML signing callback adds no hidden or known installation. -/
theorem publication_free (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : List RegistrationSigningShared.Receipt) :
    ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run before).IsQueryBoundP (InstallEnv role) 0 := by
  cases query with
  | inl query =>
      simp only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff]
      exact raw_free role source writer query
  | inr request => cases request with
    | hash request => simp [RegistrationBoundSourceCompiler.compiler, StateT.run,
        PqxdhDeploymentEnvironment.request, InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | sign request payload digest =>
        simp only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff]
        exact coins_free role _

private theorem effects_bound (role : Role) (work : OracleComp (EnvEffects n) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (InstallEnv role) cap) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  by_cases counted : InstallEnv role query <;>
    simp [effect, LocalInstall, Install, counted, isQueryBoundP_query_iff]

private theorem common_step (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Common n).Domain) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) source writer sign query).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) (if Install role query then 1 else 0) := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
        StateT.run, isQueryBoundP_map_iff, Install, ite_false]
      exact effects_bound role _ 0 (publication_free role source writer sign query before.receipts)
  | inr query =>
      by_cases counted : InstallEnv role query <;>
        simp [RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
          isQueryBoundP_map_iff, effect, LocalInstall, Install, counted, isQueryBoundP_query_iff]

/-- The actual mutable Common component preserves each open installation bill on its current complete environment. -/
theorem common_bound (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Common n) Value) (cap : Nat) (bounded : work.IsQueryBoundP (Install role) cap)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((simulateQ (RegistrationNativeCommonCompiler.common (effect (KemSK := KemSK)) source writer sign) work).run before).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) role) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted state
    simpa only [ite_eq_left counted] using common_step (KemSK := KemSK) role source writer sign query state
  · intro query quiet state
    simpa only [ite_eq_right quiet] using common_step (KemSK := KemSK) role source writer sign query state

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler.publication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler.publication_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler.common_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler.common_bound
