-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts
/-! Actual Env-only installation continuations retain the preceding material reply and cannot prepare or demand another root. The derived suffix certificate covers failed insertion replies and every returned RustM outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformPublicSlotKind (State handler)
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationNativePlatformPublicSlotSuffix (Allowed RootFree Ready)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
variable {n : Nat} {KemSK A : Type}

private theorem allowed_map (role : Role) (choice : Choice n) (work : OracleComp (EnvEffects n) A)
    (prior : work.AllQueriesSatisfy (RegistrationNativePlatformPublicSlotKind.Effect role choice)) :
    (simulateQ (RegistrationNativePairedCompile.effects (KemSK := KemSK)) work).AllQueriesSatisfy
      (Allowed (KemSK := KemSK) role choice) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at prior
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePairedCompile.effects]
    exact ⟨prior.1, fun reply => ih reply (prior.2 reply)⟩

/-- The actual Env continuation is a root-free, at-most-one installation suffix of the literal Native observer. -/
theorem continuation (role : Role) (choice : Choice n) (work : OracleComp (EnvEffects n) A)
    (bounded : work.IsQueryBoundP (InstallEnv role) 1)
    (allowed : work.AllQueriesSatisfy (RegistrationNativePlatformPublicSlotKind.Effect role choice))
    (before : State n) (ready : Ready choice 1 before)
    (result : A × State n)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (RegistrationNativePairedCompile.effects (KemSK := KemSK)) work)).run before)) :
    result.2.bad = false := by
  apply RegistrationNativePlatformPublicSlotSuffix.suffix role choice _ 1 (by omega) _ _
    (allowed_map role choice work allowed) before ready result supported
  · apply RawCtxSourceOpen.simulate_bound _ _ _ work 1 bounded
    intro query
    simp only [RegistrationNativePairedCompile.effects, isQueryBoundP_query_iff]
    intro installed
    change InstallEnv role query at installed
    simp only [installed, ite_true]
    decide
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
    intro query
    simp [RegistrationNativePairedCompile.effects, RootFree, isQueryBoundP_query_iff]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix.continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix.continuation
