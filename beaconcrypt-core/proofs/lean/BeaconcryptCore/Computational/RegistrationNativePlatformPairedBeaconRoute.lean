-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedTraceEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
import BeaconcryptCore.Computational.RegistrationNativeInstallFreePreparation
/-! The selected-scalar source route changes only its actual root-preparation message. Material demand and Env effects retain their literal descriptors/replies. The derived installation bill transport covers both source scalar branches and every optional preparation reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix (NativeInstall)
open RegistrationNativePairedSafe (GlobalInstall)
open RegistrationBeaconReferenceCompiler (Spec)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}

def route (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (Spec n KemSK) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) := fun query =>
  match scalar with
  | none => RegistrationNativePublicFrontend.liftLocal false query
  | some scalar => simulateQ (RegistrationNativePublicFrontend.liftLocal false) (RegistrationNativePublicOwners.ordinary setup scalar query)

private theorem ordinary_bound (role : Role) (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n KemSK) A) (count : Nat) (bounded : work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp only [RegistrationNativePublicOwners.ordinary]
    split
    · trivial
    · simp [NativeInstall, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicOwners.ordinary, NativeInstall, isQueryBoundP_query_iff]
  · simp only [RegistrationNativePublicOwners.ordinary, NativeInstall, isQueryBoundP_query_iff]
    intro installed
    simp only [installed, ite_true]
    decide
  · simp [RegistrationNativePublicOwners.ordinary, NativeInstall, isQueryBoundP_query_iff]

/-- Scalar-dependent preparation changes no literal role installation count. -/
theorem bound (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n KemSK) A) (count : Nat) (bounded : work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) count) :
    (simulateQ (route setup scalar) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) count := by
  cases scalar with
  | none => exact RegistrationNativePairedSafe.local_bound role false work count bounded
  | some scalar =>
    have composed : route (n := n) setup (some scalar) = RegistrationNativePublicFrontend.liftLocal false ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar := rfl
    rw [composed, QueryImpl.simulateQ_compose]
    exact RegistrationNativePairedSafe.local_bound role false _ count (ordinary_bound role setup scalar work count bounded)

/-- The exact source Env callback is unchanged by the private scalar route. -/
theorem environment (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    route (n := n) setup scalar ∘ₛ RegistrationBeaconReferenceCompiler.effect = RegistrationNativePairedCompile.effects := by
  funext query
  cases scalar <;> simp [QueryImpl.compose, route, RegistrationBeaconReferenceCompiler.effect,
    RegistrationNativePublicOwners.ordinary, RegistrationNativePublicFrontend.liftLocal,
    RegistrationNativePairedCompile.effects]

/-- The literal material descriptor and optional choice reply are unchanged by scalar preparation. -/
theorem demand (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (message : RegistrationNativeRelatedFamily.Message) :
    simulateQ (route (n := n) setup scalar) (RegistrationNativePlatformBeaconMaterialInterpreter.demand message) =
      RegistrationNativePlatformPairedTraceEffects.demand message := by
  cases scalar <;> simp [route, RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    RegistrationNativePublicOwners.ordinary, RegistrationNativePublicFrontend.liftLocal,
    RegistrationNativePlatformPairedTraceEffects.demand]
end BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.environment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.environment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute.demand
