-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedInstallFacts
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
/-! The actual first-opening raw source dictionary changes its request-kind journal and emits only its real primitive/hash operations. None of those operations installs a record kernel. The arbitrary raw request tree is retained unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree
open PqxdhRecordLiftInterface (Role EnvEffects)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {Auxiliary A : Type}
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)

private theorem raw_free (role : Role) (query : RegistrationRawSealBridge.Spec.Domain) :
    (RegistrationBoundSourceCompiler.rawCompiler (n := n) source writer query).IsQueryBoundP (InstallEnv role) 0 := by
  have counted := RegistrationNativeSecretWordAtomInstallCompiler.publication_free (n := n) role source writer (fun _ => pure none) (.inl query) []
  simpa only [RegistrationBoundSourceCompiler.compiler, StateT.run, isQueryBoundP_map_iff] using counted

private theorem read_free (role : Role) (query : RegistrationRawReceiveBridge.Spec.Domain) :
    (RegistrationBeaconRecordSourceProgram.read (n := n) source writer query).IsQueryBoundP (InstallEnv role) 0 := by
  unfold RegistrationBeaconRecordSourceProgram.read QueryImpl.compose
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro request
  exact raw_free source writer role request

private theorem state_read_free (role : Role) (query : RegistrationRawReceiveBridge.Spec.Domain) (before : EnvState Auxiliary) :
    ((RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer query).run before).IsQueryBoundP (InstallEnv role) 0 := by
  simp only [RegistrationBeaconMaterialRead.read, RegistrationBeaconMaterialRead.charge,
    StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
    simulateQ_ofLift_eq_self]
  exact read_free source writer role query

/-- Every actual primitive callback is installation-free while retaining its full returned source journal. -/
theorem primitive_free (role : Role) (query : RawCtxWholeOwner.PrimitiveSpec.Domain) (before : EnvState Auxiliary) :
    ((RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer) query).run before).IsQueryBoundP (InstallEnv role) 0 := by
  unfold RegistrationBeaconChargedSource.primitive QueryImpl.compose
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro request impossible
    exact impossible.elim
  · intro request _ current
    exact state_read_free source writer role request current

/-- The literal arbitrary first-opening raw tree is installation-free for every complete Env state. -/
theorem program_free (role : Role) (work : OracleComp RawCtxWholeOwner.PrimitiveSpec A) (before : EnvState Auxiliary) :
    ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer)) work).run before).IsQueryBoundP (InstallEnv role) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ current
    exact primitive_free source writer role query current
end BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree.primitive_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree.primitive_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree.program_free
