-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle
import BeaconcryptCore.Refinement.AdapterPublicFinishLifetime
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel
private theorem apply_pure {S A : Type} {m : Type→Type} [Monad m] (value : A) (state : S) :
    (pure value :StateT S m A) state=pure (value,state) := rfl
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
variable (before : RegistrationNativeExperiment.State n KemSK source) (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform)

private theorem finish_pure
    (localPure : (RegistrationNativePlatformExtractedFinish.finish (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup source wire index packet).run before.beacons=pure ((.ok none :RustM (Option Pqxdh.Bytes)),before.beacons)) :
    ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformExtractedFinish.finish setup source wire index packet)).run before)).run previous)=pure ((.ok none :RustM (Option Pqxdh.Bytes)),(before,previous)) := by
  simp only [StateT.run] at localPure
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run]
  rw [localPure]
  simp only [apply_pure,simulateQ_pure,pure_bind]
  rw [RegistrationWorldAgreementCompiler.join_erase]
  simp only [map_pure]

theorem idle (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : before.beacons[index]?=some owner)
    (inactive : RegistrationNativePlatformExtractedSdkIdle.NativeFinishIdle owner.phase) :
    ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformExtractedFinish.finish setup source wire index packet)).run before)).run previous)=pure ((.ok none :RustM (Option Pqxdh.Bytes)),(before,previous)) := by
  apply finish_pure setup checks representation created wire index packet before coins previous
  exact RegistrationNativePlatformExtractedSdkIdle.finish_native setup wire index packet before.beacons owner selected inactive

theorem missing (absent : before.beacons[index]?=none) :
    ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformExtractedFinish.finish setup source wire index packet)).run before)).run previous)=pure ((.ok none :RustM (Option Pqxdh.Bytes)),(before,previous)) := by
  apply finish_pure setup checks representation created wire index packet before coins previous
  unfold RegistrationNativePlatformExtractedFinish.finish
  simp only [StateT.run_bind,StateT.run_get,pure_bind,absent]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel.idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel.idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel.missing
