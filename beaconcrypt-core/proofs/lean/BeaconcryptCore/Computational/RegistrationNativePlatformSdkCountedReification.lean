-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
import BeaconcryptCore.Refinement.AdapterPublicAgreementCountedCrypto
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap
/-! The actual source cryptographic dictionary's counted Rust interpretation also factors through the retained SDK backend. Explicit source keys and RNG remain arguments; every normal, failure and divergence result and the complete persistent platform state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification
variable {n : Nat} {KemSK Platform A : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

noncomputable def native (work : RustT ProbComp A) : RustT (RegistrationNativeExperiment.M n KemSK source) A :=
  AdapterPublicAgreementNativeWorldMap.transform (AdapterPublicAgreementCountedRust.counted work)

def countedBackend (work : RustT ProbComp A) : StateT (Backend n KemSK) ProbComp (RustM A) :=
  fun before => (fun result => (result.1,{before with world := worldBackend result.2})) <$>
    (PqxdhRecordLiftWorld.sampled work.run).run before.world

theorem counted_backend (work : RustT ProbComp A) (before : Native) :
    Prod.map id backend <$> (native work).run.run before=
      (countedBackend work).run (backend before) := by
  unfold native AdapterPublicAgreementNativeWorldMap.transform AdapterPublicAgreementCountedRust.counted
  rw [AdapterPublicAgreementNativeWorldMap.world_run]
  simp only [countedBackend,PqxdhRecordLiftWorld.sampled,StateT.run,backend,worldBackend,
    bind_pure_comp,Functor.map_map]
  dsimp only [Prod.map,id_eq,backend,worldBackend,AdapterPublicAgreementNativeWorldMap.putWorld]
  simp only [Function.update_idem]

theorem counted_platform (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : RustT ProbComp A) (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((native work).run.run before)).run previous=
      (simulateQ coins ((countedBackend work).run (backend before))).run previous := by
  rw [←counted_backend work before,simulateQ_map,StateT.run_map]
  congr 1

theorem bundle_continuation (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : RustT ProbComp A) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((native work).run.run
        (RegistrationNativeBundleLifecycle.after index owner scalar publication before))).run previous=
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((native work).run.run before)).run previous := by
  rw [counted_platform,counted_platform,publication_backend]

theorem finish_continuation (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : RustT ProbComp A) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon))
    (owners : List (RegistrationNativeBeaconFrontend.Owner source))
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((native work).run.run
        (RegistrationNativeFinishTerminalTree.after index owner control reply
          (RegistrationNativeFinishTerminalTree.assemble owners environment before)))).run previous=
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((native work).run.run (commitEnvironment environment before))).run previous := by
  rw [counted_platform,counted_platform,finish_backend]

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.counted_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.counted_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.counted_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.counted_platform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.bundle_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.bundle_continuation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.finish_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification.finish_continuation
