-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformExtractedSdkFinish (runner sourceProjection)
open AdapterPublicFinishLifetime (packet)
variable {n : Nat} {I KemSK P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

 theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconPending) (input : Slice U8) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    sourceProjection self pending <$>
      RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before =
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
        (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar)).run before := by
  rw [AdapterPublicFinishNormalized.program_journal setup wire self pending input owner scalar (RegistrationWorldAgreementCompiler.erase before.server.world),
    simulateQ_map,StateT.run_map]
  unfold RegistrationNativeFinishLifetime.tree
  exact congrArg (fun decoded : core.option.Option registration.ResponsePacket =>
    sourceProjection self pending <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
        ((RegistrationNativeFinishFactor.body setup wire pending decoded owner scalar).run
          (RegistrationWorldAgreementCompiler.erase before.server.world))).run before)
    (AdapterPublicFinishLifetime.packet_roundtrip input)

 theorem platform (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconPending) (input : Slice U8) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : P) :
    Prod.map (Prod.map id backend) id <$>
      (Prod.map (sourceProjection self pending) id <$>
        (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) =
      (simulateQ coins ((simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created)
        (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar)).run (backend before))).run previous := by
  have sourceLaw:=native setup checks representation created wire self pending input owner scalar before
  have lifted:=congrArg (fun work=>(simulateQ coins work).run previous) sourceLaw
  simp only [simulateQ_map,StateT.run_map] at lifted
  calc
    _=Prod.map (Prod.map id backend) id <$>
        (simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar)).run before)).run previous :=
      congrArg (fun work=>Prod.map (Prod.map id backend) id <$>work) lifted
    _= _ := RegistrationNativePlatformSdkFinishBackend.platform coins setup checks representation created
      (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar)
      (RegistrationNativePlatformSdkFinishScope.program_safe setup wire self pending input owner scalar) before previous

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource.platform
