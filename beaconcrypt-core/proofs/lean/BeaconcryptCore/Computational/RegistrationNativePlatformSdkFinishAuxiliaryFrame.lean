-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame
open RegistrationNativeBeaconFrontend (Trusted Owner)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
open RegistrationNativePlatformExtractedSdkFinish (BodyResult)

theorem tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) (result : BodyResult n KemSK source)
    (supported : result∈support (RegistrationNativeFinishLifetime.tree setup checks representation created wire pending packet owner scalar before)) :
    result.1.2.auxiliary=before.server.world.auxiliary ∧ result.2.server.world.auxiliary=before.server.world.auxiliary :=by
  let environment:=RegistrationWorldAgreementCompiler.erase before.server.world
  let body:=(RegistrationNativeFinishFactor.body (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup wire pending
    (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar).run environment
  have bodyHeld:=RegistrationNativePlatformSdkFinishAuxiliaryCore.body (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup wire pending
    (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar
  have actual : result.1∈support body :=by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeExperiment.trusted setup checks representation created source) body before
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have localFrame:=bodyHeld.1 environment result.1 actual
  have rawFrame:=RegistrationNativeLocalEnvironmentFrame.program setup checks representation created body (bodyHeld.2 environment) before result supported
  exact ⟨localFrame,congrArg RegistrationWorldAgreementCompiler.EnvState.auxiliary rawFrame.2⟩

theorem runner (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform) (reached : BodyResult n KemSK source×Platform)
    (supported : reached∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar before).run previous)) :
    reached.1.1.2.auxiliary=before.server.world.auxiliary ∧ reached.1.2.server.world.auxiliary=before.server.world.auxiliary :=by
  have actual:=RegistrationNativePlatformHashReceipt.native_support coins _ reached.1 previous reached.2 supported
  exact tree setup checks representation created wire pending packet owner scalar before reached.1 actual

theorem commit (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform) (reached : BodyResult n KemSK source×Platform)
    (supported : reached∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar before).run previous)) :
    RegistrationNativePlatformSdkReification.persistent
      (RegistrationNativePlatformSdkReification.commitEnvironment reached.1.1.2 reached.1.2,reached.2)=
      RegistrationNativePlatformSdkReification.persistent (reached.1.2,reached.2) :=by
  have facts:=runner setup checks representation created wire pending packet owner scalar before coins previous reached supported
  have auxiliary : reached.1.1.2.auxiliary=reached.1.2.server.world.auxiliary :=facts.1.trans facts.2.symm
  simp only [RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
    RegistrationNativePlatformSdkReification.commitEnvironment,RegistrationWorldAgreementCompiler.join,auxiliary]
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.runner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.runner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame.commit
