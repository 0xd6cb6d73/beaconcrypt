-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree
import BeaconcryptCore.Computational.RegistrationNativeFinishBodySafety
import BeaconcryptCore.Refinement.AdapterPublicFinishNormalized
/-! The complete actual corrected native Beacon finish is an explicit final-state projection of one shared logged cryptographic execution. The actual raw-body frame preserves World owners, source InitSent derives readiness, and terminal effects retain all primitive state and true counters. Optional rejection and every reached prefix remain in the same tree. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishLifetime
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeFinishTerminalTree (assemble execute bytes after)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

noncomputable def tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) :=
  (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((RegistrationNativeFinishFactor.body setup wire pending (match packet with | none => .None | some value => .Some value) owner scalar).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))).run before

theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (scalar : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) (before : Native)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before = (do
      let result ← tree setup checks representation created wire pending packet owner scalar before
      execute setup checks representation created index owner (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)
        result.1.1 before.beacons result.1.2 result.2) := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run, bind_pure_comp]
  change (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
    ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((RegistrationNativePlatformBeaconFinish.finish setup source wire index packet).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) = _
  rw [BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.native_tree setup wire index owner pending scalar packet before.beacons selected phase]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  rfl

theorem complete (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (scalar : PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket) (before : Native)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before =
      (fun result => (bytes result.1.1, after index owner (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending) result.1.1
        (assemble before.beacons result.1.2 result.2))) <$>
          tree setup checks representation created wire pending packet owner scalar before := by
  rw [program setup checks representation created wire index owner pending scalar packet before selected phase, map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  have owners : result.2.server.world.world.1.owners = before.server.world.world.1.owners := by
    cases packet with
    | none =>
        exact RegistrationNativeFinishBodySafety.raw_owners setup checks representation created wire pending .None owner scalar
          (RegistrationWorldAgreementCompiler.erase before.server.world) before result reached
    | some value =>
        exact RegistrationNativeFinishBodySafety.raw_owners setup checks representation created wire pending (.Some value) owner scalar
          (RegistrationWorldAgreementCompiler.erase before.server.world) before result reached
  have remained : PqxdhRecordLiftWorld.BeaconReady result.2.server.world.world.1 owner.worldOwner := by
    change result.2.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent)
    rw [owners]
    exact ready
  simpa only [Function.comp_apply] using RegistrationNativeFinishTerminalTree.execute_exact setup checks representation created index owner
    (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending) result.1.1 before.beacons result.1.2 result.2 remained


variable [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material] [ed : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]

theorem source_ready (view : BeaconcryptCore.Refinement.AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (packet : Option registration.ResponsePacket) (before : Native)
    (related : BeaconcryptCore.Refinement.AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before =
      (fun result => (bytes result.1.1, after index owner (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending) result.1.1
        (assemble before.beacons result.1.2 result.2))) <$>
          tree setup checks representation created wire pending packet owner scalar before :=
  complete setup checks representation created wire index owner pending scalar packet before selected phase
    (BeaconcryptCore.Refinement.AdapterPublicFinishWorld.initSent_ready view setup.joint before.pool self owner before.server.world.world.1 related pending prekey oneTime kem scalar stored phase)


end BeaconcryptCore.Computational.RegistrationNativeFinishLifetime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.source_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishLifetime.source_ready
