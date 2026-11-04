-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishWorld
import BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishAdmission
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK A B C : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

omit platform in
theorem ready_after_crypto (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before authenticated agreed opened : Native)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (native : owner.phase = .initSent pending scalar)
    (authentication : OracleComp RegistrationAuthenticationExecutor.Spec A)
    (agreement : OracleComp RegistrationAgreementExecutor.Spec B)
    (record : OracleComp RegistrationRecordPrimitives.Spec C) (wire : RegistrationNativeWire.Wire)
    (authReply : A) (agreeReply : B) (recordReply : C)
    (authReached : (authReply, authenticated) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) authentication)).run before))
    (agreeReached : (agreeReply, agreed) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar) agreement)).run authenticated))
    (recordReached : (recordReply, opened) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) record)).run agreed)) :
    PqxdhRecordLiftWorld.BeaconReady opened.server.world.world.1 owner.worldOwner := by
  have initial := AdapterPublicFinishWorld.initSent_ready view setup.joint before.pool self owner
    before.server.world.world.1 related pending prekey oneTime kem scalar stored native
  have authOwners := RegistrationNativeBeaconPrefixSafe.authentication_owners setup checks representation created authentication before (authReply, authenticated) authReached
  have agreeOwners := RegistrationNativeBeaconPrefixSafe.agreement_owners setup checks representation created owner scalar agreement authenticated (agreeReply, agreed) agreeReached
  have recordOwners := RegistrationNativeBeaconPrefixSafe.record_owners setup checks representation created wire record agreed (recordReply, opened) recordReached
  change opened.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent)
  rw [recordOwners, agreeOwners, authOwners]
  exact initial
omit platform in
theorem install_after_crypto (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before authenticated agreed opened : Native)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem) (native : owner.phase = .initSent pending scalar)
    (authentication : OracleComp RegistrationAuthenticationExecutor.Spec A)
    (agreement : OracleComp RegistrationAgreementExecutor.Spec B)
    (record : OracleComp RegistrationRecordPrimitives.Spec C) (wire : RegistrationNativeWire.Wire)
    (authReply : A) (agreeReply : B) (recordReply : C) (completed : registration.CompletedBeacon)
    (authReached : (authReply, authenticated) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) authentication)).run before))
    (agreeReached : (agreeReply, agreed) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar) agreement)).run authenticated))
    (recordReached : (recordReply, opened) ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) record)).run agreed)) :
    (PqxdhRecordLiftWorld.installBeacon owner.worldOwner
      ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (.known completed.kernel)).run opened.server.world.world.1 =
      pure (true, {opened.server.world.world.1 with owners := opened.server.world.world.1.owners.set owner.worldOwner (.established ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel)}) := by
  exact AdapterPublicFinishWorld.install_known _ _ _ opened.server.world.world.1
    (ready_after_crypto view setup checks representation created self owner before authenticated agreed opened related
      pending prekey oneTime kem scalar stored native authentication agreement record wire authReply agreeReply recordReply
      authReached agreeReached recordReached)
end BeaconcryptCore.Refinement.AdapterPublicFinishAdmission
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishAdmission.ready_after_crypto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishAdmission.ready_after_crypto

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishAdmission.install_after_crypto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishAdmission.install_after_crypto
