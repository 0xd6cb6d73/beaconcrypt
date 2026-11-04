-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishWorld
open BeaconcryptCore.Computational PqxdhRefinement
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {source : RegistrationNativeMldsa.Source} {KemSK : Type}

omit platform in
theorem initSent_ready (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : PqxdhRecordLiftWorld.State n)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world.owners[owner.worldOwner]?)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem)
    (native : owner.phase = .initSent pending scalar) : PqxdhRecordLiftWorld.BeaconReady world owner.worldOwner := by
  have phase := related.phase
  simp only [stored, native, AdapterPublicWrapperState.Phase] at phase
  exact phase.2.2.2.2

omit material platform ed in
theorem install_known (index : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (kernel : ConcreteRatchetKernel) (world : PqxdhRecordLiftWorld.State n)
    (ready : PqxdhRecordLiftWorld.BeaconReady world index) :
    (PqxdhRecordLiftWorld.installBeacon index shell (.known kernel)).run world =
      pure (true, {world with owners := world.owners.set index (.established shell kernel)}) := by
  classical
  change (if PqxdhRecordLiftWorld.BeaconReady world index ∧ PqxdhRecordLiftWorld.Unused world .beacon (.known kernel) then _ else _) = _
  simp only [PqxdhRecordLiftWorld.Unused, and_true, ready, ite_true,
    PqxdhRecordLiftWorld.resolve, StateT.run_pure, pure_bind, PqxdhRecordLiftWorld.markUsed]

omit platform in
theorem source_install (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : PqxdhRecordLiftWorld.State n)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world.owners[owner.worldOwner]?)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem)
    (native : owner.phase = .initSent pending scalar) (completed : registration.CompletedBeacon) :
    (PqxdhRecordLiftWorld.installBeacon owner.worldOwner
      ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (.known completed.kernel)).run world =
      pure (true, {world with owners := world.owners.set owner.worldOwner (.established ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel)}) :=
  install_known _ _ _ world (initSent_ready view joint pool self owner world related pending prekey oneTime kem scalar stored native)
end BeaconcryptCore.Refinement.AdapterPublicFinishWorld
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishWorld.initSent_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishWorld.initSent_ready
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishWorld.install_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishWorld.install_known
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishWorld.source_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishWorld.source_install
