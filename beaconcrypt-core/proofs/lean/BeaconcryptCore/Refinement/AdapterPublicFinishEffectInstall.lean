-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishWorld
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def installed (index : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell) (kernel : ConcreteRatchetKernel)
    (world : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  {(PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon index shell (.known kernel))) world) with
    owners := world.owners.set index (.established shell kernel)}

theorem effect (index : Nat) (shell : PqxdhRecordLiftInterface.BeaconShell) (kernel : ConcreteRatchetKernel)
    (world : PqxdhRecordLiftWorld.State n) (ready : PqxdhRecordLiftWorld.BeaconReady world index) :
    (PqxdhRecordLiftWorld.effects (.inr (.installBeacon index shell (.known kernel)))).run world =
      pure (true, installed index shell kernel world) := by
  change (PqxdhRecordLiftWorld.installBeacon index shell (.known kernel)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon index shell (.known kernel))) world) = _
  exact AdapterPublicFinishWorld.install_known index shell kernel _ ready

theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (shell : PqxdhRecordLiftInterface.BeaconShell) (kernel : ConcreteRatchetKernel)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 index) :
    (RegistrationNativeExperiment.trusted setup checks representation created source
      (.inl (.inr (.installBeacon index shell (.known kernel))))).run before =
      pure (true, {before with server := {before.server with world := {before.server.world with
        world := (installed index shell kernel before.server.world.world.1, before.server.world.world.2)}}}) := by
  simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  change (fun result => (result.1, {before with server := {before.server with world := {before.server.world with
    world := (result.2, before.server.world.world.2)}}})) <$>
    (PqxdhRecordLiftWorld.effects (.inr (.installBeacon index shell (.known kernel)))).run before.server.world.world.1 = _
  rw [effect index shell kernel _ ready, map_pure]
end BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.effect
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall.native
