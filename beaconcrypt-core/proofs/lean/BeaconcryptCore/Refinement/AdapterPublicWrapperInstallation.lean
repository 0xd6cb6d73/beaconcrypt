-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish

/-! Known source kernels install without resolving private seed tables. The native administrative checks reduce to actual source slot readiness and map vacancy, so these local functional facts do not assume successful source-wrapper execution or protocol security. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation
open BeaconcryptCore.Computational PqxdhRecordLiftInterface PqxdhRecordLiftWorld
variable {n : Nat}

theorem beacon (before : State n) (owner : Nat) (shell : BeaconShell)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (ready : before.owners[owner]? = some (.inactive .initSent)) :
    (installBeacon owner shell (.known kernel)).run before =
      pure (true, { before with owners := before.owners.set owner (.established shell kernel) }) := by
  simp only [installBeacon, StateT.run, BeaconReady, Unused, ready, and_self, ↓reduceIte,
    resolve, markUsed]
  rfl

theorem server (before : State n) (records : PqxdhRecordLiftWorld.Server)
    (identifier : U64) (identity : PeerBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (present : before.server = some records) (vacant : records.records.server.peers identifier = none) :
    (installServer identifier identity (.known kernel)).run before =
      let installed := some ⟨identity.identity, kernel, identity.associatedArray records.records.server.identity⟩
      let peers := Function.update records.records.server.peers identifier installed
      let server := { records.records.server with peers := peers }
      let records := { records with records := { records.records with server := server } }
      pure (true, { before with server := some records }) := by
  simp only [installServer, StateT.run, present, Unused, vacant, and_self, ↓reduceIte,
    resolve, markUsed]
  rfl

end BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation.beacon

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperInstallation.server
