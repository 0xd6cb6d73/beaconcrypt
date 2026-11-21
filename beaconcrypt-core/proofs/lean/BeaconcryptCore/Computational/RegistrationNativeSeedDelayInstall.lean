-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayFrames
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayNormalize
import BeaconcryptCore.Computational.PqxdhDeploymentBackend

/-! Actual installation guards inspect only the current public lifecycle and role-use bit. Admitted resolution queries the one persistent seed cache before installing the exact role kernel; the subsequent map and used marker are cache frames. This proves commutation for the actual normalized installation, including refusal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall
open PqxdhRecordLiftWorld (State Server)
open PqxdhRecordLiftInterface (Slot PeerBinding BeaconShell)
open RegistrationNativeSeedDelayCore (lens mask)
open Classical
open RegistrationNativeSeedDelayNormalize (resolve_commutes)
open LazyOracleDiscard (Commutes)
variable {n : Nat}

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

noncomputable def finishServer (keyId : U64) (binding : PeerBinding) (server : Server)
    (slot : Slot n) (kernel : ratchet.concrete.ConcreteRatchetKernel) : StateT (State n) ProbComp Bool := fun before =>
  let next := PqxdhRecordLiftWorld.markUsed before .server (.hidden slot)
  let peers := Function.update server.records.server.peers keyId
    (some ⟨binding.identity, kernel, binding.associatedArray server.records.server.identity⟩)
  pure (true, { next with server := some { server with records :=
    { server.records with server := { server.records.server with peers := peers } } } })

def finishBeacon (owner : Nat) (shell : BeaconShell) (owners : List PqxdhRecordLiftBeacon.Phase) (slot : Slot n)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) : StateT (State n) ProbComp Bool := fun before =>
  let next := PqxdhRecordLiftWorld.markUsed before .beacon (.hidden slot)
  pure (true, { next with owners := owners.set owner (.established shell kernel) })

private theorem finishServer_commutes (keyId : U64) (binding : PeerBinding) (server : Server)
    (slot : Slot n) (kernel : ratchet.concrete.ConcreteRatchetKernel) : Commutes lens (finishServer keyId binding server slot kernel) := by
  apply LazyOracleDiscard.commutes_frame
  intro before cache
  simp only [finishServer, PqxdhRecordLiftWorld.markUsed, StateT.run, lens, map_pure]

private theorem finishBeacon_commutes (owner : Nat) (shell : BeaconShell) (owners : List PqxdhRecordLiftBeacon.Phase) (slot : Slot n)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) : Commutes lens (finishBeacon owner shell owners slot kernel) := by
  apply LazyOracleDiscard.commutes_frame
  intro before cache
  simp only [finishBeacon, PqxdhRecordLiftWorld.markUsed, StateT.run, lens, map_pure]

noncomputable def serverBranch (keyId : U64) (binding : PeerBinding) (slot : Slot n) (selected : Option Server × Bool) :
    StateT (State n) ProbComp Bool :=
  match selected.1 with
  | none => RegistrationNativeSeedDelayCore.normalize (pure false)
  | some server => if server.records.server.peers keyId = none ∧ selected.2 = false then do
      let kernel ← RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.resolve .server (.hidden slot))
      finishServer keyId binding server slot kernel
    else RegistrationNativeSeedDelayCore.normalize (pure false)

noncomputable def beaconBranch (owner : Nat) (shell : BeaconShell) (slot : Slot n)
    (selected : List PqxdhRecordLiftBeacon.Phase × Bool) : StateT (State n) ProbComp Bool :=
  if selected.1[owner]? = some (.inactive .initSent) ∧ selected.2 = false then do
    let kernel ← RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.resolve .beacon (.hidden slot))
    finishBeacon owner shell selected.1 slot kernel
  else RegistrationNativeSeedDelayCore.normalize (pure false)

/-- Actual normalized Server installation dispatches on its existing Server and role-use bit, then resolves its seed without exposing it. -/
theorem server_shape (keyId : U64) (binding : PeerBinding) (slot : Slot n) (before : State n) :
    (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot))).run before =
      (serverBranch keyId binding slot (before.server, before.used slot .server)).run before := by
  cases found : before.server with
  | none => simp only [RegistrationNativeSeedDelayCore.normalize, PqxdhRecordLiftWorld.installServer, serverBranch, StateT.run,
      mask, found, state_pure_apply, map_pure, Prod.map_def, id_eq]
  | some server =>
      simp only [RegistrationNativeSeedDelayCore.normalize, PqxdhRecordLiftWorld.installServer, serverBranch, StateT.run,
        mask, found, PqxdhRecordLiftWorld.Unused]
      split
      · simp only [StateT.monad_bind_def, StateT.bind, finishServer, RegistrationNativeSeedDelayCore.normalize, map_bind,
          bind_map_left, map_pure, Prod.map_def, id_eq, PqxdhRecordLiftWorld.markUsed, mask]
        simp only [found]
        rfl
      · simp only [RegistrationNativeSeedDelayCore.normalize, StateT.run, state_pure_apply, map_pure, Prod.map_def, id_eq, mask, found]

/-- The Beacon lifecycle gate precedes the same hidden query, and refused completion retains every operational field. -/
theorem beacon_shape (owner : Nat) (shell : BeaconShell) (slot : Slot n) (before : State n) :
    (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden slot))).run before =
      (beaconBranch owner shell slot (before.owners, before.used slot .beacon)).run before := by
  simp only [RegistrationNativeSeedDelayCore.normalize, PqxdhRecordLiftWorld.installBeacon, beaconBranch, StateT.run,
    mask, PqxdhRecordLiftWorld.Unused, PqxdhRecordLiftWorld.BeaconReady]
  split
  · simp only [StateT.monad_bind_def, StateT.bind, finishBeacon, RegistrationNativeSeedDelayCore.normalize, map_bind,
      bind_map_left, map_pure, Prod.map_def, id_eq, PqxdhRecordLiftWorld.markUsed, mask]
    rfl
  · simp only [RegistrationNativeSeedDelayCore.normalize, StateT.run, state_pure_apply, map_pure, Prod.map_def, id_eq, mask]

/-- The literal Server installation commutes with completion at every slot; current records and role-use markers stay exact. -/
theorem server_commutes (keyId : U64) (binding : PeerBinding) (slot : Slot n) :
    Commutes lens (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.installServer keyId binding (.hidden slot))) := by
  apply PqxdhDeploymentBackend.commutes_dispatch lens _
    (fun before => (before.server, before.used slot .server)) (fun _ _ => rfl)
    (serverBranch keyId binding slot) (server_shape keyId binding slot)
  rintro ⟨current, used⟩
  cases current with
  | none => exact RegistrationNativeSeedDelayNormalize.normalize_commutes _ (LazyOracleDiscard.commutes_pure lens false)
  | some server =>
      simp only [serverBranch]
      split
      · exact LazyOracleDiscard.commutes_bind lens (resolve_commutes .server (.hidden slot))
          (finishServer_commutes keyId binding server slot)
      · exact RegistrationNativeSeedDelayNormalize.normalize_commutes _ (LazyOracleDiscard.commutes_pure lens false)

/-- The literal Beacon installation obeys the same seed-delay law with its actual native lifecycle and populated shell. -/
theorem beacon_commutes (owner : Nat) (shell : BeaconShell) (slot : Slot n) :
    Commutes lens (RegistrationNativeSeedDelayCore.normalize (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden slot))) := by
  apply PqxdhDeploymentBackend.commutes_dispatch lens _
    (fun before => (before.owners, before.used slot .beacon)) (fun _ _ => rfl)
    (beaconBranch owner shell slot) (beacon_shape owner shell slot)
  rintro ⟨current, used⟩
  simp only [beaconBranch]
  split
  · exact LazyOracleDiscard.commutes_bind lens (resolve_commutes .beacon (.hidden slot))
      (finishBeacon_commutes owner shell current slot)
  · exact RegistrationNativeSeedDelayNormalize.normalize_commutes _ (LazyOracleDiscard.commutes_pure lens false)

end BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.server_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.server_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.beacon_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.beacon_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.server_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.server_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.beacon_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSeedDelayInstall.beacon_commutes
