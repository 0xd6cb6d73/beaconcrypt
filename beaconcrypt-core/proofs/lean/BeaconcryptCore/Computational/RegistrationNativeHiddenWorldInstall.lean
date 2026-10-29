-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedInstallation

/-! A cached, unused hidden reference installs exactly the paired native concrete kernel, including its populated AD and complete source control. The explicit projection removes only the private seed cache/accounting and role-use markers. Protocol records, all primitive counters, CTX cache, produced frames and public metadata remain literal. The unused-role condition must be derived or charged as an alias event by the whole client; this module does not replace repeated native successes with refusals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall
open PqxdhRecordLiftInterface (Slot PeerBinding BeaconShell)
open PqxdhRecordLiftWorld (State kernel installServer installBeacon)
variable {n : Nat}

def view (before : State n) : State n :=
  { before with seeds := PqxdhRecordLiftLazyTable.initial, used := fun _ _ => false }

/-- The installation view keeps every concrete record and shared primitive field. -/
theorem view_fields (before : State n) :
    (view before).server = before.server ∧ (view before).owners = before.owners ∧
      (view before).ownerRaw = before.ownerRaw ∧ (view before).produced = before.produced ∧
      (view before).primitive = before.primitive := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One actual unused Server-role installation preserves its complete semantic outcome when its already-cached seed is represented by the corresponding native kernel. -/
theorem server_install (keyId : U64) (binding : PeerBinding) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .server = false) :
    Prod.map id view <$> (installServer keyId binding (.hidden slot)).run before =
      Prod.map id view <$> (installServer keyId binding (.known (kernel .server seed))).run before := by
  cases found : before.server with
  | none => simp only [installServer, StateT.run, found, map_pure]
  | some server =>
      simp only [installServer, StateT.run, found, PqxdhRecordLiftWorld.Unused, unused, and_true]
      split
      · have resolved := PqxdhRecordLiftWorld.resolve_hit .server slot before seed cached
        simp only [StateT.run] at resolved
        rw [resolved]
        simp only [PqxdhRecordLiftWorld.resolve, pure_bind, map_pure,
          PqxdhRecordLiftWorld.markUsed, Prod.map, id_eq, view]
        rfl
      · simp only [map_pure]

/-- The actual Beacon lifecycle guard and shell stay unchanged when an unused cached hidden seed supplies the native completed kernel. -/
theorem beacon_install (owner : Nat) (shell : BeaconShell) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .beacon = false) :
    Prod.map id view <$> (installBeacon owner shell (.hidden slot)).run before =
      Prod.map id view <$> (installBeacon owner shell (.known (kernel .beacon seed))).run before := by
  simp only [installBeacon, StateT.run]
  by_cases ready : PqxdhRecordLiftWorld.BeaconReady before owner
  · simp only [PqxdhRecordLiftWorld.Unused, unused, ready, and_self, ite_true]
    have resolved := PqxdhRecordLiftWorld.resolve_hit .beacon slot before seed cached
    simp only [StateT.run] at resolved
    rw [resolved]
    simp only [PqxdhRecordLiftWorld.resolve, pure_bind, map_pure,
      PqxdhRecordLiftWorld.markUsed, Prod.map, id_eq, view]
    rfl
  · simp only [PqxdhRecordLiftWorld.Unused, unused, ready, false_and, ite_false, map_pure]

/-- The actual counted environment effect charges the same administrative request in both representations and retains the same complete semantic Server result. -/
theorem server_effect (keyId : U64) (binding : PeerBinding) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .server = false) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.hidden slot)))).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.known (kernel .server seed))))).run before := by
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId binding (.hidden slot))) before
  change Prod.map id view <$> (installServer keyId binding (.hidden slot)).run charged =
    Prod.map id view <$> (installServer keyId binding (.known (kernel .server seed))).run charged
  exact server_install keyId binding slot seed charged cached unused

/-- The counted Beacon installation has the same actual lifecycle guard and source shell in both cached representations. -/
theorem beacon_effect (owner : Nat) (shell : BeaconShell) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .beacon = false) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installBeacon owner shell (.hidden slot)))).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installBeacon owner shell (.known (kernel .beacon seed))))).run before := by
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden slot))) before
  change Prod.map id view <$> (installBeacon owner shell (.hidden slot)).run charged =
    Prod.map id view <$> (installBeacon owner shell (.known (kernel .beacon seed))).run charged
  exact beacon_install owner shell slot seed charged cached unused

end BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.view_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.view_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.server_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.server_install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.beacon_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.beacon_install
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.server_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.server_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.beacon_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall.beacon_effect
