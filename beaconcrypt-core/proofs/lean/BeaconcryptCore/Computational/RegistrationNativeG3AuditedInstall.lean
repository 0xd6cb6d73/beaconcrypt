-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenWorldInstall

/-! A private audit of successful known-kernel installation records the same slot/role use as the actual hidden installation. Unlike the public installation view, this coupling retains the complete role-use map, so an adaptive proof can stop before a later repeated role. The audit is proof instrumentation on the known side; it changes no kernel, record, reply, CTX state or public binding. Its cached and unused local receipts are explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall
open PqxdhRecordLiftInterface (Slot Role PeerBinding BeaconShell)
open PqxdhRecordLiftWorld (State kernel installServer installBeacon markUsed)
variable {n : Nat}

def view (before : State n) : State n := { before with seeds := PqxdhRecordLiftLazyTable.initial }

def audit (role : Role) (slot : Slot n) (result : Bool × State n) : Bool × State n :=
  (result.1, if result.1 then markUsed result.2 role (.hidden slot) else result.2)

/-- Successful known installation audits exactly one role while retaining its literal reply and every semantic World coordinate. -/
theorem audit_fields (role : Role) (slot : Slot n) (result : Bool × State n) :
    (audit role slot result).1 = result.1 ∧
      RegistrationNativeHiddenWorldInstall.view (audit role slot result).2 =
        RegistrationNativeHiddenWorldInstall.view result.2 := by
  constructor
  · rfl
  · cases result with
    | mk reply before => cases reply <;> rfl

/-- Actual Server installation agrees with the successful-known audit while retaining the complete private role-use map. -/
theorem server (keyId : Std.U64) (binding : PeerBinding) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .server = false) :
    (Prod.map id view ∘ audit .server slot) <$>
      (installServer keyId binding (.known (kernel .server seed))).run before =
      Prod.map id view <$> (installServer keyId binding (.hidden slot)).run before := by
  cases found : before.server with
  | none => simp only [installServer, StateT.run, found, map_pure]; rfl
  | some server =>
      simp only [installServer, StateT.run, found, PqxdhRecordLiftWorld.Unused, unused, and_true]
      split
      · have resolved := PqxdhRecordLiftWorld.resolve_hit .server slot before seed cached
        simp only [StateT.run] at resolved
        rw [resolved]
        simp only [PqxdhRecordLiftWorld.resolve, pure_bind, map_pure,
          markUsed, audit, Function.comp_def, Prod.map_def, id_eq, view]
        rfl
      · simp only [map_pure]; rfl

/-- Actual Beacon installation has the same lifecycle gate and complete audited role-use map on success and refusal. -/
theorem beacon (owner : Nat) (shell : BeaconShell) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .beacon = false) :
    (Prod.map id view ∘ audit .beacon slot) <$>
      (installBeacon owner shell (.known (kernel .beacon seed))).run before =
      Prod.map id view <$> (installBeacon owner shell (.hidden slot)).run before := by
  simp only [installBeacon, StateT.run]
  by_cases ready : PqxdhRecordLiftWorld.BeaconReady before owner
  · simp only [PqxdhRecordLiftWorld.Unused, unused, ready, and_self, ite_true]
    have resolved := PqxdhRecordLiftWorld.resolve_hit .beacon slot before seed cached
    simp only [StateT.run] at resolved
    rw [resolved]
    simp only [PqxdhRecordLiftWorld.resolve, pure_bind, map_pure,
      markUsed, audit, Function.comp_def, Prod.map_def, id_eq, view]
    rfl
  · simp only [PqxdhRecordLiftWorld.Unused, unused, ready, false_and, ite_false, map_pure]
    rfl

/-- Administrative counting is literal on both Server installation paths; only the private seed-table view is erased. -/
theorem server_effect (keyId : Std.U64) (binding : PeerBinding) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .server = false) :
    (Prod.map id view ∘ audit .server slot) <$>
      (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.known (kernel .server seed))))).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.hidden slot)))).run before := by
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId binding (.hidden slot))) before
  change (Prod.map id view ∘ audit .server slot) <$>
    (installServer keyId binding (.known (kernel .server seed))).run charged =
      Prod.map id view <$> (installServer keyId binding (.hidden slot)).run charged
  exact server keyId binding slot seed charged cached unused

/-- The same counted audit law holds for the actual completed Beacon shell. -/
theorem beacon_effect (owner : Nat) (shell : BeaconShell) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.seeds.1 slot = some seed) (unused : before.used slot .beacon = false) :
    (Prod.map id view ∘ audit .beacon slot) <$>
      (PqxdhRecordLiftWorld.effects (.inr (.installBeacon owner shell (.known (kernel .beacon seed))))).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.effects (.inr (.installBeacon owner shell (.hidden slot)))).run before := by
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden slot))) before
  change (Prod.map id view ∘ audit .beacon slot) <$>
    (installBeacon owner shell (.known (kernel .beacon seed))).run charged =
      Prod.map id view <$> (installBeacon owner shell (.hidden slot)).run charged
  exact beacon owner shell slot seed charged cached unused

end BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.audit_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.audit_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.server_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.server_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.beacon_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall.beacon_effect
