-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishEffectInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
/-! Actual corrected Beacon installation and abort have explicit complete Native owner, World, kernel, binding, private-pool and cost poststates. Ready is derived separately from the source InitSent relation and actual crypto frame; this file adds no successful-install premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishTerminal
open RegistrationNativeBeaconFrontend (Owner Phase)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def setPhase (index : Nat) (phase : Phase) (owners : List (Owner source)) : List (Owner source) :=
  match owners[index]? with
  | none => owners
  | some selected => owners.set index {selected with phase}

def installed (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) (before : Native) : Native :=
  {before with
    beacons := setPhase index (.established ⟨completed.control, completed.binding, completed.application⟩) before.beacons
    server := {before.server with world := {before.server.world with world :=
      (AdapterPublicFinishEffectInstall.installed owner.worldOwner
        ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel before.server.world.world.1,
        before.server.world.world.2)}}}

theorem install (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.install index owner completed)).run before =
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)), installed index owner completed before) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run, bind_pure_comp]
  change (fun result => (result.1.1.1, {result.2 with
      beacons := result.1.1.2
      server := {result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1}})) <$>
    ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((do
        let installed : Bool ← RegistrationNativeBeaconFrontend.effect (.inr (.installBeacon owner.worldOwner
          ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (.known completed.kernel)))
        if installed then
          RegistrationNativeBeaconFrontend.updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
          pure (RustM.ok (some (TranscriptAuthParts.absSlice completed.application)))
        else RegistrationNativeBeaconFrontend.abort owner *> pure (RustM.ok none) :
        RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes))).run before.beacons).run
          (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) = _
  simp only [RegistrationNativeBeaconFrontend.effect, RegistrationNativeBeaconFrontend.updatePhase,
    StateT.run_bind, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, simulateQ_map, simulateQ_bind, simulateQ_spec_query]
  rw [AdapterPublicFinishEffectInstall.native setup checks representation created owner.worldOwner _ completed.kernel before ready]
  simp only [map_pure, pure_bind, ite_true]
  rfl

def abortedWorld (index : Nat) (world : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  {PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner index .aborted)) world with
    owners := world.owners.set index (.inactive .aborted)}

theorem abort_effect (index : Nat) (world : PqxdhRecordLiftWorld.State n) (ready : PqxdhRecordLiftWorld.BeaconReady world index) :
    (PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .aborted))).run world = pure (true, abortedWorld index world) := by
  change world.owners[index]? = some (.inactive .initSent) at ready
  change (PqxdhRecordLiftWorld.capability (.advanceOwner index .aborted)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner index .aborted)) world) = _
  simp only [PqxdhRecordLiftWorld.capability, StateT.run, PqxdhRecordLiftWorld.chargeEffect, ready, PqxdhRecordLiftWorld.LegalAdvance, ite_true]
  rfl

theorem abort_native_effect (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (before : Native) (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 index) :
    (RegistrationNativeExperiment.trusted setup checks representation created source (.inl (.inr (.advanceOwner index .aborted)))).run before =
      pure (true, {before with server := {before.server with world := {before.server.world with world :=
        (abortedWorld index before.server.world.world.1, before.server.world.world.2)}}}) := by
  simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  change (fun result => (result.1, {before with server := {before.server with world := {before.server.world with world :=
    (result.2, before.server.world.world.2)}}})) <$>
      (PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .aborted))).run before.server.world.world.1 = _
  rw [abort_effect index _ ready, map_pure]

def aborted (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (before : Native) : Native :=
  {before with
    beacons := setPhase index (.aborted control) before.beacons
    server := {before.server with world := {before.server.world with world :=
      (abortedWorld owner.worldOwner before.server.world.world.1, before.server.world.world.2)}}}

theorem abort (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (RegistrationNativeExperiment.beacon setup checks representation created (do
      RegistrationNativeBeaconFrontend.updatePhase index (.aborted control)
      RegistrationNativeBeaconFrontend.abort owner
      pure (RustM.ok (none : Option Pqxdh.Bytes)))).run before = pure (.ok none, aborted index owner control before) := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run, bind_pure_comp]
  change (fun result => (result.1.1.1, {result.2 with
      beacons := result.1.1.2
      server := {result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1}})) <$>
    ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((do
        RegistrationNativeBeaconFrontend.updatePhase index (.aborted control)
        RegistrationNativeBeaconFrontend.abort owner
        pure (RustM.ok (none : Option Pqxdh.Bytes)) :
        RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Pqxdh.Bytes))).run before.beacons).run
          (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) = _
  simp only [RegistrationNativeBeaconFrontend.abort, RegistrationNativeBeaconFrontend.effect,
    RegistrationNativeBeaconFrontend.updatePhase, StateT.run_bind, StateT.run_lift, StateT.run_map,
    StateT.run_modify, bind_pure_comp, pure_bind, Functor.map_map,
    simulateQ_map, simulateQ_spec_query]
  rw [abort_native_effect setup checks representation created owner.worldOwner before ready]
  simp only [map_pure]
  rfl

theorem installed_owner (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) (before : Native)
    (found : before.beacons[index]? = some owner) :
    (installed index owner completed before).beacons[index]? = some {owner with phase := .established ⟨completed.control, completed.binding, completed.application⟩} := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  change (setPhase index _ before.beacons)[index]? = _
  rw [setPhase, found]
  exact List.getElem?_set_self within

theorem installed_world (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (installed index owner completed before).server.world.world.1.owners[owner.worldOwner]? =
      some (.established ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel) := by
  change before.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent) at ready
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp ready
  change (before.server.world.world.1.owners.set owner.worldOwner _)[owner.worldOwner]? = _
  exact List.getElem?_set_self within

theorem aborted_owner (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (before : Native)
    (found : before.beacons[index]? = some owner) :
    (aborted index owner control before).beacons[index]? = some {owner with phase := .aborted control} := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  change (setPhase index _ before.beacons)[index]? = _
  rw [setPhase, found]
  exact List.getElem?_set_self within

theorem aborted_world (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    (aborted index owner control before).server.world.world.1.owners[owner.worldOwner]? = some (.inactive .aborted) := by
  change before.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent) at ready
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp ready
  change (before.server.world.world.1.owners.set owner.worldOwner _)[owner.worldOwner]? = _
  exact List.getElem?_set_self within

theorem phase_fusion (index : Nat) (first last : Phase) (owners : List (Owner source)) :
    setPhase index last (setPhase index first owners) = setPhase index last owners := by
  cases found : owners[index]? with
  | none => simp only [setPhase, found]
  | some owner =>
      obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
      simp only [setPhase, found, List.getElem?_set_self within, List.set_set]

end BeaconcryptCore.Computational.RegistrationNativeFinishTerminal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort_native_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort_native_effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.abort

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.installed_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.installed_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.installed_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.installed_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.aborted_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.aborted_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.aborted_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.aborted_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.phase_fusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishTerminal.phase_fusion
