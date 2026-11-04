-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishMaterial
import BeaconcryptCore.Refinement.AdapterPublicFinishRecord
import BeaconcryptCore.Computational.RegistrationNativeFinishTerminal
/-! The literal source first-record result/wrap now has exact returnedSelf and public byte projections for successful installation and abort. These source values are related to the full corrected native terminal state and its exact World slot, with original private material and final KEM-pool state allowed to differ. This is endpoint support for the whole source lifecycle join, not a claim that arbitrary source callbacks satisfy the native profile. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Owner)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

def completedSelf (self : beaconcrypt_public_wrapper.beacon.Beacon) (completed : registration.CompletedBeacon) :
    beaconcrypt_public_wrapper.beacon.Beacon :=
  {self with
    identity_key_kid := completed.binding.assigned_key_id
    state := .Established completed.control completed.binding ⟨⟨some completed.kernel⟩⟩}

def sourceResult (self : beaconcrypt_public_wrapper.beacon.Beacon) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    RustM AdapterPublicFinishBody.Result :=
  AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result)

def bytes (returned : RustM AdapterPublicFinishBody.Result) : RustM (Option Pqxdh.Bytes) := do
  let (optional, _self) ← returned
  pure (match optional with
    | .None => none
    | .Some plaintext => some (TranscriptAuthParts.absSlice plaintext))

theorem source_completed (self : beaconcrypt_public_wrapper.beacon.Beacon) (completed : registration.CompletedBeacon) :
    sourceResult self (.ok (.Ok completed)) = .ok (.Some completed.application, completedSelf self completed) := by
  simp only [sourceResult, AdapterPublicFinishRecord.result, AdapterPublicWrapperCopy.install_exact,
    AdapterPublicFinishRecord.wrap, bind_tc_ok]
  rfl

theorem source_aborted (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconAborted) :
    sourceResult self (.ok (.Err control)) = .ok (.None, {self with state := .Aborted control}) := rfl

theorem completed_bytes (self : beaconcrypt_public_wrapper.beacon.Beacon) (completed : registration.CompletedBeacon) :
    bytes (sourceResult self (.ok (.Ok completed))) = .ok (some (TranscriptAuthParts.absSlice completed.application)) := by
  rw [source_completed]
  rfl

theorem aborted_bytes (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconAborted) :
    bytes (sourceResult self (.ok (.Err control))) = .ok none := rfl

variable [platform : PublicWrapperPlatform.Platform]
variable {n : Nat}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

omit platform in
theorem installed_material (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (originalPool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint originalPool self owner world)
    (index : Nat) (completed : registration.CompletedBeacon) (before : Native)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    AdapterPublicWrapperState.Beacon view joint (RegistrationNativeFinishTerminal.installed index owner completed before).pool
      (completedSelf self completed) {owner with phase := .established ⟨completed.control, completed.binding, completed.application⟩}
      (RegistrationNativeFinishTerminal.installed index owner completed before).server.world.world.1.owners[owner.worldOwner]? := by
  rw [RegistrationNativeFinishTerminal.installed_world index owner completed before ready]
  exact AdapterPublicFinishMaterial.installed view joint originalPool before.pool self owner world related completed

omit platform in
theorem aborted_material (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (originalPool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint originalPool self owner world)
    (index : Nat) (control : pqxdh.BeaconAborted) (before : Native)
    (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes) (initial : owner.phase = .initSent pending scalar)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner) :
    AdapterPublicWrapperState.Beacon view joint (RegistrationNativeFinishTerminal.aborted index owner control before).pool
      {self with state := .Aborted control} {owner with phase := .aborted control}
      (RegistrationNativeFinishTerminal.aborted index owner control before).server.world.world.1.owners[owner.worldOwner]? := by
  rw [RegistrationNativeFinishTerminal.aborted_world index owner control before ready]
  exact AdapterPublicFinishMaterial.aborted view joint originalPool before.pool self owner world related pending scalar initial control

end BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.source_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.source_completed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.source_aborted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.source_aborted

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.completed_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.completed_bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.aborted_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.aborted_bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.installed_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.installed_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.aborted_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint.aborted_material
