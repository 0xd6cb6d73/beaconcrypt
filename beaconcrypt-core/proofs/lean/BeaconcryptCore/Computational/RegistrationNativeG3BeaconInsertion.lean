-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3ServerInsertion
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconService

/-! The actual Beacon post-record admission/install continuation has the same semantic World outcome for its source-consumed canonical kernel and an unused cached hidden reference. Complete native control, populated binding, application, rejection and shell are retained. The local cache/use receipts do not assert the global alias or lazy-service coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion
open PqxdhRecordLiftInterface (EnvEffects Slot)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat}

/-- Every supported successful actual record program retains the whole generated post-sequence-one Beacon kernel. -/
theorem program_kernel (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (completed : registration.CompletedBeacon)
    (supported : .ok (.Ok completed) ∈ support (RegistrationNativePairedBeaconService.program source descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material seed))) :
    completed.kernel = PqxdhRecordLiftWorld.kernel .beacon seed := by
  rw [RegistrationNativePairedBeaconService.program_split, support_map] at supported
  obtain ⟨value, _possible, equal⟩ := supported
  cases value with
  | fail error => cases equal
  | div => cases equal
  | ok result =>
      cases result with
      | Err aborted => cases equal
      | Ok original =>
          simp only [RegistrationBeaconSeed.replace, RustM.ok.injEq, core.result.Result.Ok.injEq] at equal
          cases equal
          rfl

/-- The actual Beacon shell/admission branch, full public result and shared World agree under both canonical kernel representations. -/
theorem after (owner : Nat) (sender : U64) (slot : Slot n)
    (completed : registration.CompletedBeacon) (seed : PqxdhRecordLiftSeed.Seed)
    (canonical : completed.kernel = PqxdhRecordLiftWorld.kernel .beacon seed)
    (before : PqxdhRecordLiftWorld.State n) (cached : before.seeds.1 slot = some seed)
    (unused : before.used slot .beacon = false) :
    Prod.map id view <$>
      (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedBeaconService.after owner sender
        (fun value => .known value.kernel) (.ok (.Ok completed)))).run before =
      Prod.map id view <$>
        (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedBeaconService.after owner sender
          (fun _ => .hidden slot) (.ok (.Ok completed)))).run before := by
  have actual := RegistrationNativeHiddenWorldInstall.beacon_effect owner
    ⟨sender, completed.control, completed.binding.associated_data⟩ slot seed before cached unused
  let finish : Bool → RustM RegistrationNativePairedBeaconService.Result := fun installed =>
    if installed then .ok (.Ok ⟨completed.control, completed.binding, completed.application⟩)
    else .ok (.Err ⟨sender⟩)
  have mapped := congrArg (fun work => (fun result => (finish result.1, result.2)) <$> work) actual.symm
  simp only [RegistrationNativePairedBeaconService.after]
  rw [canonical]
  rw [bind_pure_comp, bind_pure_comp]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped
  convert mapped using 1 <;> rfl

/-- Native record rejection and all supported successful kernels keep their exact final admission semantics. -/
theorem after_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (result : RustM RegistrationBeaconRecordExecutor.Result)
    (supported : result ∈ support (RegistrationNativePairedBeaconService.program source descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material seed)))
    (before : PqxdhRecordLiftWorld.State n) (cached : before.seeds.1 slot = some seed)
    (unused : before.used slot .beacon = false) :
    Prod.map id view <$>
      (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedBeaconService.after owner sender
        (fun value => .known value.kernel) result)).run before =
      Prod.map id view <$>
        (simulateQ PqxdhRecordLiftWorld.effects (RegistrationNativePairedBeaconService.after owner sender
          (fun _ => .hidden slot) result)).run before := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err aborted => rfl
      | Ok completed =>
          exact after owner sender slot completed seed (program_kernel source descriptor material seed completed supported)
            before cached unused

end BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.program_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.program_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.after_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BeaconInsertion.after_program
