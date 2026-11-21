-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal
import BeaconcryptCore.Computational.RegistrationNativePublicBundleMask

/-! Whole public native outgoing publication restores the private selected scalar without changing any observable callback, signing history, current environment, public owner or generated-key state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationNativePublicSourceExecution (execute)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Actual whole Main bundle publication is the native source command on the complete restored roster and reached World. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat) (roots : Roots)
    (index : Nat) (before : State n KemSK source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner (setup.dh.publicKey scalar) before.1.beacons) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr (.bundle index)))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.bundle index))).run
          (restore roots scalar before.1 before.2) := by
  have publicKey : ∀ owner, (before.1.beacons.map RegistrationNativePublicOwners.restore)[selectedOwner]? = some owner →
      owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) := by
    intro owner found
    simp only [List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨exposed, present, rfl⟩ := found
    have chosen := canonical selectedOwner exposed present
    simp only [RegistrationNativePublicOwnerMask.At, ite_true] at chosen
    exact chosen.2
  have equation := RegistrationNativePublicBundleMask.bundle_mask (n := n) setup source wire index selectedOwner scalar
    (setup.dh.publicKey scalar) (before.1.beacons.map RegistrationNativePublicOwners.restore) before.1.environment publicKey
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selectedOwner scalar (setup.dh.publicKey scalar) before.1.beacons canonical] at equation
  change Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selectedOwner (setup.dh.publicKey scalar)
          (RegistrationNativeBeaconFrontend.bundle setup source wire index)))).run before = _
  apply RegistrationNativePublicSourceLocal.local_source setup checks wire route representation created scalar credential selectedOwner
    (setup.dh.publicKey scalar) roots _ (RegistrationNativeBeaconFrontend.bundle setup source wire index) before
  · simp only [RegistrationNativePublicOwnerRestore.restore_pack]
    exact equation
  · exact RegistrationNativeTrustedAllowed.bundle_allowed setup wire index _ before.1.environment

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBundle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBundle.bundle_source
