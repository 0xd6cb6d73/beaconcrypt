-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal
import BeaconcryptCore.Computational.RegistrationNativePublicCreateMask

/-! The actual mixed native constructor restores the selected private scalar at exactly the eager source birth, including every original preflight failure, dummy draw, indexed key and public allocation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationNativePublicSourceExecution (execute)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Actual whole Main creation is the eager private-scalar source command on the complete restored native state. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat) (roots : Roots)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State n KemSK source)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selectedOwner (setup.dh.publicKey scalar) before.1.beacons) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) (.inr (.create edPin mlPin keyId)))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selectedOwner scalar
          (.inr (.create edPin mlPin keyId))).run (restore roots scalar before.1 before.2) := by
  have equation := RegistrationNativePublicCreateMask.create_mask (n := n) setup source selectedOwner scalar edPin mlPin keyId
    (before.1.beacons.map RegistrationNativePublicOwners.restore) before.1.environment
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selectedOwner scalar (setup.dh.publicKey scalar) before.1.beacons canonical] at equation
  change Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selectedOwner (setup.dh.publicKey scalar)
          (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)))).run before = _
  apply RegistrationNativePublicSourceLocal.local_source setup checks wire route representation created scalar credential selectedOwner
    (setup.dh.publicKey scalar) roots _ (RegistrationNativeScalarEager.create setup source selectedOwner scalar edPin mlPin keyId) before
  · simp only [RegistrationNativePublicOwnerRestore.restore_pack]
    exact equation
  · rw [← equation, map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind
      (RegistrationNativeTrustedAllowed.create_allowed setup edPin mlPin keyId _ before.1.environment)
      (fun _ => allQueriesSatisfy_pure _ _)

end BeaconcryptCore.Computational.RegistrationNativePublicSourceCreate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceCreate.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceCreate.create_source
