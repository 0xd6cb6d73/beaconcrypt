-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster

/-! Actual public owner finishing, including ordinary translated references and selected private-scalar restoration, executes the original native Main finishing command. The two finite metadata conditions are internal initialized-controller invariants, not restrictions on the original secrecy event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationNativePublicSourceExecution (execute)
open RegistrationNativePublicSourceEffects (toPrivate fromPrivate)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The actual mixed frontend's complete finishing command preserves the whole native owner roster, pool, current environment and reached World under the named source view. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (roots : Roots)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State n KemSK source)
    (coherent : RegistrationNativeBeaconCoherence.Holds (owners scalar before.1.beacons))
    (empty : before.1.environment.recordRequests = []) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept publicPrekey (.inr (.finish index packet)))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.finish index packet))).run
          (restore roots scalar before.1 before.2) := by
  change Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.finish setup source index packet))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run
            (restore roots scalar before.1 before.2)
  calc
    _ = RegistrationNativePublicSourceOwnerWorld.privateObserve roots before.1 <$>
        (simulateQ (RegistrationNativeOrdinaryFinishSourceNative.trusted setup wire route
          (RegistrationNativeMldsa.owned source credential) created.seed scalar)
          (((RegistrationNativeBeaconFrontend.finish setup source wire index packet).run
            (owners scalar before.1.beacons)).run before.1.environment)).run (toPrivate before.2) := by
      rw [RegistrationNativePublicSourceOwnerLayout.beacon_run]
      have native := RegistrationNativeOrdinaryFinishSourceRoster.finish_source setup wire route
        (RegistrationNativeMldsa.owned source credential) created.seed scalar index packet before.1.beacons coherent
        before.1.environment empty (Std.Array.repeat 227#usize 0#u8) (toPrivate before.2)
      have mapped := congrArg (fun distribution => RegistrationNativePublicSourceOwnerWorld.observe roots before.1 <$> distribution) native
      simp only [Functor.map_map, Prod.map_def, id_eq,
        RegistrationNativeOrdinaryFinishSourceRoster.publicView, RegistrationNativeOrdinaryFinishSourceRoster.nativeView,
        RegistrationNativePublicSourceOwnerLayout.rebuild,
        RegistrationNativePublicSourceOwnerWorld.observe, RegistrationNativeOrdinaryFinishSourceFrame.drop,
        fromPrivate, project, restore, RegistrationBeaconReferenceNativeRecord.erase,
        nativeView, RegistrationServerMaterialSourceState.nativeView] at mapped ⊢
      convert mapped using 1; rfl
    _ = _ := RegistrationNativePublicSourceOwnerWorld.program_source setup checks wire route representation created scalar credential roots
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet) before
      (RegistrationNativeTrustedAllowed.finish_allowed setup wire index packet (owners scalar before.1.beacons) before.1.environment)

end BeaconcryptCore.Computational.RegistrationNativePublicSourceFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceFinish.finish_source
