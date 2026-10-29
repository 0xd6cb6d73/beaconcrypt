-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleObservation
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishObservation

/-! The actual whole-client Beacon operations recover original native creation, outgoing publication and full finish through concrete finite source laws. Credential ownership is an internal initialized source invariant, not a restriction on the native APP event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret project Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Full actual native creation preserves every source failure, actual private birth and native owner append. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
        (RegistrationNativeIdentityFrontend.create setup mlSource edPin mlPin keyId))).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)).run (project before) := by
  rw [RegistrationNativeIdentityMainBeacon.beacon_source]
  have finite := RegistrationNativeIdentitySourceConstruction.create_source setup checks representation created edPin mlPin keyId
    before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ owned
  have lifted := congrArg (fun distribution => RegistrationNativeIdentityMainOld.assemble <$> distribution) finite
  simp only [Functor.map_map] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityMainOld.beacon_source setup checks representation created _ _ _

/-- Full actual bundle publication retains all earlier Ed attempts, ML signing, encoding failures and owner phase changes. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
        (RegistrationNativeIdentityFrontend.bundle setup mlSource wire index))).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.bundle setup mlSource wire index)).run (project before) := by
  rw [RegistrationNativeIdentityMainBeacon.beacon_source]
  have finite := RegistrationNativeIdentityBundleObservation.bundle_source setup checks representation created wire index
    before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ owned
  have lifted := congrArg (fun distribution => RegistrationNativeIdentityMainOld.assemble <$> distribution) finite
  simp only [Functor.map_map] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityMainOld.beacon_source setup checks representation created _ _ _

/-- Full actual finish retains early consumption, mandatory authentication, agreement, record opening, installation and every terminal failure. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
        (RegistrationNativeIdentityFrontend.finish setup mlSource wire index packet))).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet)).run (project before) := by
  rw [RegistrationNativeIdentityMainBeacon.beacon_source]
  have finite := RegistrationNativeIdentityFinishObservation.finish_source setup checks representation created wire index packet
    before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ owned
  have lifted := congrArg (fun distribution => RegistrationNativeIdentityMainOld.assemble <$> distribution) finite
  simp only [Functor.map_map] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityMainOld.beacon_source setup checks representation created _ _ _

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.create_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.bundle_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle.finish_source
