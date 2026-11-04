-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishObservation
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment

/-! Current-runtime opaque Ed creation and corrected assigned-ID finish restore the full original native/platform run. Generation is executed privately by the ordinary joint source, and source ownership is used only to interpret already-generated handles. No challenged Ed seed is supplied to the executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (Owned)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- Full actual finish retains early consumption, mandatory authentication, agreement, record opening, installation and every terminal failure. -/
private theorem old_finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK source × SourceState) (owned : Owned setup.joint before) :
    Prod.map id RegistrationNativeIdentityMainSource.project <$>
      (RegistrationNativeIdentityMainSource.interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityFinishRun.finish setup source wire index packet))).run before =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run (RegistrationNativeIdentityMainSource.project before) := by
  rw [RegistrationNativeIdentityMainBeacon.beacon_source]
  have finite := RegistrationNativePlatformIdentityFinishObservation.finish_source setup checks representation created wire index packet
    before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ owned
  have lifted := congrArg (fun distribution => RegistrationNativeIdentityMainOld.assemble <$> distribution) finite
  simp only [Functor.map_map] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityMainOld.beacon_source setup checks representation created _ _ _


noncomputable def create (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) : M n KemSK Platform source (RustM (Option Nat)) :=
  RegistrationNativePlatformIdentityMain.beacon setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId))

noncomputable def finish (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK Platform source (RustM (Option Pqxdh.Bytes)) :=
  RegistrationNativePlatformIdentityMain.beacon setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native (RegistrationNativePlatformIdentityFinishRun.finish setup source wire index packet))

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem lift_source (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativeIdentityMain.M n KemSK source Value) (native : StateT Native ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (law : Prod.map id RegistrationNativeIdentityMainSource.project <$>
      (RegistrationNativeIdentityMainSource.interpret joint work).run (before.1.1, before.2) =
      native.run (RegistrationNativeIdentityMainSource.project (before.1.1, before.2))) :
    Prod.map id project <$> (interpret joint (liftMain work)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins native).run
          (project before).1).run (project before).2 := by
  rw [RegistrationNativePlatformIdentityMain.interpret_lift]
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.1.2))) <$> distribution) law
  simp only [RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformMldsaProgram.lift_coins,
    StateT.run, lift_apply, Functor.map_map, Prod.map, id_eq, project] at same ⊢
  exact same

/-- Actual current creation has the exact same generated source row, real native costs and optional failure, retaining the original P. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : (State n KemSK source × Platform) × SourceState) (owned : Owned setup.joint (before.1.1, before.2)) :
    Prod.map id project <$>
      (interpret setup.joint (create setup edPin mlPin keyId checks representation created)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon setup checks representation created (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))).run
          (project before).1).run (project before).2 := by
  rw [create, RegistrationNativePlatformIdentityMain.beacon_native]
  exact lift_source setup.joint _ _ before
    (RegistrationNativeIdentityMainLifecycle.create_source setup checks representation created edPin mlPin keyId (before.1.1, before.2) owned)

/-- The actual source corrected finish, including copy-before-install and assigned sender ID, restores every native/P failure and success state. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : (State n KemSK source × Platform) × SourceState) (owned : Owned setup.joint (before.1.1, before.2)) :
    Prod.map id project <$>
      (interpret setup.joint (finish setup checks representation created wire index packet)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon setup checks representation created (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet))).run
          (project before).1).run (project before).2 := by
  rw [finish, RegistrationNativePlatformIdentityMain.beacon_native]
  exact lift_source setup.joint _ _ before
    (old_finish_source setup checks representation created wire index packet (before.1.1, before.2) owned)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle.create_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle.finish_source
