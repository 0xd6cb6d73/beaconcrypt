-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorReached
import BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The actual generated SDK constructor and the native owner constructor use one common source key-generation run. Pure registration is explicit proof administration after the SDK object returns; its source pre-registration snapshot is retained separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
variable {n : Nat} {I KemSK R Error Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def close (work : (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)) A) : StateT Native (StateT Platform ProbComp) A := fun before =>
  (fun result =>(result.1.1.1,RegistrationNativeFinishTerminalTree.assemble result.1.1.2 result.1.2 result.2)) <$>
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)).run before

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : V → W) (work : StateT S m V) (before : S) :
    (observe <$>work) before=(fun result =>(observe result.1,result.2)) <$>work before := by
  change (observe <$>work).run before=_
  rw [StateT.run_map]
  rfl

theorem lift_closed (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) :
    close (AdapterBeaconConstructorNative.lift coins setup checks representation created work)=
      RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created work) := by
  funext before
  change (close (AdapterBeaconConstructorNative.lift coins setup checks representation created work)).run before=_
  unfold close AdapterBeaconConstructorNative.lift RegistrationNativePlatformGenericBundle.liftLegacy
  change (fun result =>(result.1.1.1,RegistrationNativeFinishTerminalTree.assemble result.1.1.2 result.1.2 result.2)) <$>
    (simulateQ (fun query =>RegistrationNativePlatformInterpret.state coins
      (RegistrationNativeExperiment.trusted setup checks representation created source query))
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before=_
  rw [←RegistrationNativePlatformInterpret.state_simulate]
  unfold RegistrationNativePlatformInterpret.state RegistrationNativePlatformExperiment.liftNative
  rw [RegistrationNativeLocalStatePatch.beacon_run,simulateQ_map]
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R)

omit children in
theorem native_entry
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem) (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R) :
    Prod.fst <$> close (AdapterBeaconConstructorNative.entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)=
      RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId)) := by
  have equation := congrArg (close (n := n) (Platform := Platform) (source := source))
    (AdapterBeaconConstructorNative.native_entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)
  have mapped : close (Prod.fst <$> AdapterBeaconConstructorNative.entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)=
      Prod.fst <$> close (AdapterBeaconConstructorNative.entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng) := by
    funext before
    change (close (Prod.fst <$> AdapterBeaconConstructorNative.entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)).run before =
      (Prod.fst <$> close (AdapterBeaconConstructorNative.entry (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)).run before
    unfold RegistrationNativePlatformExtractedSdkCreate.close
    dsimp only [StateT.run]
    simp only [map_apply,Functor.map_map]
  rw [mapped,lift_closed] at equation
  exact equation

omit children in
theorem typed_source
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (identityBytes mldsaBytes : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityBytes=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mldsaBytes=.ok (.Ok mlPin)) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng
      (m := RustT (AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)))
      generator keyId identityBytes mldsaBytes rng=
    RustT.lift (AdapterBeaconConstructorNative.sourceResult coins setup checks representation created generator view kem leaves keyId serverId <$>
      AdapterBeaconConstructorNative.joint (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng) := by
  rw [AdapterBeaconConstructorNative.source_all coins setup checks representation created generator view kem leaves]
  unfold AdapterBeaconConstructorNative.sourceAll
  rw [parsed]
  change ((pure (core.result.Result.Ok serverId : core.result.Result _ ed.Error) : RustT _ _) >>= _)=_
  rw [pure_bind,parsedMl]
  change ((pure (core.result.Result.Ok mlPin : core.result.Result _ core.array.TryFromSliceError) : RustT _ _) >>= _)=_
  rw [pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.lift_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.lift_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.native_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.native_entry
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate.typed_source
