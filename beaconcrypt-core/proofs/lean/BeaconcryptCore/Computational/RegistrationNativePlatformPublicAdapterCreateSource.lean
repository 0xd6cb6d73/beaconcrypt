-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody
/-! The complete actual constructor entry preserves the adversary's original pin slices. Its pure parse failures and all terminal Rust results are retained in the same source/backend projection. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def source (previous : ChildOperations (RustT SourceM)) (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (identityKey mlKey : Slice U8) (rng : R) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m:=RustT SourceM) generator keyId identityKey mlKey rng

noncomputable def physical (previous : ChildOperations (RustT PhysicalM)) (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (identityKey mlKey : Slice U8) (rng : R) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created)
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m:=RustT PhysicalM) generator keyId identityKey mlKey rng


variable (generator : rand_core.TryCryptoRng R Error) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
variable (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
  (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
variable (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator)

omit material ed original originalCrypto in
private theorem closed_pure {A : Type} (value : A) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (RegistrationNativePlatformExtractedSdkCreate.close (pure value : SourceM A)).run before = pure (value,before) := by
  unfold RegistrationNativePlatformExtractedSdkCreate.close
  simp only [StateT.run_pure,map_pure]
  exact congrArg pure (congrArg (fun current => (value,current)) (RegistrationNativeLocalStatePatch.assemble_self before))

omit material ed original originalCrypto in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

include signing prekey kemContract in
theorem full_source (sourcePrevious : ChildOperations (RustT SourceM))
    (physicalPrevious : ChildOperations (RustT PhysicalM))
    (keyId : U64) (identityKey mlKey : Slice U8) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id backend <$> (RegistrationNativePlatformExtractedSdkCreate.close
      (source coins setup checks representation created view sourcePrevious generator keyId identityKey mlKey rng).run).run before =
    (physical coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey rng).run.run (backend before) := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children sourcePrevious (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created)
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children physicalPrevious (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  unfold source physical
  rw [AdapterBeaconConstructorBody.body,AdapterBeaconConstructorBody.body]
  unfold AdapterBeaconConstructorBody.source
  cases parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey with
  | fail error =>
    simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,closed_pure,StateT.run_pure,map_pure]
    rfl
  | div =>
    simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,closed_pure,StateT.run_pure,map_pure]
    rfl
  | ok result =>
    simp only [lift_ok,pure_bind]
    cases result with
    | Err error =>
      simp only [AdapterBeaconConstructorBody.reject,RustT.run_pure,closed_pure,StateT.run_pure,map_pure]
      rfl
    | Ok serverId =>
      cases parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
          1952#usize core.U8.Insts.CoreMarkerCopy mlKey with
      | fail error =>
        simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,closed_pure,StateT.run_pure,map_pure]
        rfl
      | div =>
        simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,closed_pure,StateT.run_pure,map_pure]
        rfl
      | ok result =>
        simp only [lift_ok,pure_bind]
        cases result with
        | Err error =>
          simp only [AdapterBeaconConstructorBody.reject,RustT.run_pure,closed_pure,StateT.run_pure,map_pure]
          rfl
        | Ok mlPin =>
          exact RegistrationNativePlatformPublicAdapterCreateBody.body_source coins setup checks representation created view
            generator kem signing prekey kemContract sourcePrevious physicalPrevious keyId serverId mlPin rng before

include signing prekey kemContract in
theorem full_platform (sourcePrevious : ChildOperations (RustT SourceM))
    (physicalPrevious : ChildOperations (RustT PhysicalM))
    (keyId : U64) (identityKey mlKey : Slice U8) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) (previous : P) :
    Prod.map (Prod.map id backend) id <$> ((RegistrationNativePlatformExtractedSdkCreate.close
      (source coins setup checks representation created view sourcePrevious generator keyId identityKey mlKey rng).run).run before).run previous =
    ((physical coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey rng).run.run (backend before)).run previous := by
  have law := congrArg (fun work => work.run previous)
    (full_source coins setup checks representation created view generator kem signing prekey kemContract
      sourcePrevious physicalPrevious keyId identityKey mlKey rng before)
  rw [StateT.run_map] at law
  exact law


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource.full_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource.full_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource.full_platform
