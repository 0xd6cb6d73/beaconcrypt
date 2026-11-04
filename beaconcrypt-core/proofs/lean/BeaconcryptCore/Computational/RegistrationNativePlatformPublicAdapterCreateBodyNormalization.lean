-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization
/-! The full literal constructor, including original-slice parsing and terminal Rust results, commutes with removal of the indexed KEM observation log. Actual private objects, RNG, keys, cache, counters and platform state are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization
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
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)


open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
variable (previous : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (generator : rand_core.TryCryptoRng R Error) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate mlSource))
variable (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
variable (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
  (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
variable (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator)

include ml signing prekey kemContract in
theorem body (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateBody.physical coins setup checks representation created view previous generator keyId serverId mlPin rng).run.run before =
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateBody.physical coins setup checks representation created view previous generator keyId serverId mlPin rng).run.run (erase before) := by
  rw [RegistrationNativePlatformPublicAdapterCreateBody.physical_tree coins setup checks representation created view generator kem ml signing prekey kemContract]
  simp only [RustT.run_lift,StateT.run_map,Functor.map_map]
  have law := RegistrationNativePlatformPublicAdapterCreateNormalization.stable coins setup checks representation created view kem ml.joint signing.joint prekey.joint
    (RegistrationNativePlatformPublicAdapterCreateProgram.program (view.edPublic serverId) mlPin keyId rng) before
  have observed := congrArg (fun work => Prod.map (fun value => RustM.ok (RegistrationNativePlatformPublicAdapterCreateBody.outcome setup view generator ml signing prekey keyId serverId value)) id <$> work) law
  simpa only [Functor.map_map,Prod.map_def,id_eq] using observed

omit material ed original originalCrypto in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

include ml signing prekey kemContract in
theorem full (keyId : U64) (identityKey mlKey : Slice U8) (rng : R) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view previous generator keyId identityKey mlKey rng).run.run before =
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view previous generator keyId identityKey mlKey rng).run.run (erase before) := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created)
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  unfold RegistrationNativePlatformPublicAdapterCreateSource.physical
  rw [AdapterBeaconConstructorBody.body]
  unfold AdapterBeaconConstructorBody.source
  cases parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey with
  | fail error =>
    simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
  | div =>
    simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
  | ok result =>
    simp only [lift_ok,pure_bind]
    cases result with
    | Err error =>
      simp only [AdapterBeaconConstructorBody.reject,RustT.run_pure,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
    | Ok serverId =>
      cases parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
          1952#usize core.U8.Insts.CoreMarkerCopy mlKey with
      | fail error =>
        simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
      | div =>
        simp only [RustT.run_bind,RustT.run_liftRust,pure_bind,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
      | ok result =>
        simp only [lift_ok,pure_bind]
        cases result with
        | Err error =>
          simp only [AdapterBeaconConstructorBody.reject,RustT.run_pure,StateT.run_pure,map_pure,Prod.map_def,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]
        | Ok mlPin =>
          exact body coins setup checks representation created view previous generator kem ml signing prekey kemContract keyId serverId mlPin rng before

include ml signing prekey kemContract in
theorem platform (keyId : U64) (identityKey mlKey : Slice U8) (rng : R) (before : Backend n KemSK) (previousP : P) :
    Prod.map (Prod.map id erase) id <$> ((RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view previous generator keyId identityKey mlKey rng).run.run before).run previousP =
    Prod.map (Prod.map id erase) id <$> ((RegistrationNativePlatformPublicAdapterCreateSource.physical coins setup checks representation created view previous generator keyId identityKey mlKey rng).run.run (erase before)).run previousP := by
  have law := congrArg (fun work => work.run previousP)
    (full coins setup checks representation created view previous generator kem ml signing prekey kemContract keyId identityKey mlKey rng before)
  simpa only [StateT.run_map,Prod.map_def,id_eq] using law

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.body
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization.platform
