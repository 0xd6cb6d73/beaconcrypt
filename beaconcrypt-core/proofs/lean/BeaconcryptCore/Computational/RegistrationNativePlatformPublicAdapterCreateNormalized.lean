-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBodyNormalization
/-! The complete constructor source callback factors through the actual physical store after erasing only the indexed observation transcript. Original source objects, RNG, private keys, cache, counters and persistent platform state remain exact. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)


variable (sourcePrevious : ChildOperations (RustT (AdapterBeaconConstructorNative.M n KemSK mlSource RegistrationServerRoleBackend.State (StateT P ProbComp))))
variable (physicalPrevious : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (generator : rand_core.TryCryptoRng R Error) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate mlSource))
variable (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
variable (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
  (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
variable (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator)
variable (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
open RegistrationNativePlatformPublicAdapterStore (Store erase)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned returned_exact store)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (strongPhysical)


def result (raw : RustM (Option Nat × Store n KemSK R P) × (Backend n KemSK × P)) :
    RustM (Option Nat × Store n KemSK R P) × (Backend n KemSK × P) :=
  (match raw.1 with
  | .fail error => .fail error
  | .div => .div
  | .ok returned => .ok (returned.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize returned.2),
    RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent raw.2)

omit original originalCrypto in
theorem finish (before : Store n KemSK R P) (returned : RustM (AdapterBeaconConstructorBody.Outcome R))
    (after : Backend n KemSK × P) :
    result (RegistrationNativePlatformPublicAdapterCreateStore.finish before returned after) =
      RegistrationNativePlatformPublicAdapterCreateStore.finish
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) returned
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent after) := by
  cases returned <;> rfl

noncomputable def source (keyId : U64) (identityKey mlKey : Slice U8) (before : Store n KemSK R P) :=
  result <$> RegistrationNativePlatformPublicAdapterCreatePhysical.run coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey before

include ml signing prekey kemContract in
theorem stable (keyId : U64) (identityKey mlKey : Slice U8) (before : Store n KemSK R P) :
    source coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey before =
      source coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) := by
  have law := RegistrationNativePlatformPublicAdapterCreateBodyNormalization.platform coins setup checks representation created view physicalPrevious generator kem ml signing prekey kemContract
    keyId identityKey mlKey before.rng before.backend.1 before.backend.2
  have observed := congrArg (fun work => (fun raw => RegistrationNativePlatformPublicAdapterCreateStore.finish
    (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) raw.1.1 (raw.1.2,raw.2)) <$> work) law
  unfold source RegistrationNativePlatformPublicAdapterCreatePhysical.run RegistrationNativePlatformPublicAdapterCreateStore.run
  simp only [Functor.map_map,finish,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_idempotent]
  simpa only [Functor.map_map,Prod.map_def,id_eq,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent] using observed

noncomputable def physical
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) : Store n KemSK R P :=
  RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (erase before.base.objects)

theorem query (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterCreatePhysical.dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before) =
    source coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey
      (physical setup view views created credential current before) := by
  have projected : RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterCreatePhysical.dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before) =
    result <$> RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterCreatePhysical.dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before) := by
    unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
    conv_rhs => erw [Functor.map_map]
    rfl
  rw [projected,RegistrationNativePlatformPublicAdapterCreatePhysical.query]
  exact stable coins setup checks representation created view physicalPrevious generator kem ml signing prekey kemContract keyId identityKey mlKey (erase before.base.objects)

include sourcePrevious ml signing prekey kemContract in
theorem normal (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (keyId : U64) (identityKey mlKey : Slice U8) (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (output : RustM (Option Nat × Store n KemSK R P) × (Backend n KemSK × P))
    (supported : output∈support (source coins setup checks representation created view physicalPrevious generator keyId identityKey mlKey
      (physical setup view views created credential current before))) :
    ∃reply next,output=(.ok (reply,next),next.backend) := by
  rw [←query coins setup checks representation created view sourcePrevious physicalPrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before,
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw] at supported
  erw [support_map] at supported
  obtain ⟨packet,_possible,same⟩ := supported
  let call := RegistrationNativePlatformPublicAdapterCreatePhysical.dispatch coins setup checks representation created view sourcePrevious generator kem ml signing prekey kemContract views credential parsing keyId identityKey mlKey current before
  exact ⟨call.observe (returned call packet),physical setup view views created credential _ (store call packet),same.symm⟩


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized.normal
