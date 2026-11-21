-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical
/-! The actual constructor body is interpreted by source-only primitive dictionaries on the physical backend. Its exact object/RNG result and reached backend/platform state are the erasure of the same selected SDK common run. All native leaves are derived from original individual primitive contracts. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody
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
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  AdapterBeaconConstructorBody.withInputs (m:=SourceM) generator keyId serverId mlPin rng

noncomputable def physical (previous : ChildOperations (RustT PhysicalM)) (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :=
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created)
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  AdapterBeaconConstructorBody.withInputs (m:=PhysicalM) generator keyId serverId mlPin rng

variable (generator : rand_core.TryCryptoRng R Error) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
variable (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
  (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
variable (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator)

noncomputable def outcome (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) :=
  AdapterBeaconConstructorJoint.sourceResult generator view setup.joint _ signing _ _ prekey keyId serverId

include kemContract in
theorem source_tree (previous : ChildOperations (RustT SourceM))
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :
    source coins setup checks representation created view previous generator keyId serverId mlPin rng = RustT.lift
      (outcome setup view generator signing prekey keyId serverId <$>
        simulateQ (RegistrationNativePlatformPublicAdapterCreateJointPhysical.sourceHandler coins setup checks representation created view kem signing.joint prekey.joint)
          (RegistrationNativePlatformPublicAdapterCreateProgram.program (view.edPublic serverId) mlPin keyId rng)) := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  let leaves := RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves coins setup checks representation created view previous generator kem signing prekey kemContract
  have law := AdapterBeaconConstructorNative.source_body coins setup checks representation created generator view kem leaves keyId serverId mlPin rng
  unfold AdapterBeaconConstructorNative.joint at law
  rw [← RegistrationNativePlatformPublicAdapterCreateProgram.joint_source generator view setup.joint _ leaves.ed _ _ leaves.kx
    (AdapterBeaconConstructorKemLift.joint coins setup view kem) (view.edPublic serverId) mlPin keyId rng] at law
  exact law

include kemContract in
theorem physical_tree (previous : ChildOperations (RustT PhysicalM))
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :
    physical coins setup checks representation created view previous generator keyId serverId mlPin rng = RustT.lift
      (outcome setup view generator signing prekey keyId serverId <$>
        simulateQ (RegistrationNativePlatformPublicAdapterCreateJointPhysical.handler coins setup checks representation created view kem signing.joint prekey.joint)
          (RegistrationNativePlatformPublicAdapterCreateProgram.program (view.edPublic serverId) mlPin keyId rng)) := by
  let uniform := RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.physicalGenerators coins setup checks representation created view
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.crypto view uniform
  let : ChildOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterCreateDictionaries.children previous (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
  let mappedEd := RegistrationNativePlatformPublicAdapterCreateGeneration.signing uniform (RegistrationNativePlatformPublicAdapterCreateKem.physical view coins) generator view setup.joint _ signing
  let mappedKx := RegistrationNativePlatformPublicAdapterCreateDictionaries.prekeyContract setup view uniform generator prekey
  have law := AdapterBeaconConstructorJoint.source_program generator view setup.joint _ mappedEd _ _ mappedKx
    (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem) keyId serverId mlPin rng
    (by rfl)
    (RegistrationNativePlatformPublicAdapterCreateKemPhysical.operation view coins setup kem generator kemContract)
  rw [← RegistrationNativePlatformPublicAdapterCreateProgram.joint_source generator view setup.joint _ mappedEd _ _ mappedKx
    (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem) (view.edPublic serverId) mlPin keyId rng] at law
  exact law

include signing prekey kemContract in
theorem body_source (sourcePrevious : ChildOperations (RustT SourceM))
    (physicalPrevious : ChildOperations (RustT PhysicalM))
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id backend <$> (RegistrationNativePlatformExtractedSdkCreate.close
      (source coins setup checks representation created view sourcePrevious generator keyId serverId mlPin rng).run).run before =
    (physical coins setup checks representation created view physicalPrevious generator keyId serverId mlPin rng).run.run (backend before) := by
  rw [source_tree coins setup checks representation created view generator kem signing prekey kemContract,
    physical_tree coins setup checks representation created view generator kem signing prekey kemContract]
  have law := RegistrationNativePlatformPublicAdapterCreateJointPhysical.program_source
    coins setup checks representation created view kem signing.joint prekey.joint
    (RegistrationNativePlatformPublicAdapterCreateProgram.program (source:=mlSource) (view.edPublic serverId) mlPin keyId rng)
    ((before.beacons,RegistrationWorldAgreementCompiler.erase before.server.world),before)
  rw [RegistrationNativePlatformPublicAdapterCreatePrimitives.flatten_source] at law
  have observed := congrArg (fun work => Prod.map (fun value => RustM.ok (outcome setup view generator signing prekey keyId serverId value)) id <$> work) law
  have initial : RegistrationNativePlatformPublicAdapterCreatePrimitives.project
      ((before.beacons,RegistrationWorldAgreementCompiler.erase before.server.world),before) = backend before := by
    unfold RegistrationNativePlatformPublicAdapterCreatePrimitives.project
    rw [RegistrationNativeLocalStatePatch.assemble_self]
  rw [initial] at observed
  simp only [Functor.map_map] at observed
  simpa only [RegistrationNativePlatformExtractedSdkCreate.close,RustT.run_lift,StateT.run_map,StateT.run,map_apply,
    Functor.map_map,RegistrationNativePlatformPublicAdapterCreatePrimitives.project,Prod.map_def,id_eq,Function.comp_apply] using observed


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.source_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.source_tree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.physical_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.physical_tree
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateBody.body_source
