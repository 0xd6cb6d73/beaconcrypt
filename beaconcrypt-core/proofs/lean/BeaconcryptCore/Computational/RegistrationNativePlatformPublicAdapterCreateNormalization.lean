-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
/-! Constructor sampling, hashing and actual private-pair birth never read the indexed KEM observation transcript. Normalization removes only that transcript; the same object, RNG, key roster, shared cache, counters and platform state remain. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
variable {n : Nat} {I KemSK R P A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

theorem uniform (query : unifSpec.Domain) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created query).run before =
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created query).run (erase before) := by
  dsimp only [RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform,RegistrationNativePlatformSdkReification.backendLeaf,StateT.run]
  simp only [simulateQ_map,Functor.map_map]
  rfl

theorem sample (work : ProbComp A) (before : Backend n KemSK) :
    Prod.map id erase <$> (simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) work).run before =
    (simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) work).run (erase before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  exact uniform coins setup checks representation created

theorem hash (request : registration.HashRequest) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created request).run before =
    (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created request).run (erase before) := by
  dsimp only [RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash,RegistrationNativePlatformSdkReification.backendLeaf,StateT.run]
  simp only [simulateQ_map,Functor.map_map]
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (ml : R → ProbComp (Option (RegistrationNativeMldsa.Credential mlSource) × R))
variable (signing : R → ProbComp (PqxdhJointIdentity.IdentitySeed × R))
variable (prekey : R → ProbComp (PqxdhJointGapDh.ScalarBytes × R))

theorem kem_joint (rng : R) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem rng).run before =
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem rng).run (erase before) := by
  dsimp only [RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint,StateT.run]
  simp only [simulateQ_map,Functor.map_map]
  rfl

noncomputable def handler : QueryImpl (RegistrationNativePlatformPublicAdapterCreateProgram.Spec mlSource R)
    (StateT (Backend n KemSK) (StateT P ProbComp)) :=
  RegistrationNativePlatformPublicAdapterCreateProgram.handler
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (ml rng))
    (RegistrationNativePlatformPublicAdapterCreateJointPhysical.hash coins setup checks representation created)
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (signing rng))
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (prekey rng))
    (fun rng before => Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem rng).run before)

theorem query (request : (RegistrationNativePlatformPublicAdapterCreateProgram.Spec mlSource R).Domain) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformPublicAdapterCreateJointPhysical.handler coins setup checks representation created view kem ml signing prekey request).run before =
      (handler coins setup checks representation created view kem ml signing prekey request).run (erase before) := by
  rcases request with rng | request | rng | rng | rng
  · exact sample coins setup checks representation created (ml rng) before
  · exact hash coins setup checks representation created request before
  · exact sample coins setup checks representation created (signing rng) before
  · exact sample coins setup checks representation created (prekey rng) before
  · exact kem_joint coins setup view kem rng before

theorem program (work : OracleComp (RegistrationNativePlatformPublicAdapterCreateProgram.Spec mlSource R) A) (before : Backend n KemSK) :
    Prod.map id erase <$> (simulateQ (RegistrationNativePlatformPublicAdapterCreateJointPhysical.handler coins setup checks representation created view kem ml signing prekey) work).run before =
      (simulateQ (handler coins setup checks representation created view kem ml signing prekey) work).run (erase before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  exact query coins setup checks representation created view kem ml signing prekey

theorem stable (work : OracleComp (RegistrationNativePlatformPublicAdapterCreateProgram.Spec mlSource R) A) (before : Backend n KemSK) :
    Prod.map id erase <$> (simulateQ (RegistrationNativePlatformPublicAdapterCreateJointPhysical.handler coins setup checks representation created view kem ml signing prekey) work).run before =
    Prod.map id erase <$> (simulateQ (RegistrationNativePlatformPublicAdapterCreateJointPhysical.handler coins setup checks representation created view kem ml signing prekey) work).run (erase before) := by
  rw [program,program,RegistrationNativePlatformPublicAdapterPhysicalBackend.idempotent]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.hash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.kem_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.kem_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalization.stable
