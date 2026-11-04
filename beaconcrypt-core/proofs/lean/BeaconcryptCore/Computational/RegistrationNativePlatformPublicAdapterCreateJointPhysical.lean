-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical
/-! The existing constructor joint tree has an exact interpretation on the retained physical backend. The same five primitive stages and returned RNG are used on both sides; the proof derives each source query projection internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterCreatePrimitives (Full project)
variable {n : Nat} {I KemSK R P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (kem : AdapterBeaconConstructorKem.Representation view R)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)
variable (ml : R → ProbComp (Option (RegistrationNativeMldsa.Credential source) × R))
variable (signing : R → ProbComp (PqxdhJointIdentity.IdentitySeed × R))
variable (prekey : R → ProbComp (PqxdhJointGapDh.ScalarBytes × R))

noncomputable def sourceHandler : QueryImpl (RegistrationNativePlatformPublicAdapterCreateProgram.Spec source R) SourceM :=
  RegistrationNativePlatformPublicAdapterCreateProgram.handler
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created) (ml rng))
    (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created) (signing rng))
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created) (prekey rng))
    (AdapterBeaconConstructorKemLift.joint coins setup view kem)

noncomputable def hash (request : registration.HashRequest) : PhysicalM CtxRomAuth.CtxDigest :=fun before =>
  simulateQ coins ((RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created
    (.inr (.inl (RegistrationInputs.hashBytes request)))).run before)

noncomputable def handler : QueryImpl (RegistrationNativePlatformPublicAdapterCreateProgram.Spec source R) PhysicalM :=
  RegistrationNativePlatformPublicAdapterCreateProgram.handler
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (ml rng))
    (hash coins setup checks representation created)
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (signing rng))
    (fun rng => simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) (prekey rng))
    (RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint view coins setup kem)

omit material ed in
private theorem mk_apply {S A : Type} {m : Type → Type} (work : S → m (A × S)) (before : S) :
    (StateT.mk work) before = work before := rfl
omit material ed in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

omit material ed in
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value,before)) <$> work := by
  change (StateT.lift work : StateT S m A).run before = _
  rw [StateT.run_lift,bind_pure_comp]

private noncomputable def sampleImpl {A : Type} (work : ProbComp A) : QueryImpl (Unit →ₒ A) SourceM :=fun _ =>
  simulateQ (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created) work

omit material ed in
private theorem sample_source {A : Type} (work : ProbComp A) (before : Full n KemSK source) :
    Prod.map id project <$>
      ((sampleImpl coins setup checks representation created work).flattenStateT.flattenStateT ()).run before =
      (simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) work).run (project before) := by
  have law := RegistrationNativePlatformPublicAdapterCreatePrimitives.program_source (n:=n) (source:=source)
    coins setup checks representation created work before
  unfold RegistrationNativePlatformPublicAdapterCreatePrimitives.flatUniform at law
  rw [RegistrationNativePlatformPublicAdapterCreatePrimitives.flatten_source] at law
  simp only [Functor.map_map] at law
  simpa only [sampleImpl,QueryImpl.flattenStateT,StateT.run_mk,mk_apply,map_apply,StateT.run_map,Functor.map_map] using law

theorem query_source (query : (RegistrationNativePlatformPublicAdapterCreateProgram.Spec source R).Domain)
    (before : Full n KemSK source) :
    Prod.map id project <$>
      ((sourceHandler coins setup checks representation created view kem ml signing prekey).flattenStateT.flattenStateT query).run before =
    (handler coins setup checks representation created view kem ml signing prekey query).run (project before) := by
  rcases query with rng | request | rng | rng | rng
  · exact sample_source coins setup checks representation created (ml rng) before
  · have law := RegistrationNativePlatformPublicAdapterCreatePrimitives.hash_source coins setup checks representation created request before
    simpa only [sourceHandler,handler,RegistrationNativePlatformPublicAdapterCreateProgram.handler,
      RegistrationNativePlatformPublicAdapterCreatePrimitives.flatHash,QueryImpl.flattenStateT,
      StateT.run_mk,mk_apply,map_apply,StateT.run_map,Functor.map_map,hash,StateT.run,
      RegistrationNativePlatformPublicAdapterCreateProgram.Spec,OracleSpec.Range,OracleSpec.add_apply_inr,
      OracleSpec.add_apply_inl,OracleSpec.ofFn] using law
  · exact sample_source coins setup checks representation created (signing rng) before
  · exact sample_source coins setup checks representation created (prekey rng) before
  · have law := RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint_source view coins setup kem rng before.1.1 before.1.2 before.2
    dsimp only [sourceHandler,handler,RegistrationNativePlatformPublicAdapterCreateProgram.handler,QueryImpl.flattenStateT,
      AdapterBeaconConstructorKemLift.joint,StateT.run]
    simp only [mk_apply,lift_apply,map_apply,Functor.map_map]
    exact law

theorem program_source {A : Type}
    (work : OracleComp (RegistrationNativePlatformPublicAdapterCreateProgram.Spec source R) A)
    (before : Full n KemSK source) :
    Prod.map id project <$>
      (simulateQ (sourceHandler coins setup checks representation created view kem ml signing prekey).flattenStateT.flattenStateT work).run before =
    (simulateQ (handler coins setup checks representation created view kem ml signing prekey) work).run (project before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  exact query_source coins setup checks representation created view kem ml signing prekey

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateJointPhysical.program_source
