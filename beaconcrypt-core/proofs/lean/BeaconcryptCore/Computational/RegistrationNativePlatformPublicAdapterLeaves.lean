-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
import BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad
/-! Source-local getters and container operations are lifted from the same persistent platform interpreter into either the complete analysis state or the retained physical backend. The actual leaf result and platform poststate are unchanged; no protocol-owner representation is available to the backend dictionary. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
variable {S P A : Type}

def lift (work : RustT (StateT P ProbComp) A) : RustT (StateT S (StateT P ProbComp)) A :=
  ⟨StateT.lift work.run⟩

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

@[instance_reducible] def localOperations
    (original : LocalOperations (RustT (StateT P ProbComp))) :
    LocalOperations (RustT (StateT S (StateT P ProbComp))) where
  auth_MldsaIdentity_public_key identity:=lift (original.auth_MldsaIdentity_public_key identity)
  auth_MldsaIdentity_sign_requested identity request:=lift (original.auth_MldsaIdentity_sign_requested identity request)
  ratchet_initial_ratchet_hkdf request:=lift (original.ratchet_initial_ratchet_hkdf request)
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher key:=
    lift (original.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher key)
  ratchet_execute_seal_request request:=lift (original.ratchet_execute_seal_request request)
  ratchet_execute_write_request request:=lift (original.ratchet_execute_write_request request)

variable [PublicWrapperPlatform.Allocator]

@[instance_reducible] def containerOperations
    (original : ContainerOperations (RustT (StateT P ProbComp))) :
    ContainerOperations (RustT (StateT S (StateT P ProbComp))) where
  setContains eq hash build allocate hashQuery equivalent collection query:=
    lift (original.setContains eq hash build allocate hashQuery equivalent collection query)
  setReserve eq hash build allocate collection capacity:=
    lift (original.setReserve eq hash build allocate collection capacity)
  setInsert eq hash build allocate collection key:=
    lift (original.setInsert eq hash build allocate collection key)
  mapContains eq hash build allocate hashQuery equivalent collection query:=
    lift (original.mapContains eq hash build allocate hashQuery equivalent collection query)
  mapReserve eq hash build allocate collection capacity:=
    lift (original.mapReserve eq hash build allocate collection capacity)
  mapEntry eq hash build allocate collection key:=
    lift (original.mapEntry eq hash build allocate collection key)
  vacantInsert allocate hash build vacant value:=
    lift (original.vacantInsert allocate hash build vacant value)

omit material platform ed [PublicWrapperPlatform.Allocator] in
theorem source {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
    (work : RustT (StateT P ProbComp) A) (before : RegistrationNativeExperiment.State n KemSK source)
    (previous : P) :
    Prod.map (Prod.map id backend) id <$>
      (((lift (S:=RegistrationNativeExperiment.State n KemSK source) work).run.run before).run previous)=
      (((lift (S:=Backend n KemSK) work).run.run (backend before)).run previous) := by
  simp only [lift,StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.localOperations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.localOperations

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.containerOperations' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.containerOperations

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves.source
