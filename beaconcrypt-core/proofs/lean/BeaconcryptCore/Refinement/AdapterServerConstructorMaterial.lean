-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The initialized Server material relation is derived from its actual key object, empty std stores and same native fingerprint path. Metadata frames are computed from the literal hash/sampler, never supplied as whole-controller assumptions. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorMaterial
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
local notation "World" => PqxdhRecordLiftWorld.State n
local notation "M" => StateT World ProbComp

omit material platform primitive [AdapterServerConstructorPrimitive.Standard] generators in
private theorem hash_fields (input : Pqxdh.Bytes) (before : World)
    (result : CtxRomAuth.CtxDigest×World)
    (supported : result∈support ((PqxdhRecordLiftWorld.effects (.inr (.hash input))).run before)) :
    result.2.server=before.server ∧ result.2.owners=before.owners := by
  simp only [PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.capability,
    PqxdhRecordLiftWorld.chargeEffect,PqxdhRecordLiftWorld.sampled,StateT.run,
    bind_pure_comp,Functor.map_map,support_map] at supported
  obtain ⟨inner,_called,rfl⟩:=supported
  exact ⟨rfl,rfl⟩

theorem finish (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
    (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
    (edSample : M (Option PqxdhJointIdentity.IdentitySeed))
    (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint edSample)
    (mlSample : M (Option (RegistrationNativeMldsa.Credential mlSource)))
    (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view mlSample)
    (identityIndex : Nat) (identifier : U64) (prepared : AdapterServerConstructorJoint.Prepared mlSource)
    (before after : World) (initial : RegistrationNativeExperiment.Initial n KemSK mlSource)
    (empty : before.server=none)
    (supported : (some initial,after)∈support ((AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared).run before)) :
    Server view views initial.created initial.credential
      (AdapterServerConstructorJoint.object generator view views objects setup.joint edSample ed mlSample ml identifier prepared)
      initial.state.server ∧
    initial.state.beacons=[] ∧ initial.state.server.sessions=[] ∧
    initial.state.server.world.world.1.owners=before.owners := by
  simp only [AdapterServerConstructorStartup.finish,RegistrationWorldServerFrontend.start,
    StateT.run,bind_assoc,pure_bind,mem_support_bind_iff] at supported
  obtain ⟨installed,installedSupport,supported⟩:=supported
  simp only [PqxdhRecordLiftWorld.initializeServer,empty,mem_support_pure_iff] at installedSupport
  subst installed
  have pin:=RegistrationWorldServerFrontend.initializePin_native
    (⟨PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys prepared.seed).ed25519,identifier⟩ : pqxdh.ServerBinding)
    prepared.credential.publicKey
    ((PqxdhJointDhExtractFamily.empty,
      ⟨RegistrationServerRoleBackend.empty,[],[],
        ({before with server:=some (PqxdhRecordLiftWorld.importedServer
          (PqxdhLiveServerConstruction.initialized setup.joint identityIndex identifier .generated prepared.seed))},[])⟩) :
      RegistrationWorldServerReplay.Global n RegistrationServerRoleBackend.State)
  simp only [StateT.run] at pin
  simp only [PqxdhLiveServerConstruction.initialized] at supported pin
  rw [pin] at supported
  simp only [RegistrationWorldServerCompletion.capability,StateT.run,bind_map_left,
    mem_support_bind_iff] at supported
  obtain ⟨hashed,hashSupport,supported⟩:=supported
  simp only [mem_support_pure_iff] at supported
  obtain ⟨actualHash,actualSupport,pinOutput⟩:=hashSupport
  simp only [mem_support_pure_iff] at pinOutput
  subst hashed
  cases supported
  have fields:=hash_fields (PqxdhRefinement.absBytes prepared.credential.publicKey) _ actualHash actualSupport
  have identity:=AdapterServerConstructorJoint.identity generator view views objects setup.joint edSample ed mlSample ml identityIndex identifier prepared
  have empties:=AdapterServerConstructorObjects.empty views objects identifier (ed.realize prepared.seed) (ml.realize prepared.credential)
  refine ⟨?_,rfl,rfl,fields.2⟩
  refine ⟨identity,rfl,rfl,rfl,rfl,empties.1,?_⟩
  refine ⟨PqxdhRecordLiftWorld.importedServer (PqxdhLiveServerConstruction.initialized setup.joint identityIndex identifier .generated prepared.seed),fields.1,rfl,rfl,?_⟩
  exact empties.2
end BeaconcryptCore.Refinement.AdapterServerConstructorMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorMaterial.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorMaterial.finish
