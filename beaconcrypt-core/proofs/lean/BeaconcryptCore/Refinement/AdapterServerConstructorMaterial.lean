-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The initialized Server material relation is derived from its actual key object, empty std stores and pure native full-pin selection. The original joint Ed/ML samples and complete startup state remain; no hash callback or whole-controller conclusion is a premise. -/
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


theorem finish (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
    (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
    (edSample : M (Option PqxdhJointIdentity.IdentitySeed))
    (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint edSample)
    (mlSample : M (Option (RegistrationNativeMldsa.Credential mlSource)))
    (ml : AdapterServerConstructorGeneration.MldsaContract generator view mlSample)
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
  simp only [mem_support_pure_iff] at supported
  obtain ⟨pinned,rfl,supported⟩ := supported
  cases supported
  have identity:=AdapterServerConstructorJoint.identity generator view views objects setup.joint edSample ed mlSample ml identityIndex identifier prepared
  have empties:=AdapterServerConstructorObjects.empty views objects identifier (ed.realize prepared.seed) (ml.realize prepared.credential)
  refine ⟨?_,rfl,rfl,rfl⟩
  refine ⟨identity,rfl,rfl,rfl,rfl,empties.1,?_⟩
  refine ⟨PqxdhRecordLiftWorld.importedServer (PqxdhLiveServerConstruction.initialized setup.joint identityIndex identifier .generated prepared.seed),rfl,rfl,rfl,?_⟩
  exact empties.2
end BeaconcryptCore.Refinement.AdapterServerConstructorMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorMaterial.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorMaterial.finish
