-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource
import BeaconcryptCore.Refinement.AdapterServerConstructorRetained
import BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame
import BeaconcryptCore.Refinement.AdapterServerConstructorMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source initializer executes the actual checked caller-RNG constructor and actual Server authentication_pin continuation. The receipt retains even constructor errors and the same returned source Self/RNG. Native initialization is its proved projection, with no caller startup/profile equation. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorReady
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [storage : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [localOps : LocalOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [children : ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
local notation "World"   =>   PqxdhRecordLiftWorld.State n
local notation "M"   =>   StateT World ProbComp

open AdapterServerConstructorRunner
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
variable (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
variable (ensureInit : StateT Unit ProbComp Bool)
local notation "edSample"   =>   PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)
local notation "mlSample"   =>   PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)
variable (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint
  (PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)))
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view
  (PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)))
include views objects ed ml

variable (edGetter : ∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
variable (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
variable (hashLeaf : ∀request,(children.executeHash request).run=RegistrationNativeServerPinRecompute.nativeHash request)
include edGetter mlGetter hashLeaf

theorem material (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : Receipt n KemSK R mlSource)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (supported : receipt∈support (game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    Server view views ready.initial.created ready.initial.credential ready.stored ready.initial.state.server ∧
    ready.initial.state.beacons=[] ∧ ready.initial.state.server.sessions=[] ∧
    ready.initial.state.server.world.world.1.owners=[] := by
  obtain ⟨prepared,nextRng,before,after,keySupport,finishSupport⟩:=
    AdapterServerConstructorRunnerSource.selected setup generator view views objects ensureInit ed ml identityIndex identifier rng receipt ready supported returned
  have keyLaw : Prod.fst <$>AdapterServerConstructorJoint.joint generator view setup.joint edSample ed mlSample ml rng=
      AdapterServerConstructorStartup.keys (n:=n) mlSource ensureInit := by
    rw [AdapterServerConstructorJoint.native generator view setup.joint edSample ed mlSample ml]
    rfl
  have keyNative : (some prepared,before)∈support
      ((AdapterServerConstructorStartup.keys (n:=n) mlSource ensureInit).run PqxdhRecordLiftWorld.initial) := by
    rw [←keyLaw,StateT.run_map,support_map]
    exact ⟨((some prepared,nextRng),before),keySupport,rfl⟩
  have fields:=AdapterServerConstructorKeyFrame.keys mlSource ensureInit _ _ keyNative
  have modelFinish : (some ready.initial,after)∈support
      ((AdapterServerConstructorStartup.finish setup mlSource identityIndex identifier prepared).run before) := by
    rw [←AdapterServerConstructorInitialized.native setup generator view views objects edSample ed mlSample ml identityIndex identifier prepared nextRng before edGetter mlGetter hashLeaf,support_map]
    exact ⟨(some ready,after),finishSupport,rfl⟩
  have kept:=AdapterServerConstructorRetained.returned setup view identityIndex identifier _ nextRng before after ready finishSupport
  have related:=AdapterServerConstructorMaterial.finish setup generator view views objects edSample ed mlSample ml
    identityIndex identifier prepared before after ready.initial fields.1 modelFinish
  refine ⟨?_,related.2.1,related.2.2.1,related.2.2.2.trans fields.2⟩
  simpa only [←kept.1] using related.1
end BeaconcryptCore.Refinement.AdapterServerConstructorReady

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorReady.material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorReady.material
