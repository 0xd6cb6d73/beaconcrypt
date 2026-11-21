-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorRunner
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source initializer executes the actual checked caller-RNG constructor and actual Server authentication_pin continuation. The receipt retains even constructor errors and the same returned source Self/RNG. Native initialization is its proved projection, with no caller startup/profile equation. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
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
variable (ml : AdapterServerConstructorGeneration.MldsaContract generator view
  (PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)))
include views objects ed ml

omit children in
theorem source (identityIndex : Nat) (identifier : U64) (rng : R) :
    run setup view identityIndex identifier generator rng=(do
      let result←AdapterServerConstructorJoint.joint generator view setup.joint edSample ed mlSample ml rng
      let called:=RustM.ok (AdapterServerConstructorJoint.sourceResult generator view views objects setup.joint edSample ed mlSample ml identifier result)
      match result.1 with
      | none => pure ⟨called,none⟩
      | some prepared => do
        let ready←AdapterServerConstructorInitialized.finish setup view identityIndex identifier
          (AdapterServerConstructorJoint.object generator view views objects setup.joint edSample ed mlSample ml identifier prepared) result.2
        pure ⟨called,ready⟩) := by
  unfold run
  rw [AdapterServerConstructorJoint.source_program generator view views objects setup.joint edSample ed mlSample ml identifier rng]
  simp only [RustT.run_lift,bind_map_left]
  apply bind_congr
  rintro ⟨prepared,nextRng⟩
  cases prepared <;> rfl

omit children in
theorem selected (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : Receipt n KemSK R mlSource)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (supported : receipt∈support (game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    ∃prepared nextRng before after,
      ((some prepared,nextRng),before)∈support
        ((AdapterServerConstructorJoint.joint generator view setup.joint edSample ed mlSample ml rng).run PqxdhRecordLiftWorld.initial) ∧
      (some ready,after)∈support
        ((AdapterServerConstructorInitialized.finish setup view identityIndex identifier
          (AdapterServerConstructorJoint.object generator view views objects setup.joint edSample ed mlSample ml identifier prepared) nextRng).run before) := by
  rw [game,support_map] at supported
  obtain ⟨⟨actual,after⟩,called,equal⟩:=supported
  change actual=receipt at equal
  subst actual
  rw [source setup generator view views objects ensureInit ed ml identityIndex identifier rng] at called
  simp only [StateT.run_bind,mem_support_bind_iff] at called
  obtain ⟨⟨⟨prepared,nextRng⟩,before⟩,keySupport,called⟩:=called
  cases prepared with
  | none =>
    simp only [StateT.run_pure,mem_support_pure_iff] at called
    cases called
    cases returned
  | some prepared =>
    simp only [StateT.run_bind,StateT.run_pure,mem_support_bind_iff] at called
    obtain ⟨⟨found,finalWorld⟩,finishSupport,called⟩:=called
    simp only [mem_support_pure_iff,Prod.mk.injEq] at called
    obtain ⟨receiptEq,_worldEq⟩:=called
    have same : found=some ready:=(congrArg Receipt.ready receiptEq).symm.trans returned
    rw [same] at finishSupport
    exact ⟨prepared,nextRng,before,finalWorld,keySupport,finishSupport⟩
end BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource.source

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorRunnerSource.selected
