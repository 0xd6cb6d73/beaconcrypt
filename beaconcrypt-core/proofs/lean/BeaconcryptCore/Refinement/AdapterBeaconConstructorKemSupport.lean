-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Every reached source KEM receipt is built from that same actual private draw and has the corresponding reached private pool row. Shared external coin state is retained; no public-reply secret recovery or key-validity admission assumption is used. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK R P : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]

theorem joint_supported (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : AdapterBeaconConstructorKem.Representation view R) (rng : R)
    (before : AdapterBeaconConstructorKem.Native n KemSK source) (platform : P)
    (receipt : AdapterBeaconConstructorKem.Receipt R) (after : AdapterBeaconConstructorKem.Native n KemSK source) (platformAfter : P)
    (supported : ((receipt, after), platformAfter) ∈ support (((AdapterBeaconConstructorKem.joint coins setup view model rng).run before).run platform)) :
    ∃ pair world,
      receipt = AdapterBeaconConstructorKem.receipt view model before pair rng ∧
      after = AdapterBeaconConstructorKem.after before pair world := by
  change ((receipt, after), platformAfter) ∈ support ((simulateQ coins
    ((fun result => (AdapterBeaconConstructorKem.receipt view model before result.1 rng,
      AdapterBeaconConstructorKem.after before result.1 result.2)) <$>
        (PqxdhRecordLiftWorld.sampled (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)).run before.server.world.world.1)).run platform) at supported
  rw [simulateQ_map] at supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨⟨selected, reachedP⟩, _, same⟩ := supported
  cases same
  exact ⟨selected.1, selected.2, rfl, rfl⟩

theorem key_material_supported (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : AdapterBeaconConstructorKem.Representation view R) (rng : R)
    (before : AdapterBeaconConstructorKem.Native n KemSK source) (platform : P)
    (receipt : AdapterBeaconConstructorKem.Receipt R) (after : AdapterBeaconConstructorKem.Native n KemSK source) (platformAfter : P)
    (supported : ((receipt, after), platformAfter) ∈ support (((AdapterBeaconConstructorKem.joint coins setup view model rng).run before).run platform)) :
    AdapterPublicWrapperState.KemPair view after.pool receipt.pair receipt.born.1 receipt.born.2 := by
  obtain ⟨pair, world, rfl, rfl⟩ := joint_supported coins setup view model rng before platform receipt after platformAfter supported
  exact AdapterBeaconConstructorKem.key_material view model before pair world rng

variable {Auxiliary : Type}
theorem lifted_supported (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : AdapterBeaconConstructorKem.Representation view R) (rng : R)
    (owners ownersAfter : RegistrationNativeBeaconFrontend.State source)
    (env envAfter : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : AdapterBeaconConstructorKem.Native n KemSK source) (platform : P)
    (receipt : AdapterBeaconConstructorKem.Receipt R) (after : AdapterBeaconConstructorKem.Native n KemSK source) (platformAfter : P)
    (supported : ((((receipt, ownersAfter), envAfter), after), platformAfter) ∈ support
      (((((AdapterBeaconConstructorKemLift.joint coins setup view model rng).run owners).run env).run before).run platform)) :
    ownersAfter = owners ∧ envAfter = env ∧
      AdapterPublicWrapperState.KemPair view after.pool receipt.pair receipt.born.1 receipt.born.2 := by
  simp only [AdapterBeaconConstructorKemLift.joint, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨⟨⟨received, middle⟩, lastP⟩, generated, same⟩ := supported
  cases same
  exact ⟨rfl, rfl, key_material_supported coins setup view model rng before platform received middle lastP generated⟩

end BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.joint_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.joint_supported

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.key_material_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.key_material_supported

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.lifted_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport.lifted_supported
