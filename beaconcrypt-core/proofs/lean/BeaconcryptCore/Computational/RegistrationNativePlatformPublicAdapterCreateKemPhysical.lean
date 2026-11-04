-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate
/-! The physical constructor KEM receipt is built from the same private pair and exact returned RNG before the public owner is registered. The pool append uses the actual source pair views. Its comparison with the retained source stack preserves the actual source environment and every uniform/cache/platform effect. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend backend worldBackend)
variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)

omit material ed in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

def receipt (model : AdapterBeaconConstructorKem.Representation view R)
    (before : Backend n KemSK) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (rng : R) : AdapterBeaconConstructorKem.Receipt R :=
  ⟨(before.pool.keys.length,pair.1),(model.realize pair.1 pair.2 rng).1,(model.realize pair.1 pair.2 rng).2⟩

def after (before : Backend n KemSK) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (world : PqxdhRecordLiftWorld.State n) : Backend n KemSK :=
  {before with pool := (PqxdhLiveKemBirth.created before.pool pair).2, world := worldBackend world}

noncomputable def joint (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (model : AdapterBeaconConstructorKem.Representation view R) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp) (AdapterBeaconConstructorKem.Receipt R) :=fun before =>
  simulateQ coins ((fun result => (receipt view model before result.1 rng,after before result.1 result.2)) <$>
    (PqxdhRecordLiftWorld.sampled (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)).run before.world)

theorem joint_source (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (model : AdapterBeaconConstructorKem.Representation view R) (rng : R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (fun result => (result.1,backend (RegistrationNativeFinishTerminalTree.assemble owners environment result.2))) <$>
      (AdapterBeaconConstructorKem.joint coins setup view model rng).run before =
    (joint view coins setup model rng).run (backend (RegistrationNativeFinishTerminalTree.assemble owners environment before)) := by
  dsimp only [AdapterBeaconConstructorKem.joint,RegistrationNativePlatformInterpret.state,
    AdapterBeaconConstructorKem.jointSource,AdapterBeaconConstructorKem.after,AdapterBeaconConstructorKem.receipt,
    joint,after,receipt,PqxdhRecordLiftWorld.sampled,StateT.run,
    backend,RegistrationNativeFinishTerminalTree.assemble,RegistrationWorldAgreementCompiler.join,worldBackend]
  simp only [simulateQ_map,Functor.map_map,bind_pure_comp,Function.update_idem]

variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
theorem operation (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (model : AdapterBeaconConstructorKem.Representation view R) (generator : rand_core.TryCryptoRng R Error)
    (contract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup model generator) (rng : R) :
    RegistrationNativePlatformPublicAdapterCreateKem.physical (n:=n) view coins generator rng = RustT.lift
      ((fun result : AdapterBeaconConstructorKem.Receipt R => (core.result.Result.Ok result.pair,result.rng)) <$>
        joint view coins setup model rng) := by
  apply RustT.ext
  rw [RustT.run_lift,Functor.map_map]
  funext before
  change RegistrationNativePlatformPublicAdapterCreateKem.backendInstall view <$> simulateQ coins
      ((RegistrationNativePlatformSdkCountedReification.countedBackend (original.kemGenerate generator rng)).run before) =
    ((fun result : AdapterBeaconConstructorKem.Receipt R => RustM.ok (core.result.Result.Ok result.pair,result.rng)) <$>
      joint view coins setup model rng).run before
  rw [StateT.run_map,contract.operation]
  dsimp only [RegistrationNativePlatformSdkCountedReification.countedBackend,joint,
    PqxdhRecordLiftWorld.sampled,StateT.run]
  simp only [RustT.run_lift,simulateQ_map,map_apply,Functor.map_map,bind_pure_comp]
  apply congrArg (fun observe => observe <$> _)
  funext result
  simp only [RegistrationNativePlatformPublicAdapterCreateKem.backendInstall,receipt,after,
    model.publicView,model.privateView]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical.joint_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical.operation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical.operation
