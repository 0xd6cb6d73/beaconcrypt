-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource
/-! The same original source key-generation tree is observed by the Native signing-cut and physical backend coin interpreters. Both preserve actual uniform draws and the explicit source coin-effect count. One original primitive representation/sampling contract supplies both mapped contracts with the same realized private pair and caller RNG. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)

noncomputable def nativeUniform : QueryImpl unifSpec CutM :=fun query=>
  RegistrationNativePlatformCutErasure.liftWorld
    (RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.effect (.inl query))))

noncomputable def backendUniform : QueryImpl unifSpec (StateT (Backend n KemSK) (StateT P ProbComp)) :=fun query before=>
  simulateQ coins ((RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created (.inl query)).run before)

theorem native_program (work : ProbComp A) :
    simulateQ (nativeUniform (n:=n) (source:=source) coins setup checks representation created) work=
      RegistrationNativePlatformCutErasure.liftWorld (RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.sample (n:=n) (KemSK:=KemSK) (mldsaSource:=source) (Auxiliary:=RegistrationServerRoleBackend.State) work))) := by
  unfold nativeUniform
  rw [RegistrationNativePlatformCutLift.program]
  apply congrArg RegistrationNativePlatformCutErasure.liftWorld
  calc
    _ = RegistrationNativePlatformInterpret.state coins
        (simulateQ (fun query : unifSpec.Domain=>RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.effect (n:=n) (KemSK:=KemSK) (mldsaSource:=source)
            (Auxiliary:=RegistrationServerRoleBackend.State) (.inl query))) work) :=
      (RegistrationNativePlatformInterpret.state_simulate coins _ work).symm
    _ = _ := congrArg (RegistrationNativePlatformInterpret.state coins)
      (RegistrationNativeLocalStatePatch.beacon_simulate (n:=n) (source:=source) setup checks representation created
        (fun query : unifSpec.Domain=>RegistrationNativeBeaconFrontend.effect (n:=n) (KemSK:=KemSK)
          (mldsaSource:=source) (Auxiliary:=RegistrationServerRoleBackend.State) (.inl query))
        (fun query=>RegistrationNativeLocalStatePatch.effect_work (.inl query)) work).symm

theorem native_scalar (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp)) :
    simulateQ (nativeUniform (n:=n) (source:=source) coins setup checks representation created) PqxdhJointGapDh.sampleScalar=
      RegistrationNativePlatformCutErasure.liftWorld
        (AdapterPublicBundleSourceExecution.sample (n:=n) (source:=source) coins setup checks representation created writer) := by
  rw [native_program]
  unfold AdapterPublicBundleSourceExecution.sample
  rw [RegistrationNativeBundleInterpretation.legacy]

theorem backend_program (work : ProbComp A) :
    simulateQ (backendUniform (n:=n) coins setup checks representation created) work=
      RegistrationNativePlatformPublicAdapterBundleSigning.sample (n:=n) coins setup checks representation created work := by
  unfold backendUniform
  exact (RegistrationNativePlatformInterpret.state_simulate coins
    (fun query=>RegistrationNativePlatformSdkReification.backendLeaf (n:=n) setup checks representation created (.inl query)) work).symm

theorem primitive_source (work : RustT ProbComp A)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id (fun state=>backend state.1) <$>
      ((RegistrationNativePlatformPublicAdapterUniformObserver.observe
        (nativeUniform coins setup checks representation created) work).run.run before)=
      ((RegistrationNativePlatformPublicAdapterUniformObserver.observe
        (backendUniform coins setup checks representation created) work).run.run (backend before.1)) := by
  unfold RegistrationNativePlatformPublicAdapterUniformObserver.observe
  rw [native_program,backend_program]
  simp only [RegistrationNativePlatformCutErasure.liftWorld,StateT.run,Functor.map_map]
  exact RegistrationNativePlatformPublicAdapterBundleSigning.sample_source coins setup checks representation created work.run before.1

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
noncomputable def native_contract {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar) :
    let : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (nativeUniform coins setup checks representation created) original
    AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n:=n) (source:=source) coins setup checks representation created writer)) := by
  let : CryptoOperations (RustT CutM):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (nativeUniform coins setup checks representation created) original
  let mapped:=RegistrationNativePlatformPublicAdapterUniformObserver.generation
    (nativeUniform (n:=n) (source:=source) coins setup checks representation created) generator view _ PqxdhJointGapDh.sampleScalar contract
  refine {realize:=contract.realize,privateView:=contract.privateView,publicView:=contract.publicView,operation:=?_}
  intro rng
  have law:=mapped.operation rng
  change _=RustT.lift ((fun scalar=>(core.result.Result.Ok (contract.realize scalar rng).1,(contract.realize scalar rng).2)) <$>
    simulateQ (nativeUniform coins setup checks representation created) PqxdhJointGapDh.sampleScalar) at law
  rw [native_scalar coins setup checks representation created writer] at law
  exact law

noncomputable def backend_contract {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar) :
    let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (backendUniform coins setup checks representation created) original
    AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformPublicAdapterBundleSigning.sample (n:=n) coins setup checks representation created PqxdhJointGapDh.sampleScalar) := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (backendUniform coins setup checks representation created) original
  let mapped:=RegistrationNativePlatformPublicAdapterUniformObserver.generation
    (backendUniform (n:=n) coins setup checks representation created) generator view _ PqxdhJointGapDh.sampleScalar contract
  refine {realize:=contract.realize,privateView:=contract.privateView,publicView:=contract.publicView,operation:=?_}
  intro rng
  have law:=mapped.operation rng
  change _=RustT.lift ((fun scalar=>(core.result.Result.Ok (contract.realize scalar rng).1,(contract.realize scalar rng).2)) <$>
    simulateQ (backendUniform (n:=n) coins setup checks representation created) PqxdhJointGapDh.sampleScalar) at law
  rw [backend_program] at law
  exact law

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_scalar

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.backend_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.backend_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.primitive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.primitive_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.native_contract

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.backend_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration.backend_contract
