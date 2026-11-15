-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration
/-! Native instrumentation of a selected actual SDK Bundle adds only its private signing receipts and owner history. Individual source public getters are read from the same opaque objects; key generation is the same original primitive under the explicit source coin observer. The concrete leaf laws are derived internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
variable (self : beaconcrypt_public_wrapper.beacon.Beacon)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "M"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)

@[instance_reducible] noncomputable def locals
    (_coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (_checks : PqxdhServerAuthExperiment.Checks)
    (_representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (_created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (_writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (_view : AdapterPublicWrapperState.MaterialView source KemSK)
    (_index : Nat) (_owner : RegistrationNativeBeaconFrontend.Owner source)
    (_self : beaconcrypt_public_wrapper.beacon.Beacon)
    (previous : LocalOperations (RustT M)) : LocalOperations (RustT M) := previous

@[instance_reducible] noncomputable def crypto (previous : CryptoOperations (RustT M)) (failure : ed.Error) : CryptoOperations (RustT M) := by
  classical
  exact {previous with
    edPublicBytes:=fun key=>pure (view.edPublic key)
    kxPublicBytes:=fun key=>pure (view.kxPublic key)
    kemPublicBytes:=fun key=>pure (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic key))
    edSign:=fun message key=>if key=self.identity_key.secret_key then
      ⟨RustM.ok <$>RegistrationNativePlatformCutErasure.liftWorld
        (AdapterPublicBundlePrimitives.sign coins setup checks representation created writer index owner failure message)⟩
      else previous.edSign message key}

variable (previousLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp))))
variable (previousCrypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp))))
variable (failure : ed.Error)

theorem getters :
    let : LocalOperations (RustT M):=locals coins setup checks representation created writer view index owner self previousLocal
    let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self previousCrypto failure
    AdapterPublicBundleMaterial.Getters (m:=M) view := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created writer view index owner self previousLocal
  let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self previousCrypto failure
  exact {ed:=fun _=>rfl,kx:=fun _=>rfl,kem:=fun _=>rfl}

theorem leaves :
    let : LocalOperations (RustT M):=locals coins setup checks representation created writer view index owner self previousLocal
    let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self previousCrypto failure
    AdapterPublicBundleSourceExecution.Leaves (n:=n) coins setup checks representation created writer index owner failure
      self := by
  let : LocalOperations (RustT M):=locals coins setup checks representation created writer view index owner self previousLocal
  let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self previousCrypto failure
  classical
  constructor
  · intro message
    change (if self.identity_key.secret_key=self.identity_key.secret_key then
      (⟨RustM.ok <$>RegistrationNativePlatformCutErasure.liftWorld
        (AdapterPublicBundlePrimitives.sign coins setup checks representation created writer index owner failure message)⟩ : RustT M _)
      else previousCrypto.edSign message self.identity_key.secret_key).run=_
    rw [ite_eq_left rfl]

variable [original : CryptoOperations (RustT ProbComp)]
noncomputable def generation_native {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar) :
    let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform coins setup checks representation created) original) failure
    AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n:=n) (source:=source) coins setup checks representation created writer)) := by
  let : CryptoOperations (RustT M):=crypto coins setup checks representation created writer view index owner self
    (RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform coins setup checks representation created) original) failure
  let mapped:=RegistrationNativePlatformPublicAdapterBundleGeneration.native_contract (n:=n) coins setup checks representation created generator view writer contract
  refine {realize:=contract.realize,privateView:=contract.privateView,publicView:=contract.publicView,operation:=?_}
  intro rng
  change (RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original).kxGenerate generator rng=_
  let : CryptoOperations (RustT M):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.nativeUniform (n:=n) (source:=source) coins setup checks representation created) original
  exact mapped.operation rng

noncomputable def generation_backend {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar) :
    let : CryptoOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
      RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup view
        (RegistrationNativePlatformPublicAdapterUniformObserver.operations
          (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) original) failure
    AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformPublicAdapterBundleSigning.sample (n:=n) coins setup checks representation created PqxdhJointGapDh.sampleScalar) := by
  let : CryptoOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=
    RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup view
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) original) failure
  let mapped:=RegistrationNativePlatformPublicAdapterBundleGeneration.backend_contract (n:=n) coins setup checks representation created generator view contract
  refine {realize:=contract.realize,privateView:=contract.privateView,publicView:=contract.publicView,operation:=?_}
  intro rng
  change (RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original).kxGenerate generator rng=_
  let : CryptoOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original
  exact mapped.operation rng

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.getters

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation.generation_backend
