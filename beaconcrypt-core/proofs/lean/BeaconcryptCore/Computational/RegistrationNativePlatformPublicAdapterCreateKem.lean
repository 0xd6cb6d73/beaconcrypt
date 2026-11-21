-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKem
/-! Constructor KEM generation observes the original source key-generation result and RNG, then appends the private pair read from that same returned source object. Only a successful source pair causes a pool birth. The physical backend and analysis interpretation share this exact operation, including failure and divergence. The selected per-key sampling contract is stated on the original primitive method before either interpretation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
omit material ed in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Reply" => core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair ed.Error × R

def nativeInstall (result : RustM Reply × Native) : RustM Reply × Native :=
  match result.1 with
  | .ok (.Ok pair,_) => (result.1,{result.2 with pool :=
      (PqxdhLiveKemBirth.created result.2.pool (view.kemPublic pair.public_key,view.kemSecret pair.secret_key)).2})
  | _ => result

def backendInstall (result : RustM Reply × Backend n KemSK) : RustM Reply × Backend n KemSK :=
  match result.1 with
  | .ok (.Ok pair,_) => (result.1,{result.2 with pool :=
      (PqxdhLiveKemBirth.created result.2.pool (view.kemPublic pair.public_key,view.kemSecret pair.secret_key)).2})
  | _ => result

theorem install_source (result : RustM Reply × Native) :
    Prod.map id backend (nativeInstall view result) = backendInstall view (Prod.map id backend result) := by
  rcases result with ⟨result,before⟩
  cases result with
  | fail error => rfl
  | div => rfl
  | ok word =>
    rcases word with ⟨pair,rng⟩
    cases pair <;> rfl

variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]

noncomputable def native (generator : rand_core.TryCryptoRng R Error) (rng : R) :
    RustT (StateT Native (StateT P ProbComp)) Reply := ⟨fun before =>
  nativeInstall view <$> simulateQ coins
    ((RegistrationNativePlatformSdkCountedReification.native (original.kemGenerate generator rng)).run.run before)⟩

noncomputable def physical (generator : rand_core.TryCryptoRng R Error) (rng : R) :
    RustT (StateT (Backend n KemSK) (StateT P ProbComp)) Reply := ⟨fun before =>
  backendInstall view <$> simulateQ coins
    ((RegistrationNativePlatformSdkCountedReification.countedBackend (original.kemGenerate generator rng)).run before)⟩

theorem operation_source (generator : rand_core.TryCryptoRng R Error) (rng : R) (before : Native) (previous : P) :
    Prod.map (Prod.map id backend) id <$> ((native view coins generator rng).run.run before).run previous =
      ((physical view coins generator rng).run.run (backend before)).run previous := by
  have law := congrArg (fun work => Prod.map (backendInstall view) id <$> work)
    (RegistrationNativePlatformSdkCountedReification.counted_platform coins (original.kemGenerate generator rng) before previous)
  change Prod.map (Prod.map id backend) id <$>
      (nativeInstall view <$> simulateQ coins
        ((RegistrationNativePlatformSdkCountedReification.native (original.kemGenerate generator rng)).run.run before)).run previous =
    (backendInstall view <$> simulateQ coins
      ((RegistrationNativePlatformSdkCountedReification.countedBackend (original.kemGenerate generator rng)).run (backend before))).run previous
  simp only [StateT.run_map,Functor.map_map] at law ⊢
  calc
    _ = (fun result => Prod.map (backendInstall view) id (Prod.map (Prod.map id backend) id result)) <$>
        (simulateQ coins ((RegistrationNativePlatformSdkCountedReification.native (original.kemGenerate generator rng)).run.run before)).run previous := by
      apply congrArg (fun observe => observe <$> _)
      funext result
      exact congrArg (fun pair => (pair,result.2)) (install_source view result.1)
    _ = _ := law

structure Contract (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (model : AdapterBeaconConstructorKem.Representation view R) (generator : rand_core.TryCryptoRng R Error) where
  operation : ∀ rng, original.kemGenerate generator rng = RustT.lift
    ((fun pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK =>
      let realized := model.realize pair.1 pair.2 rng
      (core.result.Result.Ok realized.1,realized.2)) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)

theorem native_operation (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (model : AdapterBeaconConstructorKem.Representation view R) (generator : rand_core.TryCryptoRng R Error)
    (contract : Contract view setup model generator) (rng : R) :
    native (n:=n) view coins generator rng = RustT.lift
      ((fun receipt : AdapterBeaconConstructorKem.Receipt R => (core.result.Result.Ok receipt.pair,receipt.rng)) <$>
        AdapterBeaconConstructorKem.joint coins setup view model rng) := by
  apply RustT.ext
  rw [RustT.run_lift,Functor.map_map]
  funext before
  change nativeInstall view <$> simulateQ coins
      ((RegistrationNativePlatformSdkCountedReification.native (original.kemGenerate generator rng)).run.run before) =
    ((fun receipt : AdapterBeaconConstructorKem.Receipt R => RustM.ok (core.result.Result.Ok receipt.pair,receipt.rng)) <$>
      AdapterBeaconConstructorKem.joint coins setup view model rng).run before
  rw [StateT.run_map]
  rw [contract.operation]
  dsimp only [RegistrationNativePlatformSdkCountedReification.native,
    AdapterPublicAgreementNativeWorldMap.transform,AdapterPublicAgreementCountedRust.counted,
    RegistrationNativeExperiment.world,RegistrationNativeExperiment.server,
    AdapterBeaconConstructorKem.joint,RegistrationNativePlatformInterpret.state,
    AdapterBeaconConstructorKem.jointSource,PqxdhRecordLiftWorld.sampled,StateT.run]
  simp only [RustT.run_lift,Functor.map_map,bind_pure_comp,simulateQ_map,map_apply]
  apply congrArg (fun observe => observe <$> _)
  funext result
  simp only [nativeInstall,AdapterBeaconConstructorKem.receipt,AdapterBeaconConstructorKem.after,
    model.publicView,model.privateView]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.install_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.install_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.operation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.operation_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.native_operation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKem.native_operation
