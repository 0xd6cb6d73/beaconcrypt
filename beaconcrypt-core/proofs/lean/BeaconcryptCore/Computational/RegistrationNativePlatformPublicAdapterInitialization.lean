-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStartupGeneration
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
/-! Public initialization derives its observed primitive dictionaries from the same original constructor, cryptographic and persistent local methods. Optional generation refusal and the actual returned Server/RNG remain joint with the initialization receipt. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {n : Nat} {I KemSK R Error P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [AdapterServerConstructorPrimitive.Standard]
variable [originalGenerators : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable [originalLocal : LocalOperations (RustT (StateT P ProbComp))]
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) ProbComp

noncomputable def observeLocal (previous : P) (work : RustT (StateT P ProbComp) A) : RustT WorldM A :=
  RegistrationNativePlatformPublicAdapterUniformObserver.observe (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n))
    ⟨Prod.fst <$>work.run.run previous⟩

@[instance_reducible] noncomputable def localOperations (previous : P) : LocalOperations (RustT WorldM) where
  auth_MldsaIdentity_public_key identity:=observeLocal previous (originalLocal.auth_MldsaIdentity_public_key identity)
  auth_MldsaIdentity_sign_requested identity request:=observeLocal previous (originalLocal.auth_MldsaIdentity_sign_requested identity request)
  ratchet_initial_ratchet_hkdf request:=observeLocal previous (originalLocal.ratchet_initial_ratchet_hkdf request)
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher value:=observeLocal previous
    (originalLocal.collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher value)
  ratchet_execute_seal_request request:=observeLocal previous (originalLocal.ratchet_execute_seal_request request)
  ratchet_execute_write_request request:=observeLocal previous (originalLocal.ratchet_execute_write_request request)

@[instance_reducible] noncomputable def generators : AdapterBeaconConstructorRequestMonad.Operations (RustT WorldM) :=
  RegistrationNativePlatformPublicAdapterCreateGeneration.operations (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n))
    originalGenerators (fun generator rng=>RegistrationNativePlatformPublicAdapterUniformObserver.observe
      (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n)) (originalGenerators.kemGenerate generator rng))

@[instance_reducible] noncomputable def cryptography : CryptoOperations (RustT WorldM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n)) originalCrypto

@[instance_reducible] noncomputable def children : ChildOperations (RustT WorldM) where
  executeHash request:=⟨RegistrationNativeServerPinRecompute.nativeHash request⟩
  authenticateInit _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  authenticateResponse _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  commitmentHash _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  openRequest _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  ratchetHkdf _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  compare _ _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  encodeInit _:=AdapterRecordRequestMonad.liftRust (.fail .panic)
  encodeResponse _:=AdapterRecordRequestMonad.liftRust (.fail .panic)

variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (views : AdapterPublicWrapperStorage.Views) (objects : AdapterServerConstructorObjects.Leaves views)
variable (ensureInit : StateT Unit ProbComp Bool)
variable (serverEd : AdapterServerConstructorJoint.EdContract generator view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (ml : AdapterServerConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate source))
variable (edGetter : ∀key,originalCrypto.edPublicBytes key=pure (view.edPublic key))
variable (mlGetter : ∀identity,(originalLocal.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))

noncomputable local instance observedGenerators : AdapterBeaconConstructorRequestMonad.Operations (RustT WorldM):=generators (n:=n)
noncomputable local instance observedCrypto : CryptoOperations (RustT WorldM):=cryptography (n:=n)
noncomputable local instance observedChildren : ChildOperations (RustT WorldM):=children (n:=n)

noncomputable def signing :=
  RegistrationNativePlatformPublicAdapterStartupGeneration.signing (n:=n)
    (fun generator rng=>RegistrationNativePlatformPublicAdapterUniformObserver.observe
      (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n)) (originalGenerators.kemGenerate generator rng))
    generator view setup.joint (AdapterServerConstructorStartup.edCore ensureInit) serverEd

noncomputable def mldsa :=
  RegistrationNativePlatformPublicAdapterStartupGeneration.mldsa (n:=n)
    (fun generator rng=>RegistrationNativePlatformPublicAdapterUniformObserver.observe
      (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n)) (originalGenerators.kemGenerate generator rng))
    generator view (RegistrationNativeMldsa.generate source) ml

omit platform [PublicWrapperPlatform.Allocator] [AdapterServerConstructorPrimitive.Standard] originalGenerators in
include edGetter in
theorem ed_public (key : beaconcrypt_crypto.crypto_sign.PublicKey) :
    ((observedCrypto (n:=n)).edPublicBytes key).run=pure (.ok (view.edPublic key)) :=by
  change simulateQ (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n)) (originalCrypto.edPublicBytes key).run=_
  rw [edGetter,RustT.run_pure,simulateQ_pure]

omit [PublicWrapperPlatform.Allocator] [AdapterServerConstructorPrimitive.Standard] originalGenerators originalCrypto in
include mlGetter in
theorem ml_public (previous : P) (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) :
    letI : LocalOperations (RustT WorldM):=localOperations (n:=n) previous
    (LocalOperations.auth_MldsaIdentity_public_key (m:=RustT WorldM) identity).run=pure (.ok (view.mldsa identity).publicKey) :=by
  change simulateQ (RegistrationNativePlatformPublicAdapterStartupGeneration.uniform (n:=n))
    (Prod.fst <$>(originalLocal.auth_MldsaIdentity_public_key identity).run.run previous)=_
  rw [mlGetter]
  simp only [StateT.run_pure,map_pure,simulateQ_pure]

omit material platform ed [PublicWrapperPlatform.Allocator] [AdapterServerConstructorPrimitive.Standard]
  originalGenerators originalCrypto in
theorem hash (request : registration.HashRequest) :
    ((observedChildren (n:=n)).executeHash request).run=RegistrationNativeServerPinRecompute.nativeHash request :=rfl

noncomputable def sample (previous : P) (identityIndex : Nat) (identifier : U64) (rng : R) :=
  letI : LocalOperations (RustT WorldM):=localOperations (n:=n) previous
  RegistrationNativePlatformExtractedSdkInitialized.sample (n:=n) setup generator view identityIndex identifier rng

omit [PublicWrapperPlatform.Allocator] in
include objects serverEd ml edGetter mlGetter in
theorem native (previous : P) (identityIndex : Nat) (identifier : U64) (rng : R) :
    (fun packet=>AdapterServerConstructorRunner.nativeView packet.val) <$>
      sample (n:=n) setup generator view previous identityIndex identifier rng=
      RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex identifier :=by
  let : LocalOperations (RustT WorldM):=localOperations (n:=n) previous
  exact RegistrationNativePlatformExtractedSdkInitialized.native setup generator view views objects ensureInit
    (signing (n:=n) setup generator view ensureInit serverEd) (mldsa (n:=n) generator view ml)
    (ed_public (n:=n) view edGetter) (ml_public (n:=n) view mlGetter previous) identityIndex identifier rng

include objects serverEd ml edGetter mlGetter in
noncomputable def carrier (previous : P) (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : AdapterServerConstructorRunner.Receipt n KemSK R source)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R source)
    (supported : receipt∈support (letI : LocalOperations (RustT WorldM):=localOperations (n:=n) previous
      AdapterServerConstructorRunner.game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views ready.initial.created ready.initial.credential
      (ready.initial.state,previous) :=by
  let : LocalOperations (RustT WorldM):=localOperations (n:=n) previous
  exact RegistrationNativePlatformSdkStrongInitialized.carrier setup generator view views objects ensureInit
    (signing (n:=n) setup generator view ensureInit serverEd) (mldsa (n:=n) generator view ml)
    (ed_public (n:=n) view edGetter) (ml_public (n:=n) view mlGetter previous) identityIndex identifier rng receipt ready previous supported returned

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.ed_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.ed_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.ml_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.ml_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization.carrier
