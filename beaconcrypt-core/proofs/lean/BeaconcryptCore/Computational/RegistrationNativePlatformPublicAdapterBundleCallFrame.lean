-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleCallFrame
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterPhysicalFrame
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (previousLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error) (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (previousChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
local notation "M"=>StateT (Backend n KemSK) (StateT P ProbComp)
local notation "previousCrypto"=>RegistrationNativePlatformPublicAdapterUniformObserver.operations
  (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original
local notation "localOps"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.locals coins setup checks representation created view previousLocal
local notation "cryptoOps"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.crypto setup view previousCrypto failure
local notation "childOps"=>RegistrationNativePlatformPublicAdapterBundleDictionaries.children coins setup checks representation created writer previousChildren

private theorem with_keys {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R) :
    let : LocalOperations (RustT M):=localOps
    let : CryptoOperations (RustT M):=cryptoOps
    let : ChildOperations (RustT M):=childOps
    Compatible (AdapterPublicBundleBody.withKeys (m:=M) self control prekey oneTime kem rng).run :=by
  let : LocalOperations (RustT M):=localOps
  let : CryptoOperations (RustT M):=cryptoOps
  let : ChildOperations (RustT M):=childOps
  let leaves : AdapterPublicBundleMaterial.PublicationLeaves (m:=M) (self:=self):=RegistrationNativePlatformPublicAdapterBundleDictionaries.leaves coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren self
  dsimp only
  rw [AdapterPublicBundlePublication.withKeys self control prekey oneTime kem rng
    (view.kxPublic prekey.public_key) (view.kxPublic oneTime.public_key) (view.edPublic self.identity_key.public_key)
    (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key))
    (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) leaves) (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) leaves)  rfl rfl rfl rfl (AdapterPublicBundleMaterial.PublicationLeaves.edLaw (self:=self) leaves) (AdapterPublicBundleMaterial.PublicationLeaves.hashLaw (self:=self) leaves) ]
  change Compatible (AdapterPublicBundlePublication.install self prekey oneTime kem rng <$>
    RegistrationNativePlatformBeaconPublication.begin (AdapterPublicInitPublication.outgoing (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) leaves)
      (AdapterPublicInitPublication.edMethod (view.edPublic self.identity_key.public_key) (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) leaves)))
      (fun signed=>(ChildOperations.encodeInit (m:=RustT M) (AdapterPublicBundleBody.packet signed)).run)
      control _ _ self.authentication.server_pin)
  apply map_frame
  let outgoing:=AdapterPublicInitPublication.outgoing (AdapterPublicBundleMaterial.PublicationLeaves.hash (self:=self) leaves)
    (AdapterPublicInitPublication.edMethod (view.edPublic self.identity_key.public_key) (AdapterPublicBundleMaterial.PublicationLeaves.edSign (self:=self) leaves))
  let handler : QueryImpl (RegistrationNativePlatformWriter.Spec E) M:=fun query=>match query with
    | .inl query=>outgoing query
    | .inr query=>StateT.lift (writer query)
  have tree:=program_frame handler (fun query=>by
    cases query with
    | inr query=>exact lift_frame _
    | inl query=>cases query with
      | inl query=>cases query with
        | hash request=>exact RegistrationNativePlatformPublicAdapterBundleFrame.hash coins setup checks representation created (RegistrationInputs.hashBytes request)
        | sign request payload digest=>exact pure_frame _
      | inr request=>
        dsimp only [handler,outgoing,AdapterPublicInitPublication.outgoing,AdapterPublicInitPublication.edMethod]
        split <;> exact pure_frame _)
    (RegistrationNativePlatformWriter.begin E control
      ⟨view.edPublic self.identity_key.public_key,view.kxPublic prekey.public_key,RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key)⟩
      ⟨view.kxPublic oneTime.public_key⟩ self.authentication.server_pin)
  rw [RegistrationNativePlatformWriter.begin_interpret] at tree
  have encoded : (fun signed : registration.InitView=>(ChildOperations.encodeInit (m:=RustT M) (AdapterPublicBundleBody.packet signed)).run)=
      (fun signed=>simulateQ (fun query=>StateT.lift (writer query))
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket signed)).run) :=by
    funext signed
    exact (simulateQ_liftTarget (n:=M) writer _).symm
  rw [encoded]
  exact tree

 theorem call {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) :
    Compatible (RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view previousLocal previousCrypto failure writer previousChildren generator self rng) :=by
  let : LocalOperations (RustT M):=localOps
  let : CryptoOperations (RustT M):=cryptoOps
  let : ChildOperations (RustT M):=childOps
  unfold RegistrationNativePlatformPublicAdapterBundleSource.call
  dsimp only
  rw [AdapterPublicBundleBody.source]
  unfold AdapterPublicBundleBody.program
  cases stored:self.state with
  | Fresh control prekey kem=>
    unfold AdapterPublicBundleBody.generated
    simp only [RustT.run_bind]
    apply bind_frame
    · change Compatible (RegistrationNativePlatformPublicAdapterUniformObserver.observe
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created)
        (original.kxGenerate generator rng)).run
      exact program_frame _ (RegistrationNativePlatformPublicAdapterBundleFrame.coin coins setup checks representation created) _
    · intro result
      cases result with
      | fail error | div=>exact pure_frame _
      | ok result=>
        rcases result with ⟨generated,after⟩
        cases generated with
        | Err error=>exact pure_frame _
        | Ok oneTime=>exact with_keys coins setup checks representation created view previousLocal failure writer previousChildren self control prekey oneTime kem after
  | FreshWithCoins control prekey oneTime kem=>exact with_keys coins setup checks representation created view previousLocal failure writer previousChildren self control prekey oneTime kem rng
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>exact pure_frame _
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleCallFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleCallFrame.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleCallFrame.call
