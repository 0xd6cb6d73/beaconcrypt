-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageActual
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcherCore
/-! The literal public Bundle body executes under source leaf dictionaries that record the actual hash/sign replies. Its source-body normalization retains those same observations and all returned objects/state, rather than inferring a trace from an erasure theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterSourceTrace (recorded)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {S Log E KemSK :Type} {mlSource :RegistrationNativeMldsa.Source}
variable {m :Type→Type} [Monad m] [LawfulMonad m]
variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "M"=>StateT (RegistrationNativePlatformCutJournal.State (S×List Log)) m
variable (implementation :QueryImpl (RegistrationNativePlatformWriter.Spec E) (StateT S m))
variable (observation :(query :(RegistrationNativePlatformWriter.Spec E).Domain)→(RegistrationNativePlatformWriter.Spec E).Range query→List Log)
variable (fallback :registration.MldsaSigningRequest→StateT (S×List Log) m RegistrationSigningShared.SignReply)
variable (previousLocal :LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (S×List Log)) m)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (S×List Log)) m)))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (S×List Log)) m)))
variable (edSign :Slice U8→beaconcrypt_crypto.crypto_sign.SecretKey→StateT (RegistrationNativePlatformCutJournal.State (S×List Log)) m
  (core.result.Result (alloc.vec.Vec U8) ed.Error))

noncomputable def shared :QueryImpl RegistrationSigningShared.Spec M :=
  RegistrationNativePlatformCutJournal.source (fun query=>recorded implementation observation (.inl (.inl query))) fallback

@[instance_reducible] noncomputable def locals :LocalOperations (RustT M) :=
  {previousLocal with
    auth_MldsaIdentity_public_key:=fun identity=>pure (view.mldsa identity).publicKey
    auth_MldsaIdentity_sign_requested:=fun _identity request=>⟨RustM.ok <$>
      (AdapterPublicBundleNative.vector <$>
        RegistrationNativePlatformCutJournal.sign (fun query=>recorded implementation observation (.inl (.inl query))) fallback request)⟩}

@[instance_reducible] noncomputable def crypto :CryptoOperations (RustT M) :=
  {previousCrypto with
    edPublicBytes:=fun key=>pure (view.edPublic key)
    kxPublicBytes:=fun key=>pure (view.kxPublic key)
    kemPublicBytes:=fun key=>pure (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic key))
    edSign:=fun message key=>⟨RustM.ok <$>edSign message key⟩}

@[instance_reducible] noncomputable def children :ChildOperations (RustT M) :=
  {previousChildren with
    executeHash:=fun request=>⟨(fun digest=>RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      RegistrationNativePlatformCutJournal.hash (fun query=>recorded implementation observation (.inl (.inl query))) request⟩
    encodeInit:=fun packet=>⟨simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observation (.inr query)))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E) packet).run⟩}

noncomputable def withKeys {R :Type} (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R) :
    M (RustM (core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)) :=
  let :LocalOperations (RustT M):=locals view implementation observation fallback previousLocal
  let :CryptoOperations (RustT M):=crypto view previousCrypto edSign
  let :ChildOperations (RustT M):=children implementation observation previousChildren
  (AdapterPublicBundleBody.withKeys (m:=M) self control prekey oneTime kem rng).run

noncomputable def call {R Error :Type} (generator :rand_core.TryCryptoRng R Error)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (rng :R) :
    M (RustM (core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)) :=
  let :LocalOperations (RustT M):=locals view implementation observation fallback previousLocal
  let :CryptoOperations (RustT M):=crypto view previousCrypto edSign
  let :ChildOperations (RustT M):=children implementation observation previousChildren
  (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT M) generator self rng).run

noncomputable def code {R Error :Type} (generator :rand_core.TryCryptoRng R Error)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (rng :R) :
    M (RustM (core.option.Option (alloc.vec.Vec U8)×beaconcrypt_public_wrapper.beacon.Beacon×R)) :=
  match self.state with
  | .Fresh control prekey kem=>do
    let generated←(previousCrypto.kxGenerate generator rng).run
    match generated with
    | .fail error=>pure (.fail error)
    | .div=>pure .div
    | .ok (result,after)=>match result with
      | .Err _=>pure (.ok (.None,self,after))
      | .Ok oneTime=>
        withKeys view implementation observation fallback previousLocal previousCrypto previousChildren edSign
          self control prekey oneTime kem after
  | .FreshWithCoins control prekey oneTime kem=>
    withKeys view implementation observation fallback previousLocal previousCrypto previousChildren edSign
      self control prekey oneTime kem rng
  | _=>pure (.ok (.None,self,rng))

theorem call_code {R Error :Type} (generator :rand_core.TryCryptoRng R Error)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (rng :R) :
    call view implementation observation fallback previousLocal previousCrypto previousChildren edSign generator self rng=
      code view implementation observation fallback previousLocal previousCrypto previousChildren edSign generator self rng :=by
  let :LocalOperations (RustT M):=locals view implementation observation fallback previousLocal
  let :CryptoOperations (RustT M):=crypto view previousCrypto edSign
  let :ChildOperations (RustT M):=children implementation observation previousChildren
  unfold call
  dsimp only
  cases stored:self.state with
  | Fresh control prekey kem=>
    rw [AdapterPublicBundleBody.fresh generator self rng control prekey kem stored]
    unfold code
    rw [stored]
    simp only [AdapterPublicBundleBody.generated,RustT.run_bind]
    apply bind_congr
    intro generated
    cases generated with
    | fail error | div=>rfl
    | ok pair=>rcases pair with ⟨result,after⟩;cases result <;>rfl
  | FreshWithCoins control prekey oneTime kem=>
    rw [AdapterPublicBundleBody.with_coins generator self rng control prekey oneTime kem stored]
    unfold code
    rw [stored]
    rfl
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
    have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
    rw [RegistrationNativePlatformExtractedSdkIdle.bundle_source generator self rng idle]
    unfold code
    rw [stored]

theorem source {R :Type} (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng :R)
    (edLeaf :∀request,AdapterPublicInitPublication.edMethod (view.edPublic self.identity_key.public_key)
      (fun message=>edSign message self.identity_key.secret_key) request=
      RegistrationNativePlatformCutJournal.liftNative (recorded implementation observation (.inl (.inr request))))
    (before :S×List Log) :
    Prod.map id Prod.fst <$>
      (withKeys view implementation observation fallback previousLocal previousCrypto previousChildren edSign self control prekey oneTime kem rng).run (before,none)=
      (fun result=>(AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1,result.2)) <$>
        RegistrationNativePlatformPublicAdapterBundleStageActual.publication implementation observation control
          ⟨view.edPublic self.identity_key.public_key,view.kxPublic prekey.public_key,
            RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key)⟩
          ⟨view.kxPublic oneTime.public_key⟩ self.authentication.server_pin
          (view.mldsa self.authentication.identity).publicKey before :=by
  let :LocalOperations (RustT M):=locals view implementation observation fallback previousLocal
  let :CryptoOperations (RustT M):=crypto view previousCrypto edSign
  let :ChildOperations (RustT M):=children implementation observation previousChildren
  unfold withKeys
  rw [AdapterPublicBundlePublication.withKeys self control prekey oneTime kem rng
    (view.kxPublic prekey.public_key) (view.kxPublic oneTime.public_key) (view.edPublic self.identity_key.public_key)
    (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key)) (view.mldsa self.authentication.identity).publicKey
    (fun message=>edSign message self.identity_key.secret_key)
    (RegistrationNativePlatformCutJournal.hash (fun query=>recorded implementation observation (.inl (.inl query))))
    (fun request=>AdapterPublicBundleNative.vector <$>
      RegistrationNativePlatformCutJournal.sign (fun query=>recorded implementation observation (.inl (.inl query))) fallback request)
    rfl rfl rfl rfl rfl (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)]
  have outgoing :AdapterPublicInitPublication.outgoing
      (RegistrationNativePlatformCutJournal.hash (fun query=>recorded implementation observation (.inl (.inl query))))
      (fun request=>AdapterPublicBundleNative.vector <$>
        RegistrationNativePlatformCutJournal.sign (fun query=>recorded implementation observation (.inl (.inl query))) fallback request)
      (AdapterPublicInitPublication.edMethod (view.edPublic self.identity_key.public_key)
        (fun message=>edSign message self.identity_key.secret_key))=
      RegistrationNativePlatformCutJournal.extended (shared implementation observation fallback)
        (fun request=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observation (.inl (.inr request)))) :=by
    funext query
    cases query with
    | inl query=>cases query with
      | hash request=>rfl
      | sign request payload digest=>
        simp only [AdapterPublicInitPublication.outgoing,Functor.map_map]
        have same :(fun reply=>AdapterPublicInitPublication.borrowed (AdapterPublicBundleNative.vector reply))=id:=
          funext AdapterPublicBundleNative.borrowed_vector
        rw [same,id_map]
        rfl
    | inr request=>exact edLeaf request
  rw [outgoing]
  have encoded :(fun signed :registration.SignedInitView=>(ChildOperations.encodeInit (m:=RustT M) (AdapterPublicBundleBody.packet signed)).run)=
      (fun signed=>simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observation (.inr query)))
        (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
          (RegistrationNativePlatformWriter.initPacket signed)).run) :=by
    funext signed
    rfl
  rw [encoded]
  have fallbackSame:=(RegistrationNativePlatformPublicAdapterBundleStageCut.actual (recorded implementation observation) fallback
    control ⟨view.edPublic self.identity_key.public_key,view.kxPublic prekey.public_key,
      RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key)⟩
    ⟨view.kxPublic oneTime.public_key⟩ self.authentication.server_pin (view.mldsa self.authentication.identity).publicKey).symm.trans
      (RegistrationNativePlatformPublicAdapterBundleStageCut.actual (recorded implementation observation) (fun _=>pure .None)
        control ⟨view.edPublic self.identity_key.public_key,view.kxPublic prekey.public_key,
          RegistrationNativeBeaconFrontend.pqArray (view.kemPublic kem.public_key)⟩
        ⟨view.kxPublic oneTime.public_key⟩ self.authentication.server_pin (view.mldsa self.authentication.identity).publicKey)
  unfold RegistrationNativePlatformPublicAdapterBundleStageActual.publication
  simp only [StateT.run_map,bind_pure_comp,Functor.map_map]
  dsimp only [shared,children]
  rw [fallbackSame]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody.call_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleObservedBody.call_code
