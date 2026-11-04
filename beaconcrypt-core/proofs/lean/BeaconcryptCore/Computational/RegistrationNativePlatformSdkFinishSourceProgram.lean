-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDictionaries
/-! The literal SDK finish body is normalized in the same arbitrary persistent monad using its source primitive model. Decapsulation remains the original source computation. No indexed primitive equality, selected owner or scalar is required at this executable source boundary. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkFinishDictionaries
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def run (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    m (RustM AdapterPublicFinishBody.Result) :=
  letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
    (recording setup trusted erased) writer
  letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
    (m:=RustT m) self input).run

omit material platform ed [PublicWrapperPlatform.CryptoOperations] localOps crypto in
private theorem run_map {A B : Type} (function : A → B) (work : RustT m A) :
    (function <$> work).run = (fun result => function <$> result) <$> work.run := by
  change (work >>= fun value => pure (function value)).run = _
  rw [RustT.run_bind, ← bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

omit platform localOps in
theorem agreement (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (keys : AdapterPublicAgreementFields.Keys) (authenticated : registration.AuthenticatedResponse) :
    ((do let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m:=RustT m) phase keys) :
      RustT m agreement.AgreementEffect).run =
      simulateQ (AdapterPublicAgreementCapture.implementation model keys)
        (RegistrationAgreementExecutor.beacon authenticated) := by
  have noentropy (effect : agreement.AgreementEffect) :
      beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m:=RustT m) effect keys =
        Prod.fst <$> beaconcrypt_public_request.pqxdh.execute_agreement
          beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError effect keys () := rfl
  have factored : (do
      let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
      beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m:=RustT m) phase keys) =
      Prod.fst <$> (do
        let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m:=RustT m)
          beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError phase keys ()) := by
    simp only [noentropy, map_bind]
  rw [factored, run_map,
    AdapterPublicAgreementCapture.beacon beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError
      model keys authenticated (), Functor.map_map]
  have same : (fun result : RustM agreement.AgreementEffect =>
      Prod.fst <$> (do let completed ← result; .ok (completed, ()))) = id := by
    funext result
    cases result <;> rfl
  rw [same]
  exact id_map _

noncomputable def suffix (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) :
    m (RustM AdapterPublicFinishBody.Result) :=
  match effect with
  | .Rejected (.Some control) => pure (.ok (.None, {self with state:=.Aborted control}))
  | .BeaconComplete agreed => (fun answer => AdapterPublicFinishRecord.wrap self
      (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
      simulateQ (record setup wire trusted) (RegistrationBeaconRecordExecutor.begin agreed)
  | _ => pure (.ok (.None,self))

omit [PublicWrapperPlatform.CryptoOperations] crypto in
theorem suffix_source (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
      (recording setup trusted erased) writer
    (AdapterPublicFinishBody.fromAgreement (m:=m) self effect).run = suffix setup wire trusted self effect := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
    (recording setup trusted erased) writer
  cases effect with
  | Rejected optional => cases optional <;> rfl
  | BeaconComplete agreed =>
      apply AdapterPublicFinishInterpret.source (primitives setup trusted erased) (record setup wire trusted)
        (source_leaves setup trusted erased parseEd verifyEd writer) (record_leaves setup wire trusted erased) _ self agreed
      intro request
      simpa only [primitives, map_pure] using initial request
  | _ => rfl

noncomputable def accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) : m (RustM AdapterPublicFinishBody.Result) := do
  let agreed ← simulateQ (AdapterPublicAgreementCapture.implementation model
    (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem))
    (RegistrationAgreementExecutor.beacon authenticated)
  match agreed with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok effect => suffix setup wire trusted self effect

 theorem accepted_source (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
      (recording setup trusted erased) writer
    (AdapterPublicFinishAuthentication.accepted (m:=m) self prekey oneTime kem authenticated).run =
      accepted setup wire trusted view model self prekey oneTime kem authenticated := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (authentication (source:=source) setup trusted) parseEd verifyEd)
    (recording setup trusted erased) writer
  have grouped : AdapterPublicFinishAuthentication.accepted (m:=m) self prekey oneTime kem authenticated = (do
      let finished ← (do
        let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
        beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase
          (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem))
      AdapterPublicFinishBody.fromAgreement self finished) := by
    simp only [AdapterPublicFinishAuthentication.accepted, bind_assoc]
    rfl
  rw [grouped, RustT.run_bind, agreement setup view model]
  unfold accepted
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => rfl
  | ok effect => exact suffix_source setup wire trusted erased parseEd verifyEd writer initial self effect

noncomputable def after (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) : m (RustM AdapterPublicFinishBody.Result) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err control) => pure (.ok (.None,{self with state:=.Aborted control}))
  | .ok (.Ok authenticated) => accepted setup wire trusted view model self prekey oneTime kem authenticated

noncomputable def program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) : m (RustM AdapterPublicFinishBody.Result) :=
  match self.state with
  | .InitSent pending prekey oneTime kem =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok control => do
          let reply ← simulateQ (authentication (source:=source) setup trusted) (RegistrationResponseExecutor.begin pending
            (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
          after setup wire trusted view model {self with state:=.Aborted control} prekey oneTime kem reply
  | _ => pure (.ok (.None,self))

theorem source_program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) m) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m:=m) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    run (source:=source) setup trusted erased parseEd verifyEd writer self input =
      program setup wire trusted view model self input := by
  unfold run
  rw [AdapterPublicFinishAuthentication.source (authentication (source:=source) setup trusted) parseEd verifyEd
    (recording setup trusted erased) writer self input]
  unfold program
  cases state:self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control => rfl
  | InitSent pending prekey oneTime kem =>
      cases aborted:pending.aborted_state with
      | fail error | div => simp only [aborted]
      | ok control =>
          simp only [aborted]
          apply bind_congr
          intro reply
          cases reply with
          | fail error | div => rfl
          | ok outcome => cases outcome with
            | Err control => rfl
            | Ok authenticated =>
                exact accepted_source setup wire trusted erased parseEd verifyEd writer initial view model
                  _ prekey oneTime kem authenticated

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.suffix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.suffix_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.accepted_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram.source_program
