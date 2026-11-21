-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore
import BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary
import BeaconcryptCore.Computational.RegistrationResponseNormal
/-! The whole active extracted Beacon finish function now equals a closed stateful execution using the concrete all-input source response decoder, actual native authentication, NoEntropy agreementCore and actual unlogged first-record interpreter. The complete returned source Self and all underlying mutable owner/Env/trusted primitive effects are retained. The source agreement is instantiated from individual primitive functional/representation contracts and actual private stored keys; the record callback dictionary is concrete, leaving only its individual initial-HKDF normality law. No codec law, aggregate handler/controller law, successful authentication, agreement or opening premise is assumed. Native request-journal and lifecycle bookkeeping remain the next composition step. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishTree
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner)
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable {n : Nat} {I KemSK Auxiliary E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [localOps : LocalOperations (RustT (M n KemSK source Auxiliary))]
variable [crypto : CryptoOperations (RustT (M n KemSK source Auxiliary))]

noncomputable def recordSuffix (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) : M n KemSK source Auxiliary (RustM AdapterPublicFinishBody.Result) :=
  match effect with
  | .Rejected (.Some control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .BeaconComplete agreed => (fun result => AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result)) <$>
      simulateQ (RegistrationNativeRecordJournal.unlogged setup wire) (RegistrationBeaconRecordExecutor.begin agreed)
  | _ => pure (.ok (.None, self))

noncomputable def accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) : M n KemSK source Auxiliary (RustM AdapterPublicFinishBody.Result) := do
  let result ← simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok phase => recordSuffix setup wire self phase

variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (erased : commitment.CommitmentTranscript)
variable (authentication : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (M n KemSK source Auxiliary))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
variable (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
  pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))

include initial in
omit crypto [PublicWrapperPlatform.CryptoOperations] in
theorem record_source (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children authentication
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    (AdapterPublicFinishBody.fromAgreement (m := M n KemSK source Auxiliary) self effect).run = recordSuffix setup wire self effect := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children authentication
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  cases effect with
  | Rejected optional => cases optional <;> rfl
  | BeaconComplete agreed => exact AdapterPublicFinishRecordDictionary.first_open setup wire erased authentication writer initial self agreed
  | _ => rfl

include initial in
theorem accepted_source (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar keys)
    (authenticated : registration.AuthenticatedResponse) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children authentication
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    (AdapterPublicFinishAuthentication.accepted (m := M n KemSK source Auxiliary) self prekey oneTime kem authenticated).run =
      accepted setup wire self owner scalar authenticated := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children authentication
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  rw [AdapterPublicFinishNativeCore.accepted_agreement model self prekey oneTime kem owner scalar keys decap authenticated]
  unfold accepted
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => rfl
  | ok phase => exact record_source setup wire erased authentication writer initial self phase

noncomputable def afterAuthentication (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    M n KemSK source Auxiliary (RustM AdapterPublicFinishBody.Result) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .ok (.Ok authenticated) => accepted setup wire self owner scalar authenticated

include initial in
omit authentication in
theorem source_active (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (parseEd : Slice U8 → M n KemSK source Auxiliary (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source Auxiliary (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : Codecs (RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := RustT (M n KemSK source Auxiliary)) self input).run = (do
      let reply ← simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
        (RegistrationResponseExecutor.begin pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
      afterAuthentication setup wire {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} owner scalar reply) := by
  let auth := AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source) parseEd verifyEd
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children auth
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : Codecs (RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicFinishAuthentication.source (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer self input]
  simp only [stored, RegistrationResponseNormal.aborted_exact]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div => rfl
  | ok outcome => cases outcome with
    | Err control => rfl
    | Ok authenticated =>
        exact accepted_source setup wire erased auth writer initial view model _ prekey oneTime kem owner scalar keys decap authenticated

end BeaconcryptCore.Refinement.AdapterPublicFinishTree

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTree.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTree.record_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTree.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTree.accepted_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTree.source_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTree.source_active
