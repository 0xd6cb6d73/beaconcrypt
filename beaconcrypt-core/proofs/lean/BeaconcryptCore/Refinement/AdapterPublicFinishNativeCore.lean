-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication
import BeaconcryptCore.Refinement.AdapterPublicFinishInterpret
import BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconMaterial
/-! The literal accepted source Beacon finish composes the actual NoEntropy agreement executor and native record interpreter in the complete native owner/Env monad. Private stored objects select the actual scalar/opaque KEM handle through their material relation. Only individual primitive normality/representation contracts are premises; no complete agreement, first-record or security conclusion is assumed. Native request-journal instrumentation and owner/environment installation remain separate representation steps. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
variable [localOps : LocalOperations (RustT (M n KemSK source Auxiliary))]
variable [crypto : CryptoOperations (RustT (M n KemSK source Auxiliary))]
variable [children : ChildOperations (RustT (M n KemSK source Auxiliary))]
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def recordSuffix (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (native : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK source Auxiliary))
    (effect : agreement.AgreementEffect) : M n KemSK source Auxiliary (RustM AdapterPublicFinishBody.Result) :=
  match effect with
  | .Rejected (.Some control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .BeaconComplete agreed =>
      (fun answer => AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
        simulateQ native (RegistrationBeaconRecordExecutor.begin agreed)
  | _ => pure (.ok (.None, self))

omit [PublicWrapperPlatform.CryptoOperations] crypto in
theorem record_suffix (primitive : AdapterPublicFinishRecord.Primitives (M n KemSK source Auxiliary))
    (native : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK source Auxiliary))
    (actual : AdapterPublicFinishRecord.Contract primitive) (leaves : AdapterPublicFinishInterpret.Leaves primitive native)
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run = RustM.ok <$> primitive.initial request)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) :
    (AdapterPublicFinishBody.fromAgreement (m := M n KemSK source Auxiliary) self effect).run =
      recordSuffix self native effect := by
  cases effect with
  | Rejected optional => cases optional <;> rfl
  | BeaconComplete agreed => exact AdapterPublicFinishInterpret.source primitive native actual leaves initial self agreed
  | _ => rfl

theorem accepted_agreement (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar related)
    (authenticated : registration.AuthenticatedResponse) :
    (AdapterPublicFinishAuthentication.accepted (m := M n KemSK source Auxiliary) self prekey oneTime kem authenticated).run = (do
      let agreed ← simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner scalar)
        (RegistrationAgreementExecutor.beacon authenticated)
      match agreed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok effect => (AdapterPublicFinishBody.fromAgreement self effect).run) := by
  have grouped : AdapterPublicFinishAuthentication.accepted (m := M n KemSK source Auxiliary) self prekey oneTime kem authenticated = (do
      let finished ← (do
        let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
        beaconcrypt_public_request.pqxdh.execute_beacon_agreement phase
          (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem))
      AdapterPublicFinishBody.fromAgreement self finished) := by
    simp only [AdapterPublicFinishAuthentication.accepted, bind_assoc]
    rfl
  rw [grouped, RustT.run_bind, AdapterPublicAgreementBeaconFrontend.source_beacon model _ owner scalar related decap authenticated]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem accepted (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (primitive : AdapterPublicFinishRecord.Primitives (M n KemSK source Auxiliary))
    (native : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK source Auxiliary))
    (actual : AdapterPublicFinishRecord.Contract primitive) (leaves : AdapterPublicFinishInterpret.Leaves primitive native)
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run = RustM.ok <$> primitive.initial request)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar related)
    (authenticated : registration.AuthenticatedResponse) :
    (AdapterPublicFinishAuthentication.accepted (m := M n KemSK source Auxiliary) self prekey oneTime kem authenticated).run = (do
      let agreed ← simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner scalar)
        (RegistrationAgreementExecutor.beacon authenticated)
      match agreed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok effect => recordSuffix self native effect) := by
  rw [accepted_agreement model self prekey oneTime kem owner scalar related decap authenticated]
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => rfl
  | ok effect => exact record_suffix primitive native actual leaves initial self effect
end BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.record_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.record_suffix

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.accepted_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.accepted_agreement

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNativeCore.accepted
