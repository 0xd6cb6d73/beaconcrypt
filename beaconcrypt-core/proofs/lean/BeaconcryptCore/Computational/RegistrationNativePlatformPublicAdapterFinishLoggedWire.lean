-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable {m :Type→Type} [Monad m] [LawfulMonad m]

private theorem from_initial (primitive :AdapterPublicFinishRecord.Primitives m)
    (native :QueryImpl RegistrationRecordPrimitives.Spec m) (leaves :AdapterPublicFinishInterpret.Leaves primitive native)
    (initial :registration.BeaconInitialKdf) :
    simulateQ (AdapterPublicFinishRecord.handler primitive) (RegistrationBeaconRecordExecutor.fromInitial initial)=
      simulateQ native (RegistrationBeaconRecordExecutor.fromInitial initial) :=by
  unfold RegistrationBeaconRecordExecutor.fromInitial RegistrationBeaconRecordExecutor.continueWith
  cases requested:initial.request with
  | fail error | div=>rfl
  | ok request=>
    simp only [simulateQ_bind,simulateQ_spec_query,AdapterPublicFinishRecord.handler,←leaves.initial]
    apply bind_congr
    intro response
    cases resumed:initial.resume response with
    | fail error | div=>rfl
    | ok result=>cases result with
      | Err control=>rfl
      | Ok next=>exact AdapterPublicFinishInterpret.program primitive native leaves next

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (left right :RegistrationNativeWire.Wire)
variable (trusted :QueryImpl (Trusted n KemSK) m) (note :Stage→Log)

theorem first (initial :registration.BeaconInitialKdf) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord setup left trusted note initial=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord setup right trusted note initial :=by
  have one:=from_initial (RegistrationNativePlatformSdkFinishDictionaries.primitives setup trusted ⟨List.replicate 357 0#u8,by simp⟩)
    (RegistrationNativePlatformSdkFinishDictionaries.record setup left trusted)
    (RegistrationNativePlatformSdkFinishDictionaries.record_leaves setup left trusted _) initial
  have two:=from_initial (RegistrationNativePlatformSdkFinishDictionaries.primitives setup trusted ⟨List.replicate 357 0#u8,by simp⟩)
    (RegistrationNativePlatformSdkFinishDictionaries.record setup right trusted)
    (RegistrationNativePlatformSdkFinishDictionaries.record_leaves setup right trusted _) initial
  funext past
  exact congrArg (fun action=>(fun reply=>(reply,past++[note (.beaconFirstRecord initial reply)])) <$>action) (one.symm.trans two)

theorem code (agreed :agreement.BeaconAgreement) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code setup left trusted note agreed=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code setup right trusted note agreed :=by
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code
  cases registration.begin_beacon_completion agreed with
  | ok initial=>exact first setup left right trusted note initial
  | fail error | div=>rfl

variable [material :PublicWrapperPlatform.Material] [ed :AdapterInitEdPrimitive.Operations]
variable [original :CryptoOperations (RustT m)]

omit original in
theorem suffix (self :beaconcrypt_public_wrapper.beacon.Beacon) (effect :agreement.AgreementEffect) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup left trusted note self effect=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup right trusted note self effect :=by
  cases effect with
  | BeaconComplete agreed=>exact congrArg (fun action=>(fun answer=>AdapterPublicFinishRecord.wrap self
      (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>action) (code setup left right trusted note agreed)
  | Rejected optional=>cases optional <;>rfl
  | _=>rfl

variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (model :AdapterPublicAgreementCommonModel.Model (m:=m) setup view)

theorem accepted (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated :registration.AuthenticatedResponse) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup left trusted note view model self prekey oneTime kem authenticated=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup right trusted note view model self prekey oneTime kem authenticated :=by
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div=>rfl
  | ok effect=>exact suffix setup left right trusted note self effect

theorem after (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication setup left trusted note view model self prekey oneTime kem reply=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication setup right trusted note view model self prekey oneTime kem reply :=by
  cases reply with
  | fail error | div=>rfl
  | ok result=>cases result with
    | Err control=>rfl
    | Ok authenticated=>exact accepted setup left right trusted note view model self prekey oneTime kem authenticated

theorem program (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8) :
    RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup left trusted note view model self input=
      RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup right trusted note view model self input :=by
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program
  cases phase:self.state with
  | InitSent pending prekey oneTime kem=>
    cases aborted:pending.aborted_state with
    | fail error | div=>simp only [aborted]
    | ok control=>
      simp only [aborted]
      apply bind_congr
      intro reply
      exact after setup left right trusted note view model _ prekey oneTime kem reply
  | _=>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire.program
