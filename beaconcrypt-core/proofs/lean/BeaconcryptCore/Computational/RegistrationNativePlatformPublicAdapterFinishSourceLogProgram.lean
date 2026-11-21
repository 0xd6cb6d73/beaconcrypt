-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Log A B :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable {m :Type→Type} [Monad m] [LawfulMonad m]
private theorem lift_erase (work :m A) (past :List Log) :
    Prod.fst <$>(StateT.lift work:StateT (List Log) m A).run past=work :=by
  simp only [StateT.run,StateT.lift,bind_pure_comp,Functor.map_map]
  exact id_map _
private theorem pure_erase (value :A) (past :List Log) :
    Prod.fst <$>(pure value:StateT (List Log) m A).run past=(pure value:m A) :=by
  simp only [StateT.run_pure,map_pure]
private theorem bind_erase (work :StateT (List Log) m A) (sourceWork :m A)
    (next :A→StateT (List Log) m B) (sourceNext :A→m B)
    (first :∀past,Prod.fst <$>work.run past=sourceWork)
    (later :∀value past,Prod.fst <$>(next value).run past=sourceNext value) (past :List Log) :
    Prod.fst <$>(work >>=next).run past=(sourceWork >>=sourceNext) :=by
  simp only [StateT.run_bind,map_bind,later]
  have law:=congrArg (fun action=>action >>=sourceNext) (first past)
  simpa only [bind_map_left] using law
private theorem map_erase (observe :A→B) (work :StateT (List Log) m A) (sourceWork :m A)
    (same :∀past,Prod.fst <$>work.run past=sourceWork) (past :List Log) :
    Prod.fst <$>(observe <$>work).run past=observe <$>sourceWork :=by
  have law:=congrArg (fun action=>observe <$>action) (same past)
  simpa only [StateT.run_map,Functor.map_map] using law

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
variable (trusted :QueryImpl (Trusted n KemSK) m) (note :Stage→Log)

noncomputable def firstRecord (initial :registration.BeaconInitialKdf) :StateT (List Log) m (RustM RegistrationBeaconRecordExecutor.Result):=
  fun past=>(fun reply=>(reply,past++[note (.beaconFirstRecord initial reply)])) <$>
    simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire trusted) (RegistrationBeaconRecordExecutor.fromInitial initial)

theorem first_erase (initial :registration.BeaconInitialKdf) (past :List Log) :
    Prod.fst <$>(firstRecord setup wire trusted note initial).run past=
      simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire trusted) (RegistrationBeaconRecordExecutor.fromInitial initial) :=by
  simp [firstRecord,StateT.run,Functor.map_map]

noncomputable def code (agreed :agreement.BeaconAgreement) :StateT (List Log) m (RustM RegistrationBeaconRecordExecutor.Result):=
  match registration.begin_beacon_completion agreed with
  | .ok initial=>firstRecord setup wire trusted note initial
  | .fail error=>pure (.fail error)
  | .div=>pure .div

theorem code_erase (agreed :agreement.BeaconAgreement) (past :List Log) :
    Prod.fst <$>(code setup wire trusted note agreed).run past=
      simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire trusted) (RegistrationBeaconRecordExecutor.begin agreed) :=by
  unfold code RegistrationBeaconRecordExecutor.begin RegistrationBeaconRecordExecutor.continueWith
  cases registration.begin_beacon_completion agreed with
  | ok initial=>exact first_erase setup wire trusted note initial past
  | fail error | div=>simp only [StateT.run_pure,map_pure,simulateQ_pure]

variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [crypto :CryptoOperations (RustT m)]

noncomputable def suffix (self :beaconcrypt_public_wrapper.beacon.Beacon) (effect :agreement.AgreementEffect) :StateT (List Log) m (RustM AdapterPublicFinishBody.Result):=
  match effect with
  | .Rejected (.Some control)=>pure (.ok (.None,{self with state:=.Aborted control}))
  | .BeaconComplete agreed=>(fun answer=>AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
      code setup wire trusted note agreed
  | _=>pure (.ok (.None,self))

omit platform [PublicWrapperPlatform.CryptoOperations] crypto in
theorem suffix_erase (self :beaconcrypt_public_wrapper.beacon.Beacon) (effect :agreement.AgreementEffect) (past :List Log) :
    Prod.fst <$>(suffix setup wire trusted note self effect).run past=
      RegistrationNativePlatformSdkFinishSourceProgram.suffix setup wire trusted self effect :=by
  cases effect with
  | Rejected optional=>cases optional <;>exact pure_erase _ past
  | BeaconComplete agreed=>exact map_erase _ _ _ (code_erase setup wire trusted note agreed) past
  | _=>exact pure_erase _ past

variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (model :AdapterPublicAgreementCommonModel.Model (m:=m) setup view)

noncomputable def accepted (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated :registration.AuthenticatedResponse) :StateT (List Log) m (RustM AdapterPublicFinishBody.Result):=do
  let reply←StateT.lift (simulateQ (AdapterPublicAgreementCapture.implementation model
    (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem)) (RegistrationAgreementExecutor.beacon authenticated))
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok effect=>suffix setup wire trusted note self effect

omit platform [PublicWrapperPlatform.CryptoOperations] in
theorem accepted_erase (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated :registration.AuthenticatedResponse) (past :List Log) :
    Prod.fst <$>(accepted setup wire trusted note view model self prekey oneTime kem authenticated).run past=
      RegistrationNativePlatformSdkFinishSourceProgram.accepted setup wire trusted view model self prekey oneTime kem authenticated :=by
  apply bind_erase _ _ _ _ (lift_erase _) _ past
  intro reply current
  cases reply with
  | fail error | div=>exact pure_erase _ current
  | ok effect=>exact suffix_erase setup wire trusted note self effect current

noncomputable def afterAuthentication (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) :StateT (List Log) m (RustM AdapterPublicFinishBody.Result):=
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.Err control)=>pure (.ok (.None,{self with state:=.Aborted control}))
  | .ok (.Ok authenticated)=>accepted setup wire trusted note view model self prekey oneTime kem authenticated

omit platform [PublicWrapperPlatform.CryptoOperations] in
theorem after_erase (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) (past :List Log) :
    Prod.fst <$>(afterAuthentication setup wire trusted note view model self prekey oneTime kem reply).run past=
      RegistrationNativePlatformSdkFinishSourceProgram.after setup wire trusted view model self prekey oneTime kem reply :=by
  cases reply with
  | fail error | div=>exact pure_erase _ past
  | ok result=>cases result with
    | Err control=>exact pure_erase _ past
    | Ok authenticated=>exact accepted_erase setup wire trusted note view model self prekey oneTime kem authenticated past

noncomputable def program (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8) :StateT (List Log) m (RustM AdapterPublicFinishBody.Result):=
  match self.state with
  | .InitSent pending prekey oneTime kem=>
    match pending.aborted_state with
    | .fail error=>pure (.fail error)
    | .div=>pure .div
    | .ok control=>do
      let reply←StateT.lift (simulateQ (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=mlSource) setup trusted)
        (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))))
      afterAuthentication setup wire trusted note view model {self with state:=.Aborted control} prekey oneTime kem reply
  | _=>pure (.ok (.None,self))

omit platform [PublicWrapperPlatform.CryptoOperations] in
theorem program_erase (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8) (past :List Log) :
    Prod.fst <$>(program setup wire trusted note view model self input).run past=
      RegistrationNativePlatformSdkFinishSourceProgram.program setup wire trusted view model self input :=by
  unfold program RegistrationNativePlatformSdkFinishSourceProgram.program
  cases phase:self.state with
  | InitSent pending prekey oneTime kem=>
    cases aborted:pending.aborted_state with
    | fail error | div=>simp only [aborted]; exact pure_erase _ past
    | ok control=>simp only [aborted]; exact bind_erase _ _ _ _ (lift_erase _) (after_erase setup wire trusted note view model _ _ _ _) past
  | _=>exact pure_erase _ past

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.first_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.first_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.after_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.after_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program_erase
