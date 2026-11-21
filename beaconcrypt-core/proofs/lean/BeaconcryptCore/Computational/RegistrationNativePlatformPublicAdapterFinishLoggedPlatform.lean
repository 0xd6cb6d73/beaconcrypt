-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformInterpret (state state_pure state_bind state_simulate)
open RegistrationNativePlatformSdkFinishSampling (uniform uniformP)
variable {n : Nat} {I KemSK P A B Log : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "BaseM" => StateT (Backend n KemSK) ProbComp
local notation "TargetM" => StateT (Backend n KemSK) (StateT P ProbComp)

variable (note :RegistrationNativePlatformPublicAdapterSourceTrace.Stage→Log)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
noncomputable section
local instance baseCrypto : CryptoOperations (RustT BaseM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
@[instance_reducible] def targetCrypto (coins : QueryImpl unifSpec (StateT P ProbComp)) : CryptoOperations (RustT TargetM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniformP coins) original

omit original material ed in
 theorem first (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted :QueryImpl (Trusted n KemSK) BaseM) (initial :registration.BeaconInitialKdf) (past :List Log) :
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord setup wire trusted note initial).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord setup wire
        (fun query=>state coins (trusted query)) note initial).run past :=by
  have leaves : (fun query=>state coins (RegistrationNativePlatformSdkFinishDictionaries.record setup wire trusted query)) =
      RegistrationNativePlatformSdkFinishDictionaries.record setup wire (fun query=>state coins (trusted query)) :=by
    funext query
    exact state_simulate coins trusted (RegistrationNativeRecordJournal.core setup wire query)
  simp only [RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord,StateT.run,RegistrationNativePlatformSdkFinishPlatform.map,state_simulate]
  rw [leaves]

omit original material ed in
 theorem code (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted :QueryImpl (Trusted n KemSK) BaseM) (agreed :agreement.BeaconAgreement) (past :List Log) :
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code setup wire trusted note agreed).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code setup wire
        (fun query=>state coins (trusted query)) note agreed).run past :=by
  unfold RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code
  cases registration.begin_beacon_completion agreed with
  | ok initial=>exact first note coins setup wire trusted initial past
  | fail error | div=>exact state_pure coins _

omit original in
 theorem suffix (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : agreement.AgreementEffect) (past :List Log) :
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup wire trusted note self effect).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup wire
        (fun query=>state coins (trusted query)) note self effect).run past := by
  cases effect with
  | Rejected optional=>cases optional <;> exact state_pure coins _
  | BeaconComplete agreed=>
      simp only [RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix,StateT.run_map,RegistrationNativePlatformSdkFinishPlatform.map]
      rw [code note coins setup wire trusted agreed past]
  | _=>exact state_pure coins _

 theorem accepted (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) (past :List Log) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup wire trusted note view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self prekey oneTime kem authenticated).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup wire (fun query=>state coins (trusted query)) note view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self prekey oneTime kem authenticated).run past := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  have leaves : (fun query=>state coins (AdapterPublicAgreementCapture.implementation
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract)
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) query)) =
      AdapterPublicAgreementCapture.implementation
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract)
        (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) := by
    funext query
    exact RegistrationNativePlatformSdkFinishPlatform.agreement_query coins setup view contract _ query
  simp only [RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted,StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind,state_bind,state_simulate]
  rw [leaves]
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div=>exact state_pure coins _
  | ok effect=>exact suffix note coins setup wire trusted self effect past

 theorem after (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) (past :List Log) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication setup wire trusted note view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self prekey oneTime kem reply).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication setup wire (fun query=>state coins (trusted query)) note view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self prekey oneTime kem reply).run past := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  cases reply with
  | fail error | div=>exact state_pure coins _
  | ok outcome=>cases outcome with
    | Err control=>exact state_pure coins _
    | Ok authenticated=>exact accepted note coins setup wire trusted view contract self prekey oneTime kem authenticated past

 theorem program (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) (past :List Log) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup wire trusted note view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self input).run past) =
      (RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup wire (fun query=>state coins (trusted query)) note view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self input).run past := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  have leaves : (fun query=>state coins (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=source) setup trusted query)) =
      RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=source) setup (fun query=>state coins (trusted query)) := by
    funext query
    exact state_simulate coins trusted (AdapterPublicFinishFreeTree.authentication (source:=source) setup query)
  cases stored:self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>
      simp only [RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program,stored]
      exact state_pure coins _
  | InitSent pending prekey oneTime kem=>
      simp only [RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program,stored]
      cases aborted:pending.aborted_state with
      | fail error | div=>exact state_pure coins _
      | ok control=>
          simp only [StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind,state_bind,state_simulate]
          rw [leaves]
          apply bind_congr
          intro reply
          exact after note coins setup wire trusted view contract {self with state:=.Aborted control} prekey oneTime kem reply past

end
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.program
