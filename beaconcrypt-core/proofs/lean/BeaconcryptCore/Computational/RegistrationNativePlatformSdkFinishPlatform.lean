-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformInterpret (state state_pure state_bind state_simulate)
open RegistrationNativePlatformSdkFinishSampling (uniform uniformP)
variable {n : Nat} {I KemSK P A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "BaseM" => StateT (Backend n KemSK) ProbComp
local notation "TargetM" => StateT (Backend n KemSK) (StateT P ProbComp)

 theorem map (coins : QueryImpl unifSpec (StateT P ProbComp)) (observe : A → B) (work : BaseM A) :
    state coins (observe <$>work) = observe <$>state coins work := by
  rw [←bind_pure_comp,state_bind]
  simp only [state_pure,bind_pure_comp]

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
noncomputable section
local instance baseCrypto : CryptoOperations (RustT BaseM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original
@[instance_reducible] def targetCrypto (coins : QueryImpl unifSpec (StateT P ProbComp)) : CryptoOperations (RustT TargetM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniformP coins) original

 theorem agreement_query (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (keys : AdapterPublicAgreementFields.Keys) (query : RegistrationAgreementExecutor.Request) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins (AdapterPublicAgreementCapture.implementation
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) keys query) =
      AdapterPublicAgreementCapture.implementation
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) keys query := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  cases query with
  | decapsulate input=>
      cases input with
      | none=>exact state_pure coins _
      | some input=>
          cases stored:keys.beacon_kem with
          | none=>
              simp only [AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate,stored]
              exact state_pure coins _
          | some secret=>
              simp only [AdapterPublicAgreementCapture.implementation,AdapterPublicAgreementCommonModel.decapsulate,stored,
                RegistrationNativePlatformSdkFinishClosedSource.mappedModel,RegistrationNativePlatformSdkFinishPhysicalBody.model,
                RegistrationNativePlatformPublicAdapterCommonModel.model]
              rw [RegistrationNativePlatformSdkFinishSampling.program,RegistrationNativePlatformSdkFinishSampling.programP]
              rfl
  | _=>exact state_pure coins _

omit original in
 theorem suffix (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : agreement.AgreementEffect) :
    state coins (RegistrationNativePlatformSdkFinishSourceProgram.suffix setup wire trusted self effect) =
      RegistrationNativePlatformSdkFinishSourceProgram.suffix setup wire (fun query=>state coins (trusted query)) self effect := by
  cases effect with
  | Rejected optional=>cases optional <;> exact state_pure coins _
  | BeaconComplete agreed=>
      simp only [RegistrationNativePlatformSdkFinishSourceProgram.suffix,map,state_simulate]
      apply congrArg (fun impl : QueryImpl RegistrationRecordPrimitives.Spec TargetM =>
        (fun answer=>AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
          simulateQ impl (RegistrationBeaconRecordExecutor.begin agreed))
      funext query
      exact state_simulate coins trusted (RegistrationNativeRecordJournal.core setup wire query)
  | _=>exact state_pure coins _

 theorem accepted (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins (RegistrationNativePlatformSdkFinishSourceProgram.accepted setup wire trusted view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self prekey oneTime kem authenticated) =
      RegistrationNativePlatformSdkFinishSourceProgram.accepted setup wire (fun query=>state coins (trusted query)) view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self prekey oneTime kem authenticated := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  have leaves : (fun query=>state coins (AdapterPublicAgreementCapture.implementation
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract)
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) query)) =
      AdapterPublicAgreementCapture.implementation
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract)
        (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) := by
    funext query
    exact agreement_query coins setup view contract _ query
  simp only [RegistrationNativePlatformSdkFinishSourceProgram.accepted,state_bind,state_simulate]
  rw [leaves]
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div=>exact state_pure coins _
  | ok effect=>exact suffix coins setup wire trusted self effect

 theorem after (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins (RegistrationNativePlatformSdkFinishSourceProgram.after setup wire trusted view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self prekey oneTime kem reply) =
      RegistrationNativePlatformSdkFinishSourceProgram.after setup wire (fun query=>state coins (trusted query)) view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self prekey oneTime kem reply := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  cases reply with
  | fail error | div=>exact state_pure coins _
  | ok outcome=>cases outcome with
    | Err control=>exact state_pure coins _
    | Ok authenticated=>exact accepted coins setup wire trusted view contract self prekey oneTime kem authenticated

 theorem program (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (trusted : QueryImpl (Trusted n KemSK) BaseM)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    letI : CryptoOperations (RustT TargetM) := targetCrypto coins
    state coins (RegistrationNativePlatformSdkFinishSourceProgram.program setup wire trusted view
      (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view contract) self input) =
      RegistrationNativePlatformSdkFinishSourceProgram.program setup wire (fun query=>state coins (trusted query)) view
        (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self input := by
  let : CryptoOperations (RustT TargetM) := targetCrypto coins
  have leaves : (fun query=>state coins (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=source) setup trusted query)) =
      RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=source) setup (fun query=>state coins (trusted query)) := by
    funext query
    exact state_simulate coins trusted (AdapterPublicFinishFreeTree.authentication (source:=source) setup query)
  cases stored:self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>
      simp only [RegistrationNativePlatformSdkFinishSourceProgram.program,stored]
      exact state_pure coins _
  | InitSent pending prekey oneTime kem=>
      simp only [RegistrationNativePlatformSdkFinishSourceProgram.program,stored]
      cases aborted:pending.aborted_state with
      | fail error | div=>exact state_pure coins _
      | ok control=>
          simp only [state_bind,state_simulate]
          rw [leaves]
          apply bind_congr
          intro reply
          exact after coins setup wire trusted view contract {self with state:=.Aborted control} prekey oneTime kem reply

end
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.agreement_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.agreement_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform.program
