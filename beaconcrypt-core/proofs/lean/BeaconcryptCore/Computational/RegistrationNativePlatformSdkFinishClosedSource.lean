-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAgreementProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (uniform)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
local notation "SourceM" => StateT (Backend n KemSK) ProbComp
noncomputable section
local instance sourceCrypto : CryptoOperations (RustT SourceM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original

noncomputable def mappedModel (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view) :
    AdapterPublicAgreementCommonModel.Model (m:=SourceM) setup view :=
  RegistrationNativePlatformPublicAdapterCommonModel.model (uniform (n:=n) (KemSK:=KemSK)) setup view originalModel

omit original in
 theorem suffix (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : agreement.AgreementEffect) (before : Backend n KemSK) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (AdapterPublicFinishFreeTree.recordSuffix setup wire self effect)).run before =
      (RegistrationNativePlatformSdkFinishSourceProgram.suffix setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) self effect).run (erase before) := by
  cases effect with
  | Rejected optional=>cases optional <;>
      simp only [AdapterPublicFinishFreeTree.recordSuffix,RegistrationNativePlatformSdkFinishSourceProgram.suffix,
        simulateQ_pure,StateT.run_pure,map_pure] <;>rfl
  | BeaconComplete agreed=>
      let observed:=fun answer=>AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)
      have law:=RegistrationNativePlatformSdkFinishWorld.program setup checks representation created
        (simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed))
        (RegistrationNativePlatformSdkFinishWorld.record_program setup wire _) before
      have mapped:=congrArg (fun work=>Prod.map observed id <$>work) law
      simp only [Functor.map_map] at mapped
      have collected : simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire
          (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created))
            (RegistrationBeaconRecordExecutor.begin agreed) =
          simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
            (simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed)) := by
        rw [←QueryImpl.simulateQ_compose]
        rfl
      simp only [AdapterPublicFinishFreeTree.recordSuffix,RegistrationNativePlatformSdkFinishSourceProgram.suffix,
        simulateQ_map,StateT.run_map,Functor.map_map]
      rw [collected]
      exact mapped

  | _=>simp only [AdapterPublicFinishFreeTree.recordSuffix,RegistrationNativePlatformSdkFinishSourceProgram.suffix,
      simulateQ_pure,StateT.run_pure,map_pure];rfl

 theorem accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar)
    (authenticated : registration.AuthenticatedResponse)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (AdapterPublicFinishFreeTree.accepted setup wire self owner scalar authenticated)).run before =
      (RegistrationNativePlatformSdkFinishSourceProgram.accepted setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        view (mappedModel (n:=n) setup view originalModel) self prekey oneTime kem authenticated).run (erase before) := by
  have law:=RegistrationNativePlatformSdkFinishAgreementProgram.program setup checks representation created view originalModel aligned
    (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar related
    (RegistrationAgreementExecutor.beacon authenticated) (RegistrationAgreementBeaconCoverage.beacon_bound authenticated)
    before canonical pair present sameSecret
  simp only [AdapterPublicFinishFreeTree.accepted,RegistrationNativePlatformSdkFinishSourceProgram.accepted,
    simulateQ_bind,StateT.run_bind,map_bind]
  have packed : (simulateQ (RegistrationNativePlatformSdkFinishAgreementProgram.closed setup checks representation created owner scalar)
      (RegistrationAgreementExecutor.beacon authenticated)).run before =
    (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      (simulateQ (RegistrationNativeAgreementJournal.core setup owner scalar)
        (RegistrationAgreementExecutor.beacon authenticated))).run before := by
    rw [←QueryImpl.simulateQ_compose]
    rfl
  rw [packed] at law
  erw [←law,bind_map_left]
  apply bind_congr
  rintro ⟨agreed,after⟩
  cases agreed with
  | fail error | div=>simp only [simulateQ_pure,StateT.run_pure,map_pure];rfl
  | ok phase=>exact suffix setup checks representation created wire self phase after

 theorem after (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar)
    (reply : RustM RegistrationResponseExecutor.ResponseResult)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (AdapterPublicFinishFreeTree.afterAuthentication setup wire self owner scalar reply)).run before =
      (RegistrationNativePlatformSdkFinishSourceProgram.after setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        view (mappedModel (n:=n) setup view originalModel) self prekey oneTime kem reply).run (erase before) := by
  cases reply with
  | fail error | div=>simp only [AdapterPublicFinishFreeTree.afterAuthentication,RegistrationNativePlatformSdkFinishSourceProgram.after,
      simulateQ_pure,StateT.run_pure,map_pure];rfl
  | ok outcome=>cases outcome with
    | Err control=>simp only [AdapterPublicFinishFreeTree.afterAuthentication,RegistrationNativePlatformSdkFinishSourceProgram.after,
        simulateQ_pure,StateT.run_pure,map_pure];rfl
    | Ok authenticated=>
        exact accepted setup checks representation created wire view originalModel aligned self prekey oneTime kem
          owner scalar related authenticated before canonical pair present sameSecret

 theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (originalModel : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup originalModel.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar)).run before =
      (RegistrationNativePlatformSdkFinishSourceProgram.program setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        view (mappedModel (n:=n) setup view originalModel) self input).run (erase before) := by
  let work:=RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))
  have scope:=RegistrationNativePlatformSdkFinishWorld.authentication_program (n:=n) (source:=source) setup work
  have law:=RegistrationNativePlatformSdkFinishWorld.program setup checks representation created
    (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work) scope before
  have collected : simulateQ (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=source) setup
      (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)) work =
      simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work) := by
    rw [←QueryImpl.simulateQ_compose]
    rfl
  simp only [AdapterPublicFinishFreeTree.program,RegistrationNativePlatformSdkFinishSourceProgram.program,stored,
    RegistrationResponseNormal.aborted_exact,simulateQ_bind,StateT.run_bind,map_bind]
  change (do
    let middle ← (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work)).run before
    Prod.map id erase <$>(simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      (AdapterPublicFinishFreeTree.afterAuthentication setup wire
        {self with state:=.Aborted (RegistrationResponse.abortedState pending)} owner scalar middle.1)).run middle.2) = _
  rw [collected,←law,bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨reply,reached⟩ supported
  have frame:=RegistrationNativePlatformSdkFinishWorld.program_frame setup checks representation created
    (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work) scope before canonical (reply,reached) supported
  have row : reached.pool.keys[owner.kemHandle]?=some pair := by rw [frame.1];exact present
  exact after setup checks representation created wire view originalModel aligned
    {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem owner scalar related reply reached frame.2 pair row sameSecret

end
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource.program
