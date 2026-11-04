-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceLogProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (uniform)
variable {n : Nat} {I KemSK Log : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (note : RegistrationNativePlatformPublicAdapterSourceTrace.Stage → Log)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
local notation "SourceM" => StateT (Backend n KemSK) ProbComp
noncomputable section
local instance sourceCrypto : CryptoOperations (RustT SourceM) :=
  RegistrationNativePlatformPublicAdapterUniformObserver.operations (uniform (n:=n) (KemSK:=KemSK)) original


omit original material ed in
 theorem first (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (initial :registration.BeaconInitialKdf) (past :List Log) (before :Backend n KemSK) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedTree.firstRecord setup wire note initial).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.firstRecord setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note initial).run past).run (erase before) :=by
  let attach:=fun answer=>(answer,past++[note (.beaconFirstRecord initial answer)])
  have law:=RegistrationNativePlatformSdkFinishWorld.program setup checks representation created
    (simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial))
    (RegistrationNativePlatformSdkFinishWorld.record_program setup wire _) before
  have mapped:=congrArg (fun action=>Prod.map attach id <$>action) law
  have collected : simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire
      (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created))
        (RegistrationBeaconRecordExecutor.fromInitial initial) =
      simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        (simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) :=by
    rw [←QueryImpl.simulateQ_compose]
    rfl
  change Prod.map id erase <$>
    (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      (attach <$>simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial))).run before =
    (attach <$>simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire
      (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created))
      (RegistrationBeaconRecordExecutor.fromInitial initial)).run (erase before)
  rw [simulateQ_map,collected,StateT.run_map,StateT.run_map]
  simpa only [Functor.map_map,attach,Prod.map_def,id_eq] using mapped

omit original material ed in
 theorem code (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (agreed :agreement.BeaconAgreement) (past :List Log) (before :Backend n KemSK) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedTree.code setup wire note agreed).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note agreed).run past).run (erase before) :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedTree.code RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.code
  cases registration.begin_beacon_completion agreed with
  | ok initial=>exact first note setup checks representation created wire initial past before
  | fail error | div=>simp only [StateT.run_pure,simulateQ_pure,map_pure];rfl

omit original in
 theorem suffix (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : agreement.AgreementEffect) (past :List Log) (before : Backend n KemSK) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.suffix setup wire note self effect).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note self effect).run past).run (erase before) := by
  cases effect with
  | Rejected optional=>cases optional <;>
      simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.suffix,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix,
        simulateQ_pure,StateT.run_pure,map_pure] <;>rfl
  | BeaconComplete agreed=>
      have law:=code note setup checks representation created wire agreed past before
      have mapped:=congrArg (fun work=>Prod.map (Prod.map
        (fun answer=>AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) id) id <$>work) law
      simpa only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.suffix,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix,
        StateT.run_map,simulateQ_map,Functor.map_map,Prod.map_def,id_eq] using mapped
  | _=>simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.suffix,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.suffix,
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
    (past :List Log) (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.accepted setup wire note self owner scalar authenticated).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note
        view (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view originalModel) self prekey oneTime kem authenticated).run past).run (erase before) := by
  have law:=RegistrationNativePlatformSdkFinishAgreementProgram.program setup checks representation created view originalModel aligned
    (AdapterPublicAgreementBeaconMaterial.registrationKeys self prekey oneTime kem) owner scalar related
    (RegistrationAgreementExecutor.beacon authenticated) (RegistrationAgreementBeaconCoverage.beacon_bound authenticated)
    before canonical pair present sameSecret
  simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.accepted,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.accepted,StateT.run_lift,
    simulateQ_bind,StateT.run_bind,map_bind,bind_assoc,pure_bind]
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
  | ok phase=>exact suffix note setup checks representation created wire self phase past after

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
    (past :List Log) (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.afterAuthentication setup wire note self owner scalar reply).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note
        view (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view originalModel) self prekey oneTime kem reply).run past).run (erase before) := by
  cases reply with
  | fail error | div=>simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.afterAuthentication,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication,
      simulateQ_pure,StateT.run_pure,map_pure];rfl
  | ok outcome=>cases outcome with
    | Err control=>simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.afterAuthentication,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.afterAuthentication,
        simulateQ_pure,StateT.run_pure,map_pure];rfl
    | Ok authenticated=>
        exact accepted note setup checks representation created wire view originalModel aligned self prekey oneTime kem
          owner scalar related authenticated past before canonical pair present sameSecret

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
    (past :List Log) (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (present : before.pool.keys[owner.kemHandle]?=some pair)
    (sameSecret : pair.2=view.kemSecret related.kem) :
    Prod.map id erase <$>
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
        ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program setup wire note self pending input owner scalar).run past)).run before =
      ((RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program setup wire
        (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) note
        view (RegistrationNativePlatformSdkFinishClosedSource.mappedModel (n:=n) setup view originalModel) self input).run past).run (erase before) := by
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
  simp only [RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program,RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program,stored,StateT.run_lift,
    RegistrationResponseNormal.aborted_exact,simulateQ_bind,StateT.run_bind,map_bind,bind_assoc,pure_bind]
  change (do
    let middle ← (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work)).run before
    Prod.map id erase <$>(simulateQ (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created)
      ((RegistrationNativePlatformPublicAdapterFinishLoggedOutput.afterAuthentication setup wire note
        {self with state:=.Aborted (RegistrationResponse.abortedState pending)} owner scalar middle.1).run past)).run middle.2) = _
  rw [collected,←law,bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨reply,reached⟩ supported
  have frame:=RegistrationNativePlatformSdkFinishWorld.program_frame setup checks representation created
    (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work) scope before canonical (reply,reached) supported
  have row : reached.pool.keys[owner.kemHandle]?=some pair := by rw [frame.1];exact present
  exact after note setup checks representation created wire view originalModel aligned
    {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem owner scalar related reply past reached frame.2 pair row sameSecret

end
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.code

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.program
