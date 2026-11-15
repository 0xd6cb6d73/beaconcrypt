-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Auxiliary A B Log P :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
abbrev M (n :Nat) (KemSK Auxiliary Log :Type):=StateT (EnvState Auxiliary×List Log) (OracleComp (Trusted n KemSK))
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK Auxiliary
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire) (note :Stage→Log)

def lift (work :Lower A) :M n KemSK Auxiliary Log A:=fun before=>
  (fun result=>(result.1,(result.2,before.2))) <$>work.run before.1

private theorem lift_erase (work :Lower A) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(lift work).run before=work.run before.1 :=by
  simp only [lift,StateT.run,Functor.map_map,Prod.map,id_eq]
  exact id_map _

private theorem pure_erase (value :A) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(pure value:M n KemSK Auxiliary Log A).run before=(pure value:Lower A).run before.1 :=by
  simp only [StateT.run_pure,map_pure]
  rfl

private theorem bind_erase (work :M n KemSK Auxiliary Log A) (baseWork :Lower A)
    (next :A→M n KemSK Auxiliary Log B) (baseNext :A→Lower B)
    (first :∀before,Prod.map id Prod.fst <$>work.run before=baseWork.run before.1)
    (later :∀value before,Prod.map id Prod.fst <$>(next value).run before=(baseNext value).run before.1)
    (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(work >>=next).run before=(baseWork >>=baseNext).run before.1 :=by
  rw [StateT.run_bind,map_bind,StateT.run_bind,←first before,bind_map_left]
  apply bind_congr
  rintro ⟨value,after⟩
  exact later value after

private theorem map_erase (observe :A→B) (work :M n KemSK Auxiliary Log A) (baseWork :Lower A)
    (same :∀before,Prod.map id Prod.fst <$>work.run before=baseWork.run before.1) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(observe <$>work).run before=(observe <$>baseWork).run before.1 :=by
  have equation:=congrArg (fun tree=>(fun result=>(observe result.1,result.2)) <$>tree) (same before)
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using equation

noncomputable def firstRecord (initial :registration.BeaconInitialKdf) :M n KemSK Auxiliary Log (RustM RegistrationBeaconRecordExecutor.Result):=
  fun before=>do
    let result←(simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)).run before.1
    pure (result.1,(result.2,before.2++[note (.beaconFirstRecord initial result.1)]))

theorem first_erase (initial :registration.BeaconInitialKdf) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(firstRecord (n:=n) setup wire note initial).run before=
      (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)).run before.1 :=by
  simp only [firstRecord,StateT.run,bind_pure_comp,Functor.map_map,Prod.map,id_eq]
  exact id_map _

noncomputable def afterAgreement (result :RustM agreement.AgreementEffect) :M n KemSK Auxiliary Log (RustM (Option registration.CompletedBeacon)):=
  match result with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.BeaconComplete agreed)=>
    match registration.begin_beacon_completion agreed with
    | .ok initial=>RegistrationNativeFinishFactor.collapse <$>firstRecord setup wire note initial
    | .fail error=>pure (.fail error)
    | .div=>pure .div
  | .ok _=>pure (.ok none)

theorem agreement_erase (result :RustM agreement.AgreementEffect) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(afterAgreement (n:=n) setup wire note result).run before=
      (RegistrationNativeFinishFactor.afterAgreement setup wire result).run before.1 :=by
  cases result with
  | fail error | div=>exact pure_erase _ before
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      unfold afterAgreement RegistrationNativeFinishFactor.afterAgreement RegistrationBeaconRecordExecutor.begin RegistrationBeaconRecordExecutor.continueWith
      cases started:registration.begin_beacon_completion agreed with
      | ok initial=>
        simp only [started]
        exact map_erase RegistrationNativeFinishFactor.collapse _ _ (first_erase setup wire note initial) before
      | fail error | div=>simp only [started,simulateQ_pure,StateT.run_pure,map_pure,RegistrationNativeFinishFactor.collapse];rfl
    | _=>exact pure_erase _ before

noncomputable def accepted (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse) :
    M n KemSK Auxiliary Log (RustM (Option registration.CompletedBeacon)) :=do
  let agreed←lift (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated))
  afterAgreement setup wire note agreed

theorem accepted_erase (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse)
    (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(accepted (n:=n) setup wire note owner scalar authenticated).run before=
      (RegistrationNativeFinishFactor.accepted setup wire owner scalar authenticated).run before.1 :=
  bind_erase _ _ _ _ (lift_erase _) (agreement_erase setup wire note) before

noncomputable def afterAuthentication (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) :M n KemSK Auxiliary Log (RustM (Option registration.CompletedBeacon)):=
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.Err _)=>pure (.ok none)
  | .ok (.Ok authenticated)=>accepted setup wire note owner scalar authenticated

theorem authentication_erase (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(afterAuthentication (n:=n) setup wire note owner scalar reply).run before=
      (RegistrationNativeFinishFactor.afterAuthentication setup wire owner scalar reply).run before.1 :=by
  cases reply with
  | fail error | div=>exact pure_erase _ before
  | ok result=>cases result with
    | Err control=>exact pure_erase _ before
    | Ok authenticated=>exact accepted_erase setup wire note owner scalar authenticated before

noncomputable def body (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) :M n KemSK Auxiliary Log (RustM (Option registration.CompletedBeacon)) :=do
  let reply←lift (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=mlSource) setup)
    (RegistrationResponseExecutor.begin pending packet))
  afterAuthentication setup wire note owner scalar reply

theorem body_erase (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.fst <$>(body (n:=n) setup wire note pending packet owner scalar).run before=
      (RegistrationNativeFinishFactor.body setup wire pending packet owner scalar).run before.1 :=
  bind_erase _ _ _ _ (lift_erase _) (authentication_erase setup wire note owner scalar) before

noncomputable def sample (coins :QueryImpl unifSpec (StateT P ProbComp)) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pending :registration.BeaconPending) (packet :Option registration.ResponsePacket) (owner :Owner mlSource)
    (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (past :List Log) :
    ProbComp ((RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log):=
  (fun result=>((((result.1.1.1,result.1.1.2.1),result.1.2),result.2),result.1.1.2.2)) <$>
    (simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
      ((body (n:=n) setup wire note pending (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar).run
        (RegistrationWorldAgreementCompiler.erase before.server.world,past))).run before)).run previous

theorem sample_erase (coins :QueryImpl unifSpec (StateT P ProbComp)) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pending :registration.BeaconPending) (packet :Option registration.ResponsePacket) (owner :Owner mlSource)
    (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (past :List Log) :
    Prod.fst <$>sample setup wire note coins checks representation created pending packet owner scalar before previous past=
      (RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar before).run previous :=by
  have erased:=body_erase (n:=n) setup wire note pending (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world,past)
  have interpreted:=congrArg (fun tree=>(simulateQ coins ((simulateQ
    (RegistrationNativeExperiment.trusted setup checks representation created mlSource) tree).run before)).run previous) erased
  simp only [simulateQ_map,StateT.run_map] at interpreted
  unfold sample RegistrationNativePlatformExtractedSdkFinish.runner RegistrationNativeFinishLifetime.tree
  simp only [Functor.map_map]
  exact interpreted

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.first_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.first_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.agreement_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.agreement_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.authentication_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.authentication_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample_erase
