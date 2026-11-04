-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog
import BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Auxiliary A B Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
abbrev M (n :Nat) (KemSK Log :Type):=StateT (List Log) (OracleComp (Trusted n KemSK))
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK Auxiliary
local notation "LoggedLower"=>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.M n KemSK Auxiliary Log
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire) (note :Stage→Log)

private theorem lift_projection (work :Lower A) (raw :OracleComp (Trusted n KemSK) A)
    (same :∀env,Prod.fst <$>work.run env=raw) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift work).run before=
      (StateT.lift raw:M n KemSK Log A).run before.2 :=by
  have law:=congrArg (fun tree=>(fun value=>(value,before.2)) <$>tree) (same before.1)
  simpa only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift,StateT.lift,
    StateT.run,bind_pure_comp,Functor.map_map,Prod.map,id_eq] using law

private theorem pure_projection (value :A) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(pure value:LoggedLower A).run before=(pure value:M n KemSK Log A).run before.2 :=by
  simp only [StateT.run_pure,map_pure]
  rfl

private theorem bind_projection (work :LoggedLower A) (sourceWork :M n KemSK Log A)
    (next :A→LoggedLower B) (sourceNext :A→M n KemSK Log B)
    (first :∀before,Prod.map id Prod.snd <$>work.run before=sourceWork.run before.2)
    (later :∀value before,Prod.map id Prod.snd <$>(next value).run before=(sourceNext value).run before.2)
    (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(work >>=next).run before=(sourceWork >>=sourceNext).run before.2 :=by
  rw [StateT.run_bind,map_bind,StateT.run_bind,←first before,bind_map_left]
  apply bind_congr
  rintro ⟨value,after⟩
  exact later value after

private theorem map_projection (observe :A→B) (work :LoggedLower A) (sourceWork :M n KemSK Log A)
    (same :∀before,Prod.map id Prod.snd <$>work.run before=sourceWork.run before.2) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(observe <$>work).run before=(observe <$>sourceWork).run before.2 :=by
  have law:=congrArg (fun tree=>(fun value=>(observe value.1,value.2)) <$>tree) (same before)
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using law

noncomputable def firstRecord (initial :registration.BeaconInitialKdf) :M n KemSK Log (RustM RegistrationBeaconRecordExecutor.Result):=
  fun past=>(fun reply=>(reply,past++[note (.beaconFirstRecord initial reply)])) <$>
    simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)

theorem first_projection (initial :registration.BeaconInitialKdf) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord (n:=n) setup wire note initial).run before=
      (firstRecord setup wire note initial).run before.2 :=by
  have erased:=RegistrationNativeFinishLowerErasure.simulation (RegistrationNativeBeaconPhaseCommutation.record (n:=n) setup wire)
    (RegistrationNativeRecordJournal.core setup wire) (RegistrationNativeFinishLowerErasure.record_leaf setup wire)
    (RegistrationBeaconRecordExecutor.fromInitial initial) before.1
  have law:=congrArg (fun tree=>(fun reply=>(reply,before.2++[note (.beaconFirstRecord initial reply)])) <$>tree) erased
  simpa only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord,firstRecord,StateT.run,
    bind_pure_comp,Functor.map_map,Prod.map,id_eq] using law

noncomputable def code (agreed :agreement.BeaconAgreement) :M n KemSK Log (RustM RegistrationBeaconRecordExecutor.Result):=
  match registration.begin_beacon_completion agreed with
  | .ok initial=>firstRecord setup wire note initial
  | .fail error=>pure (.fail error)
  | .div=>pure .div

theorem code_erase (agreed :agreement.BeaconAgreement) (past :List Log) :
    Prod.fst <$>(code (n:=n) setup wire note agreed).run past=
      simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed) :=by
  unfold code RegistrationBeaconRecordExecutor.begin RegistrationBeaconRecordExecutor.continueWith
  cases registration.begin_beacon_completion agreed with
  | ok initial=>
    simp only [firstRecord,StateT.run,Functor.map_map]
    exact id_map _
  | fail error | div=>simp only [StateT.run_pure,map_pure,simulateQ_pure]

noncomputable def afterAgreement (result :RustM agreement.AgreementEffect) :M n KemSK Log (RustM (Option registration.CompletedBeacon)):=
  match result with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.BeaconComplete agreed)=>RegistrationNativeFinishFactor.collapse <$>code setup wire note agreed
  | .ok _=>pure (.ok none)

theorem agreement_projection (result :RustM agreement.AgreementEffect) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement (n:=n) setup wire note result).run before=
      (afterAgreement setup wire note result).run before.2 :=by
  cases result with
  | fail error | div=>exact pure_projection _ before
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement afterAgreement code
      cases started:registration.begin_beacon_completion agreed with
      | ok initial=>simp only [started];exact map_projection _ _ _ (first_projection setup wire note initial) before
      | fail error | div=>simp only [started,StateT.run_pure,map_pure,RegistrationNativeFinishFactor.collapse];rfl
    | _=>exact pure_projection _ before

noncomputable def accepted (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse) :
    M n KemSK Log (RustM (Option registration.CompletedBeacon)) :=do
  let agreed←StateT.lift (simulateQ (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated))
  afterAgreement setup wire note agreed

theorem accepted_projection (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse)
    (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted (n:=n) setup wire note owner scalar authenticated).run before=
      (accepted setup wire note owner scalar authenticated).run before.2 :=by
  apply bind_projection
  · apply lift_projection
    intro env
    exact RegistrationNativeFinishLowerErasure.simulation _ _
      (RegistrationNativeFinishLowerErasure.agreement_leaf setup owner scalar) _ env
  · exact agreement_projection setup wire note

noncomputable def afterAuthentication (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) :M n KemSK Log (RustM (Option registration.CompletedBeacon)):=
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.Err _)=>pure (.ok none)
  | .ok (.Ok authenticated)=>accepted setup wire note owner scalar authenticated

theorem authentication_projection (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (reply :RustM RegistrationResponseExecutor.ResponseResult) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication (n:=n) setup wire note owner scalar reply).run before=
      (afterAuthentication setup wire note owner scalar reply).run before.2 :=by
  cases reply with
  | fail error | div=>exact pure_projection _ before
  | ok result=>cases result with
    | Err control=>exact pure_projection _ before
    | Ok authenticated=>exact accepted_projection setup wire note owner scalar authenticated before

noncomputable def body (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) :M n KemSK Log (RustM (Option registration.CompletedBeacon)) :=do
  let reply←StateT.lift (simulateQ (AdapterPublicFinishFreeTree.authentication (source:=mlSource) setup)
    (RegistrationResponseExecutor.begin pending packet))
  afterAuthentication setup wire note owner scalar reply

theorem body_projection (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (before :EnvState Auxiliary×List Log) :
    Prod.map id Prod.snd <$>(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body (n:=n) setup wire note pending packet owner scalar).run before=
      (body setup wire note pending packet owner scalar).run before.2 :=by
  apply bind_projection
  · apply lift_projection
    intro env
    exact RegistrationNativeFinishLowerErasure.simulation _ _
      (RegistrationNativeFinishLowerErasure.authentication_leaf (source:=mlSource) setup) _ env
  · exact authentication_projection setup wire note owner scalar

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.first_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.first_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.code_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.code_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.agreement_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.agreement_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.accepted_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.accepted_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.authentication_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.authentication_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.body_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree.body_projection
