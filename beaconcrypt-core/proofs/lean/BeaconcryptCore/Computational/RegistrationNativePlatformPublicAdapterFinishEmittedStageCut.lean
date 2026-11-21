-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open AdapterPublicFinishLifetime (packet)
open RegistrationNativePlatformPublicAdapterFinishSampleStageCut (implementation)
variable {n :Nat} {I KemSK Auxiliary Log A B P :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK Auxiliary
local notation "Logged"=>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.M n KemSK Auxiliary Log
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
open RegistrationNativePlatformPublicAdapterFinishLoggedFactor (lift firstRecord afterAgreement accepted afterAuthentication body sample)

def Shift (work:Logged A) :Prop:=∀env past log,
  work.run (env,past++log)=(fun result=>(result.1,(result.2.1,past++result.2.2))) <$>work.run (env,log)

private theorem pure_shift (value:A) :Shift (pure value:Logged A):=by
  intro env past log
  simp only [StateT.run_pure,map_pure]

private theorem lift_shift (work:Lower A) :Shift (lift (Log:=Log) work):=by
  intro env past log
  simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift,StateT.run,Functor.map_map]

private theorem bind_shift (work:Logged A) (next:A→Logged B) (first:Shift work) (later:∀value,Shift (next value)) :
    Shift (work >>=next):=by
  intro env past log
  rw [StateT.run_bind,first env past log,bind_map_left,StateT.run_bind,map_bind]
  apply bind_congr
  intro result
  exact later result.1 result.2.1 past result.2.2

private theorem map_shift (observe:A→B) (work:Logged A) (same:Shift work) :Shift (observe <$>work):=by
  intro env past log
  simp only [StateT.run_map,same env past log,Functor.map_map]

variable (setup:PqxdhServerAuthExperiment.Setup base KemSK) (wire:RegistrationNativeWire.Wire) (note:Stage→Log)

private theorem first_shift (initial:registration.BeaconInitialKdf) :Shift (firstRecord (n:=n) (Auxiliary:=Auxiliary) setup wire note initial):=by
  intro env past log
  simp only [firstRecord,StateT.run,bind_pure_comp,Functor.map_map,List.append_assoc]

private theorem after_shift (reply:RustM agreement.AgreementEffect) :Shift (afterAgreement (n:=n) (Auxiliary:=Auxiliary) setup wire note reply):=by
  cases reply with
  | fail error | div=>exact pure_shift _
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      unfold afterAgreement
      cases started:registration.begin_beacon_completion agreed with
      | fail error | div=>simp only [started];exact pure_shift _
      | ok initial=>simp only [started];exact map_shift _ _ (first_shift setup wire note initial)
    | _=>exact pure_shift _

private theorem accepted_shift (owner:Owner mlSource) (scalar:PqxdhJointGapDh.ScalarBytes) (authenticated:registration.AuthenticatedResponse) :
    Shift (accepted (n:=n) (Auxiliary:=Auxiliary) setup wire note owner scalar authenticated):=
  bind_shift _ _ (lift_shift _) (after_shift setup wire note)

private theorem authentication_shift (owner:Owner mlSource) (scalar:PqxdhJointGapDh.ScalarBytes)
    (reply:RustM RegistrationResponseExecutor.ResponseResult) :
    Shift (afterAuthentication (n:=n) (Auxiliary:=Auxiliary) setup wire note owner scalar reply):=by
  cases reply with
  | fail error | div=>exact pure_shift _
  | ok result=>cases result with
    | Err control=>exact pure_shift _
    | Ok authenticated=>exact accepted_shift setup wire note owner scalar authenticated

theorem body_shift (pending:registration.BeaconPending) (decoded:core.option.Option registration.ResponsePacket)
    (owner:Owner mlSource) (scalar:PqxdhJointGapDh.ScalarBytes) :
    Shift (body (n:=n) (Auxiliary:=Auxiliary) setup wire note pending decoded owner scalar):=
  bind_shift _ _ (lift_shift _) (authentication_shift setup wire note owner scalar)

theorem sample_shift (coins:QueryImpl unifSpec (StateT P ProbComp)) (checks:PqxdhServerAuthExperiment.Checks)
    (representation:RegistrationServerRoleBackend.ConvertedIdentity setup) (created:PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pending:registration.BeaconPending) (input:Slice U8) (owner:Owner mlSource) (scalar:PqxdhJointGapDh.ScalarBytes)
    (before:Native) (previous:P) (past:List Log) :
    sample setup wire note coins checks representation created pending (packet input) owner scalar before previous past=
      (fun result=>(result.1,past++result.2)) <$>
        sample setup wire note coins checks representation created pending (packet input) owner scalar before previous [] :=by
  have shifted:=body_shift (n:=n) setup wire note pending
    (RegistrationNativePlatformExtractedSdkFinish.decodedPacket (packet input)) owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) past []
  simp only [List.append_nil] at shifted
  unfold sample
  rw [shifted]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]

theorem emitted_sample_cut (coins :QueryImpl unifSpec (StateT P ProbComp)) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (injective :Function.Injective note)
    (initial :registration.BeaconInitialKdf) (completed :registration.CompletedBeacon)
    (pending :registration.BeaconPending) (input :Slice U8) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (previous :P) (past suffix :List Log)
    (reached :(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×List Log)
    (supported :reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (packet input) owner scalar before previous past))
    (observed :reached.2=past++suffix)
    (present :note (.beaconFirstRecord initial (.ok (.Ok completed)))∈suffix) :
      ∃authenticated authenticatedEnv authenticatedState middleEnv middle,
      ((.ok (.Ok authenticated),authenticatedEnv),authenticatedState)∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=mlSource) setup)
            (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))))
          (RegistrationWorldAgreementCompiler.erase before.server.world) (before,previous)) ∧
      ((.ok (.BeaconComplete initial.agreement),middleEnv),middle)∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)) authenticatedEnv authenticatedState) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      ((.ok (.Ok completed),reached.1.1.1.2),(reached.1.1.2,reached.1.2))∈support
        (RegistrationNativePlatformPublicAdapterFinishStageCut.run (implementation coins setup checks representation created)
          (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) middleEnv middle) ∧
      reached.1.1.1.1=.ok (some completed) :=by
  rw [sample_shift setup wire note coins checks representation created pending input owner scalar before previous past,support_map] at supported
  obtain ⟨origin,called,same⟩:=supported
  have logs:past++origin.2=past++suffix:=(congrArg (fun value=>(value.2:List Log)) same).trans observed
  have originSuffix:origin.2=suffix:=List.append_cancel_left logs
  have originPresent:note (.beaconFirstRecord initial (.ok (.Ok completed)))∈origin.2:=originSuffix.symm ▸present
  have cut:=RegistrationNativePlatformPublicAdapterFinishSampleStageCut.sample_cut coins setup checks representation created wire note injective
    initial completed pending input owner scalar before previous [] origin called originPresent
  rcases cut with impossible|actual
  · exact (List.not_mem_nil impossible).elim
  · subst reached
    exact actual

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.body_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.body_shift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.sample_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.sample_shift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.emitted_sample_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.emitted_sample_cut
