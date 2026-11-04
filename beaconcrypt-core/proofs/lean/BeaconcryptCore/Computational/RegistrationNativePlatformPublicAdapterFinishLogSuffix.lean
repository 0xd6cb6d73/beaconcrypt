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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Auxiliary Log S A :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK Auxiliary
local notation "Logged"=>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.M n KemSK Auxiliary Log
variable (implementation :QueryImpl (Trusted n KemSK) (StateT S ProbComp))

open RegistrationNativePlatformPublicAdapterFinishStageCut (run logged)

private theorem lift_run (work :Lower A) (env :EnvState Auxiliary) (past :List Log) (before :S) :
    logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift work) env past before=
      (fun result=>((result.1.1,(result.1.2,past)),result.2)) <$>run implementation work env before :=by
  unfold logged RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift
  change (simulateQ implementation ((fun result=>(result.1,(result.2,past))) <$>work.run env)).run before=_
  rw [simulateQ_map,StateT.run_map]
  rfl

private theorem pure_run (value :A) (env :EnvState Auxiliary) (past :List Log) (before :S) :
    logged implementation (pure value:Logged A) env past before=pure ((value,(env,past)),before) :=by
  simp only [logged,StateT.run_pure,simulateQ_pure]

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire) (note :Stage→Log)

def Suffix (note :Stage→Log) (before after :List Log) :Prop :=
  after=before ∨∃initial reply,after=before++[note (.beaconFirstRecord initial reply)]

theorem after (reply :RustM agreement.AgreementEffect) (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement setup wire note reply) env past before)) :
    Suffix note past result.1.2.2 :=by
  cases reply with
  | fail error | div=>
    rw [show RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement (n:=n) setup wire note _=pure _ from rfl,pure_run] at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement at supported
      cases started:registration.begin_beacon_completion agreed with
      | fail error | div=>
        simp only [started] at supported
        rw [pure_run] at supported
        simp only [support_pure,Set.mem_singleton_iff] at supported
        cases supported
        exact Or.inl rfl
      | ok initial=>
        simp only [started,logged,StateT.run_map,simulateQ_map,StateT.run_map] at supported
        change result∈support (Prod.map (Prod.map RegistrationNativeFinishFactor.collapse id) id <$>
          logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord setup wire note initial) env past before) at supported
        have first:=RegistrationNativePlatformPublicAdapterFinishStageCut.first_run implementation setup wire note initial env past before
        change logged implementation _ _ _ _=_ at first
        rw [first,Functor.map_map,support_map] at supported
        obtain ⟨recorded,called,same⟩:=supported
        subst result
        exact Or.inr ⟨initial,recorded.1.1,rfl⟩
    | _=>
      rw [show RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement (n:=n) setup wire note _=pure _ from rfl,pure_run] at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl

theorem accepted (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse)
    (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted setup wire note owner scalar authenticated) env past before)) :
    Suffix note past result.1.2.2 :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted logged at supported
  simp only [StateT.run_bind,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,first,later⟩:=supported
  change middle∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift
    (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated))) env past before) at first
  rw [lift_run,support_map] at first
  obtain ⟨agreed,called,same⟩:=first
  subst middle
  exact after implementation setup wire note agreed.1.1 agreed.1.2 past agreed.2 result later

theorem body (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending packet owner scalar) env past before)) :
    Suffix note past result.1.2.2 :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body logged at supported
  simp only [StateT.run_bind,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,first,later⟩:=supported
  change middle∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift
    (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=mlSource) setup)
      (RegistrationResponseExecutor.begin pending packet))) env past before) at first
  rw [lift_run,support_map] at first
  obtain ⟨authenticated,called,same⟩:=first
  subst middle
  change result∈support (logged implementation
    (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication setup wire note owner scalar authenticated.1.1) authenticated.1.2 past authenticated.2) at later
  cases reply:authenticated.1.1 with
  | fail error | div=>
    simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication,reply] at later
    rw [pure_run] at later
    simp only [support_pure,Set.mem_singleton_iff] at later
    cases later
    exact Or.inl rfl
  | ok status=>cases status with
    | Err control=>
      simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication,reply] at later
      rw [pure_run] at later
      simp only [support_pure,Set.mem_singleton_iff] at later
      cases later
      exact Or.inl rfl
    | Ok response=>
      simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication,reply] at later
      exact accepted implementation setup wire note owner scalar response authenticated.1.2 past authenticated.2 result later

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.after

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix.body
