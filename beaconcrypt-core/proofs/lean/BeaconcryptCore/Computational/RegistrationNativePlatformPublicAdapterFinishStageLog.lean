-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishClosedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
variable {n :Nat} {I KemSK P A B Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
abbrev Spec :OracleSpec registration.BeaconInitialKdf:=fun _=>RustM RegistrationBeaconRecordExecutor.Result
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Base"=>StateT P ProbComp
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created Unit)
variable (wire :RegistrationNativeWire.Wire) (note :Stage→Log)

noncomputable def tree (initial :registration.BeaconInitialKdf) :OracleComp (Trusted n KemSK) (RustM RegistrationBeaconRecordExecutor.Result):=
  simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)

private theorem simulate_safe {J :Type} {queries :OracleSpec J}
    (handler :QueryImpl queries (OracleComp (Trusted n KemSK)))
    (safe :∀query,(handler query).AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (n:=n) (KemSK:=KemSK)))
    (work :OracleComp queries A) :
    (simulateQ handler work).AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (n:=n) (KemSK:=KemSK)) :=by
  induction work using OracleComp.inductionOn with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query]
    exact allQueriesSatisfy_bind (safe query) ih

private theorem coins_safe (work :ProbComp A) :
    (RegistrationNativeAgreementJournal.coins (n:=n) (KemSK:=KemSK) work).AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (n:=n) (KemSK:=KemSK)) :=
  simulate_safe (queries:=unifSpec)
    (fun query=>((Trusted n KemSK).query (.inl (.inl query)):OracleComp (Trusted n KemSK) _) )
    (fun _query=>(allQueriesSatisfy_query_iff _ _).mpr trivial) work

theorem tree_safe (initial :registration.BeaconInitialKdf) :
    (tree (n:=n) setup wire initial).AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (n:=n) (KemSK:=KemSK)) :=by
  apply simulate_safe
  intro query
  cases query with
  | hash transcript=>
    unfold RegistrationNativeRecordJournal.core
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>allQueriesSatisfy_pure _ _)
  | _=>exact coins_safe _

noncomputable def native :QueryImpl Spec (StateT Native Base):=fun initial=>
  RegistrationNativePlatformInterpret.state coins
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) (tree setup wire initial))

noncomputable def physical :QueryImpl Spec (StateT (Backend n KemSK) Base):=fun initial=>
  RegistrationNativePlatformInterpret.state coins
    (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created) (tree setup wire initial))

def observation (initial :Spec.Domain) (reply :Spec.Range initial) :List Log:=[note (.beaconFirstRecord initial reply)]

theorem query_source (initial :registration.BeaconInitialKdf) (before :Native) :
    Prod.map id (fun state=>erase (backend state)) <$>
      (native coins setup checks representation created wire initial).run before=
      (physical coins setup checks representation created wire initial).run (erase (backend before)) :=by
  have first:=RegistrationNativePlatformSdkFinishBackend.program setup checks representation created (tree setup wire initial) (tree_safe setup wire initial) before
  have second:=RegistrationNativePlatformSdkFinishWorld.program setup checks representation created (tree setup wire initial)
    (RegistrationNativePlatformSdkFinishWorld.record_program setup wire (RegistrationBeaconRecordExecutor.fromInitial initial)) (backend before)
  have law:Prod.map id (fun state=>erase (backend state)) <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) (tree setup wire initial)).run before=
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created) (tree setup wire initial)).run (erase (backend before)) :=by
    have mapped:=congrArg (fun work=>Prod.map id erase <$>work) first
    simp only [Functor.map_map,Prod.map_def,id_eq] at mapped
    exact mapped.trans second
  apply StateT.ext
  intro previous
  have observed:=congrArg (fun work=>(simulateQ coins work).run previous) law
  simp only [simulateQ_map,StateT.run_map] at observed
  refine (StateT.run_map (Prod.map id (fun state=>erase (backend state)))
    ((native coins setup checks representation created wire initial).run before) previous).trans ?_
  exact observed

theorem program_source (work :OracleComp Spec A) (before :Native×List Log) :
    Prod.map id (Prod.map (fun state=>erase (backend state)) id) <$>
      (simulateQ (recorded (native coins setup checks representation created wire) (observation note)) work).run before=
      (simulateQ (recorded (physical coins setup checks representation created wire) (observation note)) work).run (erase (backend before.1),before.2) :=
  RegistrationNativePlatformPublicAdapterSourceTrace.source _ _ _ (query_source coins setup checks representation created wire) (observation note) work before

theorem erase_program (work :OracleComp Spec A) (before :Backend n KemSK×List Log) :
    Prod.map id Prod.fst <$>
      (simulateQ (recorded (physical coins setup checks representation created wire) (observation note)) work).run before=
      (simulateQ (physical coins setup checks representation created wire) work).run before.1 :=
  RegistrationNativePlatformPublicAdapterSourceTrace.erase _ _ work before

def code (agreed :agreement.BeaconAgreement) :OracleComp Spec (RustM RegistrationBeaconRecordExecutor.Result):=
  match registration.begin_beacon_completion agreed with
  | .ok initial=>Spec.query initial
  | .fail error=>pure (.fail error)
  | .div=>pure .div

theorem physical_body (initial :registration.BeaconInitialKdf) :
    physical (n:=n) coins setup checks representation created wire initial=
      simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire
        (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks representation created))
        (RegistrationBeaconRecordExecutor.fromInitial initial) :=by
  unfold physical tree RegistrationNativePlatformSdkFinishPhysicalBody.trusted
  rw [RegistrationNativePlatformInterpret.state_simulate]
  rw [←QueryImpl.simulateQ_compose]
  rfl

theorem code_body (agreed :agreement.BeaconAgreement) :
    simulateQ (physical (n:=n) coins setup checks representation created wire) (code agreed)=
      simulateQ (RegistrationNativePlatformSdkFinishDictionaries.record setup wire
        (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks representation created))
        (RegistrationBeaconRecordExecutor.begin agreed) :=by
  unfold code RegistrationBeaconRecordExecutor.begin RegistrationBeaconRecordExecutor.continueWith
  cases registration.begin_beacon_completion agreed with
  | ok initial=>simpa only [simulateQ_spec_query] using physical_body coins setup checks representation created wire initial
  | fail error | div=>rw [simulateQ_pure,simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.tree_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.tree_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.erase_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.erase_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.physical_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.physical_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.code_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageLog.code_body
