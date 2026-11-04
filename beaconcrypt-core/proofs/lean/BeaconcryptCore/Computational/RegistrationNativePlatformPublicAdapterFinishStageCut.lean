-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedFactor
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK Auxiliary Log S A :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK Auxiliary
local notation "Logged"=>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.M n KemSK Auxiliary Log
variable (implementation :QueryImpl (Trusted n KemSK) (StateT S ProbComp))

noncomputable def run (work :Lower A) (env :EnvState Auxiliary) (before :S) :=
  (simulateQ implementation (work.run env)).run before

noncomputable def logged (work :Logged A) (env :EnvState Auxiliary) (past :List Log) (before :S) :=
  (simulateQ implementation (work.run (env,past))).run before

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

theorem first_run (initial :registration.BeaconInitialKdf) (env :EnvState Auxiliary) (past :List Log) (before :S) :
    logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord setup wire note initial) env past before=
      (fun result=>((result.1.1,(result.1.2,past++[note (.beaconFirstRecord initial result.1.1)])),result.2)) <$>
        run implementation (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire)
          (RegistrationBeaconRecordExecutor.fromInitial initial)) env before :=by
  have first:(RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord (n:=n) setup wire note initial).run (env,past)=
      (fun result=>(result.1,(result.2,past++[note (.beaconFirstRecord initial result.1)]))) <$>
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)).run env :=by
    simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord,StateT.run,bind_pure_comp]
  unfold logged
  rw [first,simulateQ_map,StateT.run_map]
  rfl

theorem after_cut (injective :Function.Injective note)
    (initial :registration.BeaconInitialKdf) (completed :registration.CompletedBeacon)
    (reply :RustM agreement.AgreementEffect) (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement setup wire note reply) env past before))
    (present :note (.beaconFirstRecord initial (.ok (.Ok completed)))∈result.1.2.2) :
    note (.beaconFirstRecord initial (.ok (.Ok completed)))∈past ∨
      reply=.ok (.BeaconComplete initial.agreement) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      ((.ok (.Ok completed),result.1.2.1),result.2)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) env before) ∧
      result.1.1=.ok (some completed) :=by
  cases reply with
  | fail error | div=>
    rw [show RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement (n:=n) setup wire note _=pure _ from rfl,
      pure_run] at supported
    simp only [support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl present
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement at supported
      cases started:registration.begin_beacon_completion agreed with
      | fail error | div=>
        simp only [started] at supported
        rw [pure_run] at supported
        simp only [support_pure,Set.mem_singleton_iff] at supported
        cases supported
        exact Or.inl present
      | ok actual=>
        simp only [started,logged,StateT.run_map,simulateQ_map,StateT.run_map] at supported
        change result∈support (Prod.map (Prod.map RegistrationNativeFinishFactor.collapse id) id <$>
          logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.firstRecord setup wire note actual) env past before) at supported
        rw [first_run,Functor.map_map,support_map] at supported
        obtain ⟨recorded,called,same⟩:=supported
        subst result
        change note (.beaconFirstRecord initial (.ok (.Ok completed)))∈past++[note (.beaconFirstRecord actual recorded.1.1)] at present
        rcases List.mem_append.mp present with prior|last
        · exact Or.inl prior
        · have same:=List.mem_singleton.mp last
          obtain ⟨sameInitial,sameReply⟩:=Stage.beaconFirstRecord.inj (injective same)
          subst actual
          have own:=RegistrationBeaconRecordExecutor.initial_agreement agreed initial started
          subst agreed
          right
          refine ⟨rfl,started,?_,?_⟩
          · simpa only [sameReply,Prod.map_def,id_eq] using called
          · change RegistrationNativeFinishFactor.collapse recorded.1.1=.ok (some completed)
            rw [←sameReply]
            rfl
    | _=>
      rw [show RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAgreement (n:=n) setup wire note _=pure _ from rfl,
        pure_run] at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl present

theorem accepted_cut (injective :Function.Injective note)
    (initial :registration.BeaconInitialKdf) (completed :registration.CompletedBeacon)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse)
    (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation
      (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted setup wire note owner scalar authenticated) env past before))
    (present :note (.beaconFirstRecord initial (.ok (.Ok completed)))∈result.1.2.2) :
    note (.beaconFirstRecord initial (.ok (.Ok completed)))∈past ∨
      ∃middleEnv middle,
      ((.ok (.BeaconComplete initial.agreement),middleEnv),middle)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)) env before) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      ((.ok (.Ok completed),result.1.2.1),result.2)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) middleEnv middle) ∧
      result.1.1=.ok (some completed) :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted logged at supported
  simp only [StateT.run_bind,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,first,later⟩:=supported
  change middle∈support (logged implementation (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.lift
    (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated))) env past before) at first
  rw [lift_run,support_map] at first
  obtain ⟨agreed,called,same⟩:=first
  subst middle
  have cut:=after_cut implementation setup wire note injective initial completed agreed.1.1 agreed.1.2 past agreed.2 result later present
  rcases cut with prior|⟨actual,begun,recorded,answer⟩
  · exact Or.inl prior
  · exact Or.inr ⟨agreed.1.2,agreed.2,actual ▸called,begun,recorded,answer⟩

theorem body_cut (injective :Function.Injective note)
    (initial :registration.BeaconInitialKdf) (completed :registration.CompletedBeacon)
    (pending :registration.BeaconPending) (packet :core.option.Option registration.ResponsePacket)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (env :EnvState Auxiliary) (past :List Log) (before :S)
    (result :(RustM (Option registration.CompletedBeacon)×(EnvState Auxiliary×List Log))×S)
    (supported :result∈support (logged implementation
      (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending packet owner scalar) env past before))
    (present :note (.beaconFirstRecord initial (.ok (.Ok completed)))∈result.1.2.2) :
    note (.beaconFirstRecord initial (.ok (.Ok completed)))∈past ∨
      ∃authenticated authenticatedEnv authenticatedState middleEnv middle,
      ((.ok (.Ok authenticated),authenticatedEnv),authenticatedState)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=mlSource) setup)
          (RegistrationResponseExecutor.begin pending packet)) env before) ∧
      ((.ok (.BeaconComplete initial.agreement),middleEnv),middle)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)) authenticatedEnv authenticatedState) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      ((.ok (.Ok completed),result.1.2.1),result.2)∈support (run implementation
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.fromInitial initial)) middleEnv middle) ∧
      result.1.1=.ok (some completed) :=by
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
    change result∈support (logged implementation (pure _) authenticated.1.2 past authenticated.2) at later
    rw [pure_run] at later
    simp only [support_pure,Set.mem_singleton_iff] at later
    cases later
    exact Or.inl present
  | ok status=>cases status with
    | Err control=>
      simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication,reply] at later
      change result∈support (logged implementation (pure _) authenticated.1.2 past authenticated.2) at later
      rw [pure_run] at later
      simp only [support_pure,Set.mem_singleton_iff] at later
      cases later
      exact Or.inl present
    | Ok response=>
      simp only [RegistrationNativePlatformPublicAdapterFinishLoggedFactor.afterAuthentication,reply] at later
      change result∈support (logged implementation
        (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.accepted setup wire note owner scalar response) authenticated.1.2 past authenticated.2) at later
      rcases accepted_cut implementation setup wire note injective initial completed owner scalar response authenticated.1.2 past authenticated.2 result later present with prior|⟨middleEnv,middle,agreement,begun,recorded,answer⟩
      · exact Or.inl prior
      · refine Or.inr ⟨response,authenticated.1.2,authenticated.2,middleEnv,middle,?_,agreement,begun,recorded,answer⟩
        simpa only [←reply] using called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.first_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.first_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.after_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.after_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.accepted_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.accepted_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.body_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishStageCut.body_cut
