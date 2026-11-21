-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedTree
import BeaconcryptCore.Refinement.AdapterPublicFinishNormalized
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterFinishLoggedTree (M)
variable {n :Nat} {I KemSK A Log Auxiliary :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire) (note :Stage→Log)
variable [material :PublicWrapperPlatform.Material] [ed :AdapterInitEdPrimitive.Operations]

noncomputable def suffix (self :beaconcrypt_public_wrapper.beacon.Beacon) (effect :agreement.AgreementEffect) :M n KemSK Log (RustM AdapterPublicFinishBody.Result):=
  match effect with
  | .Rejected (.Some control)=>pure (.ok (.None,{self with state:=.Aborted control}))
  | .BeaconComplete agreed=>(fun result=>AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result)) <$>
      RegistrationNativePlatformPublicAdapterFinishLoggedTree.code setup wire note agreed
  | _=>pure (.ok (.None,self))

private theorem record_reply (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconAborted)
    (aborted :self.state=.Aborted control) (agreed :agreement.BeaconAgreement)
    (key :control.server_key_id=agreed.candidate.server_binding.identity_key_id)
    (result :RustM RegistrationBeaconRecordExecutor.Result)
    (supported :result∈support (simulateQ (RegistrationNativeRecordJournal.core (n:=n) setup wire) (RegistrationBeaconRecordExecutor.begin agreed))) :
    AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result)=
      AdapterPublicFinishNormalized.output self (RegistrationNativeFinishFactor.collapse result) :=by
  have actual:=AdapterPublicFinishNormalized.simulation_support (RegistrationNativeRecordJournal.core setup wire)
    (RegistrationBeaconRecordExecutor.begin agreed) supported
  obtain ⟨normal,returned⟩:=RegistrationBeaconRecordNormal.begin_normal agreed result actual
  rw [returned] at actual ⊢
  cases normal with
  | Err rejected=>
    have same:=AdapterPublicFinishNormalized.aborted_eq rejected control
      ((RegistrationBeaconRecordKey.begin_rejected_key agreed rejected actual).trans key.symm)
    rw [same]
    change AdapterPublicFinishEndpoint.sourceResult self (.ok (.Err control))=AdapterPublicFinishNormalized.output self (.ok none)
    rw [AdapterPublicFinishEndpoint.source_aborted]
    simp only [AdapterPublicFinishNormalized.output]
    rw [←aborted]
  | Ok completed=>
    change AdapterPublicFinishEndpoint.sourceResult self (.ok (.Ok completed))=AdapterPublicFinishNormalized.output self (.ok (some completed))
    rw [AdapterPublicFinishEndpoint.source_completed]
    rfl

theorem record_output (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconAborted)
    (aborted :self.state=.Aborted control) (agreed :agreement.BeaconAgreement)
    (key :control.server_key_id=agreed.candidate.server_binding.identity_key_id) (past :List Log) :
    (suffix (n:=n) setup wire note self (.BeaconComplete agreed)).run past=
      (fun result=>(AdapterPublicFinishNormalized.output self result.1,result.2)) <$>
        (RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAgreement setup wire note (.ok (.BeaconComplete agreed))).run past :=by
  simp only [suffix,RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAgreement,StateT.run_map,Functor.map_map]
  rw [map_eq_bind_pure_comp,map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨result,log⟩ possible
  have base:result∈support (simulateQ (RegistrationNativeRecordJournal.core (n:=n) setup wire) (RegistrationBeaconRecordExecutor.begin agreed)) :=by
    rw [←RegistrationNativePlatformPublicAdapterFinishLoggedTree.code_erase setup wire note agreed past,support_map]
    exact ⟨(result,log),possible,rfl⟩
  exact congrArg pure (congrArg (fun value=>(value,log)) (record_reply setup wire self control aborted agreed key result base))

noncomputable def accepted (self :beaconcrypt_public_wrapper.beacon.Beacon) (owner :Owner mlSource)
    (scalar :PqxdhJointGapDh.ScalarBytes) (authenticated :registration.AuthenticatedResponse) :M n KemSK Log (RustM AdapterPublicFinishBody.Result):=do
  let result←StateT.lift (simulateQ (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated))
  match result with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok effect=>suffix setup wire note self effect

omit material ed in
private theorem lift_support (work :OracleComp (Trusted n KemSK) A) (past :List Log) (result :A×List Log)
    (possible :result∈support ((StateT.lift work:M n KemSK Log A).run past)) :result.1∈support work :=by
  simp only [StateT.run,StateT.lift,bind_pure_comp,support_map] at possible
  obtain ⟨value,reached,same⟩:=possible
  exact congrArg Prod.fst same ▸ reached

theorem accepted_output (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconAborted)
    (aborted :self.state=.Aborted control) (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (authenticated :registration.AuthenticatedResponse)
    (key :control.server_key_id=authenticated.control.expected_server_binding.identity_key_id) (past :List Log) :
    (accepted (n:=n) setup wire note self owner scalar authenticated).run past=
      (fun result=>(AdapterPublicFinishNormalized.output self result.1,result.2)) <$>
        (RegistrationNativePlatformPublicAdapterFinishLoggedTree.accepted setup wire note owner scalar authenticated).run past :=by
  simp only [accepted,RegistrationNativePlatformPublicAdapterFinishLoggedTree.accepted,StateT.run_bind,map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨result,log⟩ reached
  have actual:=AdapterPublicFinishNormalized.simulation_support (RegistrationNativeAgreementJournal.core setup owner scalar)
    (RegistrationAgreementExecutor.beacon authenticated) (lift_support _ past (result,log) reached)
  obtain ⟨phase,returned⟩:=RegistrationAgreementNormal.beacon_normal authenticated result actual
  rw [returned] at actual ⊢
  have phaseKey:=RegistrationBeaconAgreementKey.beacon_key authenticated phase actual
  cases phase with
  | Rejected optional=>cases optional with
    | none=>simp only [suffix,RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAgreement,
        AdapterPublicFinishNormalized.output,StateT.run_pure,map_pure]
    | some rejected=>
      have same:=AdapterPublicFinishNormalized.aborted_eq rejected control (phaseKey.trans key.symm)
      simp only [same,suffix,RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAgreement,
        AdapterPublicFinishNormalized.output,StateT.run_pure,map_pure]
      rw [←aborted]
  | BeaconComplete agreed=>exact record_output setup wire note self control aborted agreed (key.trans phaseKey.symm) log
  | _=>simp only [suffix,RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAgreement,
      AdapterPublicFinishNormalized.output,StateT.run_pure,map_pure]

noncomputable def afterAuthentication (self :beaconcrypt_public_wrapper.beacon.Beacon) (owner :Owner mlSource)
    (scalar :PqxdhJointGapDh.ScalarBytes) (reply :RustM RegistrationResponseExecutor.ResponseResult) :M n KemSK Log (RustM AdapterPublicFinishBody.Result):=
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok (.Err control)=>pure (.ok (.None,{self with state:=.Aborted control}))
  | .ok (.Ok authenticated)=>accepted setup wire note self owner scalar authenticated

noncomputable def program (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) :M n KemSK Log (RustM AdapterPublicFinishBody.Result):=do
  let reply←StateT.lift (simulateQ (AdapterPublicFinishFreeTree.authentication (source:=mlSource) setup)
    (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))))
  afterAuthentication setup wire note {self with state:=.Aborted (RegistrationResponse.abortedState pending)} owner scalar reply

theorem program_output (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (past :List Log) :
    (program (n:=n) setup wire note self pending input owner scalar).run past=
      (fun result=>(AdapterPublicFinishNormalized.output {self with state:=.Aborted (RegistrationResponse.abortedState pending)} result.1,result.2)) <$>
        (RegistrationNativePlatformPublicAdapterFinishLoggedTree.body setup wire note pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar).run past :=by
  simp only [program,RegistrationNativePlatformPublicAdapterFinishLoggedTree.body,StateT.run_bind,map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨reply,log⟩ reached
  have actual:=AdapterPublicFinishNormalized.simulation_support (AdapterPublicFinishFreeTree.authentication (source:=mlSource) setup)
    (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
    (lift_support _ past (reply,log) reached)
  rcases RegistrationResponseNormal.begin_shape pending _ reply actual with rejected |⟨supplied,authenticated,_packet,_acceptedPacket,retained,accepted⟩
  · rw [rejected]
    simp only [afterAuthentication,RegistrationNativePlatformPublicAdapterFinishLoggedTree.afterAuthentication,
      AdapterPublicFinishNormalized.output,StateT.run_pure,map_pure]
  · rw [accepted]
    exact accepted_output setup wire note _ (RegistrationResponse.abortedState pending) rfl owner scalar authenticated (by rw [retained.1]; rfl) log

theorem program_projection (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (before :EnvState Auxiliary×List Log) :
    (program (n:=n) setup wire note self pending input owner scalar).run before.2=
      (fun result=>(AdapterPublicFinishNormalized.output {self with state:=.Aborted (RegistrationResponse.abortedState pending)} result.1,result.2.2)) <$>
        (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body setup wire note pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar).run before :=by
  rw [program_output]
  rw [←RegistrationNativePlatformPublicAdapterFinishLoggedTree.body_projection setup wire note pending
    (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar before,Functor.map_map]
  rfl

theorem program_erase (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (past :List Log) :
    Prod.fst <$>(program (n:=n) setup wire note self pending input owner scalar).run past=
      AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar :=by
  let env:EnvState Unit:=⟨(),[],[],[]⟩
  rw [program_projection setup wire note self pending input owner scalar (env,past),Functor.map_map]
  have erased:=RegistrationNativePlatformPublicAdapterFinishLoggedFactor.body_erase (n:=n) setup wire note pending
    (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar (env,past)
  have mapped:=congrArg (fun tree=>(fun result=>AdapterPublicFinishNormalized.output
    {self with state:=.Aborted (RegistrationResponse.abortedState pending)} result.1) <$>tree) erased
  simp only [Functor.map_map,Prod.map,id_eq] at mapped
  exact mapped.trans (AdapterPublicFinishNormalized.program_journal setup wire self pending input owner scalar env).symm

theorem program_safe (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes) (past :List Log) :
    ((program (n:=n) setup wire note self pending input owner scalar).run past).AllQueriesSatisfy
      (RegistrationNativeWorldOwnerFrame.Safe (n:=n) (KemSK:=KemSK)) :=by
  have safe:=RegistrationNativePlatformSdkFinishScope.program_safe (n:=n) setup wire self pending input owner scalar
  unfold RegistrationNativePlatformSdkFinishScope.Scoped at safe
  rw [←program_erase setup wire note self pending input owner scalar past,allQueriesSatisfy_def,isQueryBound_map_iff] at safe
  exact safe

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.record_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.record_output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.accepted_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.accepted_output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedOutput.program_safe
