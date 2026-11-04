-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
import BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint
import BeaconcryptCore.Computational.RegistrationNativeFinishLowerErasure
import BeaconcryptCore.Computational.RegistrationResponseNormal
import BeaconcryptCore.Computational.RegistrationBeaconAgreementKey
import BeaconcryptCore.Computational.RegistrationBeaconRecordKey
import BeaconcryptCore.Computational.RegistrationBeaconRecordNormal
/-! The complete source Beacon return object and the actual native finish share one logged free request tree. Source rejection controls are derived from actual response, agreement and first-record continuations and their original identifier, rather than assumed equal. Native early-phase handling is factored after that same cryptographic tree. Source erasure discards only callback metadata; its exact returnedSelf and every Trusted primitive effect are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishNormalized
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Trusted Owner)
variable {n : Nat} {I J KemSK A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

theorem simulation_support {queries : OracleSpec J}
    (handler : QueryImpl queries (OracleComp (Trusted n KemSK))) (work : OracleComp queries A) :
    support (simulateQ handler work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact Set.Subset.rfl
  | query_bind query next ih =>
      intro result reached
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
      obtain ⟨reply, _, continued⟩ := reached
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply continued⟩

theorem aborted_eq (left right : pqxdh.BeaconAborted) (same : left.server_key_id = right.server_key_id) : left = right := by
  cases left
  cases right
  cases same
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

def output (self : beaconcrypt_public_wrapper.beacon.Beacon) (result : RustM (Option registration.CompletedBeacon)) :
    RustM AdapterPublicFinishBody.Result :=
  match result with
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok (.None, self)
  | .ok (some completed) => .ok (.Some completed.application, AdapterPublicFinishEndpoint.completedSelf self completed)

theorem record_output (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconAborted) (aborted : self.state = .Aborted control)
    (agreed : agreement.BeaconAgreement) (key : control.server_key_id = agreed.candidate.server_binding.identity_key_id) :
    AdapterPublicFinishFreeTree.recordSuffix (n := n) setup wire self (.BeaconComplete agreed) =
      output self <$> RegistrationNativeFinishLowerErasure.afterAgreement setup wire (.ok (.BeaconComplete agreed)) := by
  simp only [AdapterPublicFinishFreeTree.recordSuffix, RegistrationNativeFinishLowerErasure.afterAgreement, Functor.map_map]
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  have actual := simulation_support (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed) reached
  obtain ⟨normal, returned⟩ := RegistrationBeaconRecordNormal.begin_normal agreed result actual
  rw [returned] at actual ⊢
  cases normal with
  | Err rejected =>
      have same := aborted_eq rejected control ((RegistrationBeaconRecordKey.begin_rejected_key agreed rejected actual).trans key.symm)
      rw [same]
      change pure (AdapterPublicFinishEndpoint.sourceResult self (.ok (.Err control))) = pure (output self (.ok none))
      rw [AdapterPublicFinishEndpoint.source_aborted]
      simp only [output]
      rw [← aborted]
  | Ok completed =>
      change pure (AdapterPublicFinishEndpoint.sourceResult self (.ok (.Ok completed))) = pure (output self (.ok (some completed)))
      rw [AdapterPublicFinishEndpoint.source_completed]
      rfl

theorem accepted_output (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconAborted) (aborted : self.state = .Aborted control)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (key : control.server_key_id = authenticated.pending.control.expected_server_binding.identity_key_id) :
    AdapterPublicFinishFreeTree.accepted (n := n) setup wire self owner scalar authenticated =
      output self <$> RegistrationNativeFinishLowerErasure.accepted setup wire owner scalar authenticated := by
  simp only [AdapterPublicFinishFreeTree.accepted, RegistrationNativeFinishLowerErasure.accepted, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  have actual := simulation_support (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated) reached
  obtain ⟨phase, returned⟩ := RegistrationAgreementNormal.beacon_normal authenticated result actual
  rw [returned] at actual ⊢
  have phaseKey := RegistrationBeaconAgreementKey.beacon_key authenticated phase actual
  cases phase with
  | Rejected optional => cases optional with
    | none => simp only [AdapterPublicFinishFreeTree.recordSuffix, RegistrationNativeFinishLowerErasure.afterAgreement, output, map_pure]
    | some rejected =>
        have same := aborted_eq rejected control (phaseKey.trans key.symm)
        simp only [same, AdapterPublicFinishFreeTree.recordSuffix, RegistrationNativeFinishLowerErasure.afterAgreement, output, map_pure]
        rw [← aborted]
  | BeaconComplete agreed => exact record_output setup wire self control aborted agreed (key.trans phaseKey.symm)
  | _ => simp only [AdapterPublicFinishFreeTree.recordSuffix, RegistrationNativeFinishLowerErasure.afterAgreement, output, map_pure]

theorem program_output (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    AdapterPublicFinishFreeTree.program (n := n) setup wire self pending input owner scalar =
      output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} <$>
        RegistrationNativeFinishLowerErasure.body setup wire pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar := by
  simp only [AdapterPublicFinishFreeTree.program, RegistrationNativeFinishLowerErasure.body, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reply reached
  have actual := simulation_support (AdapterPublicFinishFreeTree.authentication (source := source) setup)
    (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))) reached
  rcases RegistrationResponseNormal.begin_shape pending _ reply actual with rejected | ⟨supplied, _, accepted⟩
  · rw [rejected]
    simp only [AdapterPublicFinishFreeTree.afterAuthentication, RegistrationNativeFinishLowerErasure.afterAuthentication, output, map_pure]
  · rw [accepted]
    exact accepted_output setup wire _ (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending) rfl owner scalar ⟨pending, supplied⟩ rfl


theorem program_journal {Auxiliary : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    AdapterPublicFinishFreeTree.program (n := n) setup wire self pending input owner scalar =
      (fun result => output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} result.1) <$>
        (RegistrationNativeFinishFactor.body setup wire pending
          (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar).run env := by
  rw [program_output]
  have erased := RegistrationNativeFinishLowerErasure.body_erasure (n := n) setup wire pending
    (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) owner scalar env
  have projected := congrArg (fun work => output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} <$> work) erased
  simpa only [Functor.map_map] using projected.symm

omit material ed in
theorem native_tree {Auxiliary : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (owners : List (Owner source))
    (selected : owners[index]? = some owner) (phase : owner.phase = .initSent pending scalar)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconFinish.finish (n := n) setup source wire index packet).run owners).run env) = (do
      let result ← (RegistrationNativeFinishFactor.body setup wire pending (match packet with | none => .None | some value => .Some value) owner scalar).run env
      (((do
        RegistrationNativeBeaconFrontend.updatePhase index (.aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending))
        RegistrationNativeFinishFactor.terminal index owner result.1 : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary _).run owners).run result.2)) := by
  rw [RegistrationNativeFinishFactor.active_factor setup wire index owner pending scalar packet owners selected phase,
    RegistrationNativeFinishFactor.delayed_phase]
  simp only [StateT.run_bind, RegistrationNativeBeaconPhaseCommutation.lift_run, bind_map_left]
  rfl


end BeaconcryptCore.Refinement.AdapterPublicFinishNormalized

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.simulation_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.simulation_support

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.aborted_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.aborted_eq

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.record_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.record_output

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.accepted_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.accepted_output

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.program_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.program_output

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.program_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.program_journal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.native_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNormalized.native_tree
