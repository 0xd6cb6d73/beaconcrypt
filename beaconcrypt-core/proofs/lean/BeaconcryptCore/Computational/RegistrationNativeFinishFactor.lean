-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconPhaseCommutation
import BeaconcryptCore.Computational.RegistrationResponseNormal
/-! The actual corrected active Beacon finish factors into one complete logged cryptographic body and one terminal lifecycle action. The body includes authentication, NoEntropy agreement and first record, preserving optional failures and Rust outcomes. Its early aborted owner write commutes through the concrete lifted body, so the same full request execution may be related to source returnedSelf before applying the terminal World action. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishFactor
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeBeaconPhaseCommutation (Lower)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def collapse (result : RustM RegistrationBeaconRecordExecutor.Result) : RustM (Option registration.CompletedBeacon) :=
  match result with
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok completed) => .ok (some completed)

noncomputable def afterAgreement (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (result : RustM agreement.AgreementEffect) : Lower n KemSK Auxiliary (RustM (Option registration.CompletedBeacon)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.BeaconComplete agreed) => collapse <$> simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) (RegistrationBeaconRecordExecutor.begin agreed)
  | .ok _ => pure (.ok none)

noncomputable def accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Lower n KemSK Auxiliary (RustM (Option registration.CompletedBeacon)) := do
  let agreed ← simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)
  afterAgreement setup wire agreed

noncomputable def afterAuthentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (result : RustM RegistrationResponseExecutor.ResponseResult) :
    Lower n KemSK Auxiliary (RustM (Option registration.CompletedBeacon)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok authenticated) => accepted setup wire owner scalar authenticated

noncomputable def body (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) : Lower n KemSK Auxiliary (RustM (Option registration.CompletedBeacon)) := do
  let authenticated ← simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source := source) setup)
    (RegistrationResponseExecutor.begin pending packet)
  afterAuthentication setup wire owner scalar authenticated

noncomputable def terminal (index : Nat) (owner : Owner source) (result : RustM (Option registration.CompletedBeacon)) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match result with
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok none => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (some completed) => RegistrationNativePlatformBeaconFinish.install index owner completed

theorem accepted_factor (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner scalar authenticated = (do
      let result ← RegistrationNativeBeaconPhaseCommutation.lift (accepted setup wire owner scalar authenticated)
      terminal index owner result) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith accepted
  rw [RegistrationNativeBeaconPhaseCommutation.lift_bind]
  have leaves := funext (RegistrationNativeBeaconPhaseCommutation.agreement_lift (n := n) (Auxiliary := Auxiliary) setup owner scalar)
  rw [leaves, RegistrationNativeBeaconPhaseCommutation.simulate_lift]
  simp only [bind_assoc]
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => simp only [afterAgreement, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]
  | ok phase => cases phase with
    | BeaconComplete completed =>
        have recordLeaves := funext (RegistrationNativeBeaconPhaseCommutation.record_lift (n := n) (source := source) (Auxiliary := Auxiliary) setup wire)
        simp only [recordLeaves, RegistrationNativeBeaconPhaseCommutation.simulate_lift, afterAgreement, map_eq_bind_pure_comp, RegistrationNativeBeaconPhaseCommutation.lift_bind, bind_assoc]
        apply bind_congr
        intro opened
        cases opened with
        | fail error | div => simp only [collapse, Function.comp_apply, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]
        | ok result => cases result <;> simp only [collapse, Function.comp_apply, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]
    | _ => simp only [afterAgreement, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]

theorem authentication_factor (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    (match reply with
      | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
      | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
      | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
      | .ok (.Ok authenticated) => RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner scalar authenticated) = (do
      let result ← RegistrationNativeBeaconPhaseCommutation.lift (afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire owner scalar reply)
      terminal index owner result) := by
  cases reply with
  | fail error | div => simp only [afterAuthentication, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]
  | ok result => cases result with
    | Err control => simp only [afterAuthentication, RegistrationNativeBeaconPhaseCommutation.lift_pure, pure_bind, terminal]
    | Ok authenticated => exact accepted_factor setup wire index owner scalar authenticated

noncomputable def active (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : core.option.Option registration.ResponsePacket) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  RegistrationNativeBeaconFrontend.updatePhase index (.aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending))
  let result ← RegistrationNativeBeaconPhaseCommutation.lift (body setup wire pending packet owner scalar)
  terminal index owner result

theorem active_factor (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (owners : List (Owner source))
    (selected : owners[index]? = some owner) (phase : owner.phase = .initSent pending scalar) :
    (RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet).run owners =
      (active setup wire index owner pending scalar (match packet with | none => .None | some value => .Some value)).run owners := by
  have factor : (do
      let reply ← simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
        (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
      match reply with
      | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
      | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
      | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
      | .ok (.Ok authenticated) => RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner scalar authenticated : M n KemSK source Auxiliary _) = (do
      let result ← RegistrationNativeBeaconPhaseCommutation.lift (body setup wire pending (match packet with | none => .None | some value => .Some value) owner scalar)
      terminal index owner result) := by
    unfold body
    rw [RegistrationNativeBeaconPhaseCommutation.lift_bind]
    have leaves := funext (RegistrationNativeBeaconPhaseCommutation.authentication_lift (n := n) (source := source) (Auxiliary := Auxiliary) setup)
    rw [leaves, RegistrationNativeBeaconPhaseCommutation.simulate_lift]
    simp only [bind_assoc]
    apply bind_congr
    intro reply
    exact authentication_factor setup wire index owner scalar reply
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith active
  simp only [StateT.run_bind, StateT.run_get, pure_bind, selected, phase, RegistrationResponseNormal.aborted_exact]
  have applied := congrArg (fun work : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) =>
    (RegistrationNativeBeaconFrontend.updatePhase index (.aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)) *> work).run owners) factor
  simp only [seqRight_eq_bind, StateT.run_bind, RegistrationNativePlatformBeaconFinish.afterAuthentication] at applied ⊢
  exact applied


theorem delayed_phase (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : core.option.Option registration.ResponsePacket) :
    active (n := n) (Auxiliary := Auxiliary) setup wire index owner pending scalar packet = (do
      let result ← RegistrationNativeBeaconPhaseCommutation.lift (body setup wire pending packet owner scalar)
      RegistrationNativeBeaconFrontend.updatePhase index (.aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending))
      terminal index owner result) := by
  unfold active
  have commutes := RegistrationNativeBeaconPhaseCommutation.phase_commutes (source := source) index
    (.aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)) (body (n := n) (Auxiliary := Auxiliary) setup wire pending packet owner scalar)
  have applied := congrArg (fun work : M n KemSK source Auxiliary (RustM (Option registration.CompletedBeacon)) => work >>= terminal index owner) commutes
  simpa only [seqRight_eq_bind, bind_assoc, pure_bind] using applied


end BeaconcryptCore.Computational.RegistrationNativeFinishFactor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishFactor.accepted_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishFactor.accepted_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishFactor.authentication_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishFactor.authentication_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishFactor.active_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishFactor.active_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishFactor.delayed_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishFactor.delayed_phase
