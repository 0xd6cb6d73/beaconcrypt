-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse
/-! The current corrected registration finish executes the actual extracted response request tree, followed by the unchanged agreement, first-record, byte-copy and assigned-identifier installation continuation. The free equality may be closed by any persistent interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Owner)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def response (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    M n KemSK source Auxiliary (RustM RegistrationResponseExecutor.ResponseResult) :=
  simulateQ (RegistrationNativeBeaconFrontend.authentication setup source ∘ₛ AdapterAuthenticationStatefulResponse.native)
    (AdapterAuthenticationRequestExtraction.authenticate (m:=AdapterAuthenticationRequestMonad.Program) pending packet).run

/-- Lowering the actual extracted request tree retains every authentication result and callback effect. -/
theorem response_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    response (n:=n) (Auxiliary:=Auxiliary) setup source pending packet =
      simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) (RegistrationResponseExecutor.begin pending packet) := by
  unfold response
  rw [QueryImpl.simulateQ_compose]
  change simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
    (AdapterAuthenticationStatefulResponse.authenticate pending packet) = _
  rw [AdapterAuthenticationStatefulResponse.source]

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let owners←get
  match owners[index]? with
  | none=>pure (.ok none)
  | some owner=>match owner.phase with
    | .initSent pending oneTime=>
      match pending.aborted_state with
      | .fail error=>pure (.fail error)
      | .div=>pure .div
      | .ok aborted=>do
        RegistrationNativeBeaconFrontend.updatePhase index (.aborted aborted)
        let authenticated←response setup source pending packet
        match authenticated with
        | .fail error=>RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
        | .div=>RegistrationNativeBeaconFrontend.abort owner *> pure .div
        | .ok (.Err _)=>RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
        | .ok (.Ok accepted)=>RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner oneTime accepted
    | _=>pure (.ok none)

/-- The exact current finish context consumes the extracted response source, including abort order and all failed continuations. -/
theorem finish_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    finish (n:=n) (Auxiliary:=Auxiliary) setup source wire index packet =
      RegistrationNativePlatformBeaconFinish.finish setup source wire index packet := by
  simp only [finish, response_source, RegistrationNativePlatformBeaconFinish.finish,
    RegistrationNativePlatformBeaconFinish.finishWith, RegistrationNativePlatformBeaconFinish.afterAuthentication]
  cases packet <;> rfl

/-- The actual current native interpreter and arbitrary persistent platform coins preserve the complete same execution. -/
theorem interpreted {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created
      (finish setup source wire index packet))).run before).run previous =
    ((RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet))).run before).run previous := by
  rw [finish_source]
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.response_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.finish_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish.interpreted
