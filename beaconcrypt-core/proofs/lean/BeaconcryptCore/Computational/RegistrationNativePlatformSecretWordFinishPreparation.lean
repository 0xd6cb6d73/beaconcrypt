-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
/-! The corrected incoming controller factors through its unchanged exact authentication/ordered-preparation source helper. The new assigned-ID material program remains the continuation. Early terminal/error returns and every current owner/environment effect retain their original order. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishPreparation
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}

noncomputable def program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformSecretWordFinish.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending _ => match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok _ => do
          let ready ← RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet
          RegistrationNativePlatformSecretWordFinish.afterPrepared setup.source wire.frameWrite owner ready
  | _ => pure (.ok none)

/-- The complete corrected source uses the same exact preparation helper followed by the actual new material continuation. -/
theorem source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run before) =
      (((program setup wire source packet).run owner).run before) := by
  simp only [RegistrationNativePlatformSecretWordFinish.finish, program, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => rfl
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved]
    | ok aborted =>
      simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind,
        phase, moved, StateT.run_set, StateT.run_modify, StateT.run_lift, bind_pure_comp, bind_map_left, bind_assoc]
      apply bind_congr
      intro authenticated
      cases authenticated with
      | fail error | div =>
        simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformSecretWordFinish.afterPrepared]
      | ok value => cases value with
        | Err previous =>
          simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformSecretWordFinish.afterPrepared]
        | Ok authenticated =>
          simp only [RegistrationNativePlatformSecretWordFinish.phase, StateT.run_bind, StateT.run_lift,
            StateT.run_map, bind_pure_comp, bind_map_left]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishPreparation.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishPreparation.source
