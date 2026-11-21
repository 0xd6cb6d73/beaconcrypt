-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFrontend
/-! The actual corrected finishing body factors through its source authentication/preparation prefix and its assigned-ID completion. The whole free materialization equation is derived from those actual bodies, retaining every terminal failure and complete local state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (Spec SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativePlatformMaterializedBeaconFrontend (translate)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)

private noncomputable def factored (packet : Option registration.ResponsePacket) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
      source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending _ => match pending.aborted_state with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok _ => do
        let prepared ← RegistrationBeaconReferenceCompiler.finishPreparation setup source packet
        RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner prepared
  | _ => pure (.ok none)

private theorem factor (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run env) =
      (((factored setup wire source packet).run owner).run env) := by
  simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, factored,
    StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted => rfl
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved]
      | ok aborted =>
          simp only [RegistrationBeaconReferenceCompiler.finishPreparation, StateT.run_bind, StateT.run_get,
            pure_bind, phase, moved, StateT.run_modify, StateT.run_set, StateT.run_lift,
            bind_pure_comp, bind_map_left, bind_assoc]
          apply bind_congr
          intro authenticated
          cases authenticated with
          | fail error | div =>
              simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformBeaconContinuation.afterPrepared]
          | ok accepted => cases accepted with
            | Err error => rfl
            | Ok accepted =>
              simp only [RegistrationNativePlatformBeaconPhase.phase, StateT.run_bind, StateT.run_lift,
                StateT.run_map, bind_pure_comp, bind_map_left]

/-- Literal response authentication, agreement, root reference demand, first opening and assigned-ID installation preserve the whole current finishing result under private seed materialization. -/
theorem finish_source (seeds : Seeds n) (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) :
    simulateQ (translate true seeds)
      (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env) =
      simulateQ (translate false seeds)
        (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env) := by
  rw [factor setup wire source packet owner env]
  simp only [factored, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted => rfl
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div => simp only [moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [moved, StateT.run_bind, simulateQ_bind]
          rw [RegistrationNativePlatformMaterializedBeaconFrontend.preparation_source]
          apply bind_congr
          rintro ⟨⟨prepared, current⟩, reached⟩
          exact RegistrationNativePlatformMaterializedBeaconFrontend.afterPrepared_source setup.source wire.frameWrite
            owner current prepared seeds reached
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFinish.finish_source
