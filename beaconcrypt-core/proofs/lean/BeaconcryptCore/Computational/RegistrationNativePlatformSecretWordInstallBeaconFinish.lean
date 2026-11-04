-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
/-! Exact successful installation accounting for the corrected Word finish, including optional scalar preparation, authentication failures and the actual assigned-ID first-record continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativePlatformSecretWordInstallBeaconComplete (compile abort complete_all)
open RegistrationNativePlatformSecretWordFinish (finish afterPrepared phase)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private noncomputable def close {Value : Type} (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformSecretWordFinish.M n KemSK Auxiliary source Value)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) :=
  compile setup scalar ((work.run owner).run env)

private theorem finish_close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : EnvState Auxiliary) :
    close (n := n) setup ownScalar (finish setup wire source packet) owner env =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error, owner), env)
        | .div => pure ((.div, owner), env)
        | .ok _ => do
            let reached ← close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env
            close setup ownScalar (afterPrepared setup.source wire.frameWrite owner reached.1.1) reached.1.2 reached.2
      | _ => pure ((.ok none, owner), env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, StateT.run_pure, simulateQ_pure]
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [close, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile, finish, RegistrationNativeSecretWordBeaconCompiler.finishPreparation,
            StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_modify, StateT.run_set,
            StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, bind_assoc]
          apply bind_congr
          intro accepted
          cases accepted with
          | fail error | div => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
          | ok response => cases response with
            | Err _ => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
            | Ok authenticated =>
                simp only [phase, StateT.run_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, bind_map_left, simulateQ_bind, simulateQ_map]

/-- Every actual corrected finish has the exact successful own-role suffix of its same public result. -/
theorem finish (role : Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) (packet : Option registration.ResponsePacket) (before : State)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) setup scalar
      (((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner).run env))).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = if role = .beacon ∧ present result.1.1.1 = true then 1 else 0 := by
  change result ∈ support ((simulateQ handler (close setup scalar
    (RegistrationNativePlatformSecretWordFinish.finish setup wire source packet) owner env)).run before) at supported
  rw [finish_close] at supported
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
    simp only [ownerPhase, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
  | initSent pending oneTime =>
    simp only [ownerPhase] at supported
    cases moved : pending.aborted_state with
    | fail error | div =>
      simp only [moved, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
    | ok aborted =>
      simp only [moved, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨prepared, possible, continued⟩ := supported
      have noInstall := RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free (n := n) role setup source packet owner env
      have bound := RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0 noInstall
      have prefixEq := RegistrationNativeSecretWordInstallTrace.free role _ bound before prepared possible
      cases outcome : prepared.1.1.1 with
      | fail error | div =>
        simp only [outcome, afterPrepared] at continued
        have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 _ prepared.2 result continued
        refine ⟨[], ?_, ?_⟩
        · rw [ended.2, prefixEq, List.append_nil]
        · rw [ended.1]; simp [present]
      | ok preparedValue => cases preparedValue with
        | none =>
          simp only [outcome, afterPrepared] at continued
          have ended := abort setup scalar owner prepared.1.1.2 prepared.1.2 (.ok none) prepared.2 result continued
          refine ⟨[], ?_, ?_⟩
          · rw [ended.2, prefixEq, List.append_nil]
          · rw [ended.1]; simp [present]
        | some ready =>
          have completed := complete_all role setup scalar setup.source wire.frameWrite owner prepared.1.1.2 ready prepared.1.2 prepared.2 result
            (by simpa only [outcome, afterPrepared, close] using continued)
          refine ⟨if role = .beacon ∧ present result.1.1.1 = true then [ready.reference] else [], ?_, ?_⟩
          · rw [completed, prefixEq]
          · split <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish.finish
