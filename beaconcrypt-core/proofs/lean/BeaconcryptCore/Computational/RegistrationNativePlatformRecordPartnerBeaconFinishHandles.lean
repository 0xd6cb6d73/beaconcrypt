-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe
/-! The corrected complete Beacon continuation has the exact successful physical-owner handle suffix, retaining the actual material demand and all authentication, opening and refusal branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (handler update free)
open RegistrationBeaconReferenceCompiler (SelectedOwner effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformPublicSlotBeaconFinishSafe (compile)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- Both source material replies have exactly the successful physical-owner handle suffix of their returned application. -/
theorem complete (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (envBefore : EnvState Auxiliary) (before : List Handle)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (compile (n := n) setup scalar
      (RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source writer effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready) current envBefore)).run before)) :
    result.2=before++if role=.beacon ∧ present result.1.1.1=true then [.owner owner.worldOwner] else [] := by
  rw [RegistrationNativePlatformPublicSlotBeaconFinishSafe.complete_run] at supported
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,RegistrationNativePlatformPublicSlotEffects.demand,
    simulateQ_bind,simulateQ_spec_query] at supported
  simp only [handler,StateT.run,bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨choice,_queried,continued⟩ := supported
  cases choice with
  | none =>
      let failed : RustM RegistrationNativePairedBeaconService.Result := .ok (.Err ⟨0#u64⟩)
      change result∈support ((simulateQ (handler role)
        (((RegistrationNativePlatformBeaconMaterialFrontend.after
          (RegistrationNativePairedCompile.effects (n := n) (KemSK := KemSK)) owner failed).run current).run envBefore)).run before) at continued
      rw [← RegistrationNativePlatformBeaconMaterialFrontend.after_run] at continued
      obtain ⟨kept,value⟩ := RegistrationNativePlatformRecordPartnerBeaconHandles.settled_handles
        role owner current failed envBefore before result continued
      rw [kept,value]
      simp [failed,RegistrationNativeSecretWordInstallInsert.success]
  | some choice =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.chosen,StateT.run] at continued
      exact RegistrationNativePlatformRecordPartnerBeaconHandles.program_handles role setup.source writer owner current ready choice envBefore before result continued

private theorem finish_close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State) :
    compile (n := n) setup scalar (RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet) owner env =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error,owner),env)
        | .div => pure ((.div,owner),env)
        | .ok _ => do
            let reached ← compile setup scalar (RegistrationBeaconReferenceCompiler.finishPreparation setup source packet) owner env
            compile setup scalar (RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner reached.1.1) reached.1.2 reached.2
      | _ => pure ((.ok none,owner),env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
    simp only [compile,RegistrationNativePlatformBeaconReferenceFinish.finish,StateT.run_bind,
      StateT.run_get,pure_bind,ownerPhase,StateT.run_pure,simulateQ_pure]
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div =>
      simp only [compile,RegistrationNativePlatformBeaconReferenceFinish.finish,StateT.run_bind,
        StateT.run_get,pure_bind,ownerPhase,moved,StateT.run_pure,simulateQ_pure]
    | ok aborted =>
      simp only [compile,RegistrationNativePlatformBeaconReferenceFinish.finish,RegistrationBeaconReferenceCompiler.finishPreparation,
        StateT.run_bind,StateT.run_get,pure_bind,ownerPhase,moved,StateT.run_modify,StateT.run_set,
        StateT.run_lift,bind_pure_comp,bind_map_left,simulateQ_bind,bind_assoc]
      apply bind_congr
      intro accepted
      cases accepted with
      | fail error | div => simp only [StateT.run_pure,simulateQ_pure,pure_bind,RegistrationNativePlatformBeaconContinuation.afterPrepared]
      | ok response => cases response with
        | Err _ => simp only [StateT.run_pure,simulateQ_pure,pure_bind,RegistrationNativePlatformBeaconContinuation.afterPrepared]
        | Ok authenticated =>
          simp only [RegistrationNativePlatformBeaconPhase.phase,StateT.run_bind,StateT.run_lift,
            StateT.run_map,bind_pure_comp,bind_map_left,simulateQ_bind,simulateQ_map]

private theorem abort_handles (role : Role) (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) (value : RustM (Option Pqxdh.Bytes))
    (before : List Handle) (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (compile (n := n) setup scalar
      (RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value) current env)).run before)) :
    result.1.1.1=value ∧ result.2=before := by
  simp only [compile,RegistrationNativePlatformBeaconMaterialFrontend.abort,seqRight_eq_bind,
    StateT.run_lift,StateT.run_map,bind_pure_comp,simulateQ_map] at supported
  rw [←QueryImpl.apply_compose,RegistrationNativePlatformPairedBeaconRoute.environment] at supported
  simp only [RegistrationNativePairedCompile.effects,simulateQ_spec_query,Functor.map_map,support_map] at supported
  obtain ⟨reply,called,equal⟩ := supported
  simp only [handler,StateT.run,update,support_map] at called
  obtain ⟨actual,_queried,replyEq⟩ := called
  cases replyEq
  cases equal
  exact ⟨rfl,rfl⟩

/-- Every literal corrected Beacon finish has precisely the handle suffix of its same successful application result. -/
theorem finish (role : Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) (packet : Option registration.ResponsePacket) (before : List Handle)
    (result : ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State) × List Handle)
    (supported : result∈support ((simulateQ (handler role) (compile (n := n) setup scalar
      (RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet) owner env)).run before)) :
    result.2=before++if role=.beacon ∧ present result.1.1.1=true then [.owner owner.worldOwner] else [] := by
  rw [finish_close] at supported
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
    simp only [ownerPhase,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    subst result
    simp [present]
  | initSent pending oneTime =>
    simp only [ownerPhase] at supported
    cases moved : pending.aborted_state with
    | fail error | div =>
      simp only [moved,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      subst result
      simp [present]
    | ok aborted =>
      simp only [moved,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨prepared,possible,continued⟩ := supported
      have noInstall := RegistrationNativeInstallFreePreparation.preparation_free (n := n) role setup source packet owner env
      have bound := RegistrationNativePlatformPairedBeaconRoute.bound role setup scalar _ 0 noInstall
      have prefixEq := RegistrationNativePlatformRecordPartnerSnapshotHandles.free role _ bound before
      simp only [compile] at possible
      rw [prefixEq,support_map] at possible
      obtain ⟨reached,_called,equal⟩ := possible
      cases equal
      cases outcome : reached.1.1 with
      | fail error | div =>
        simp only [outcome,RegistrationNativePlatformBeaconContinuation.afterPrepared] at continued
        have ended := abort_handles role setup scalar owner reached.1.2 reached.2 _ before result continued
        rw [ended.1,ended.2]
        simp [present]
      | ok preparedValue => cases preparedValue with
        | none =>
          simp only [outcome,RegistrationNativePlatformBeaconContinuation.afterPrepared] at continued
          have ended := abort_handles role setup scalar owner reached.1.2 reached.2 (.ok none) before result continued
          rw [ended.1,ended.2]
          simp [present]
        | some ready =>
          exact complete role setup scalar wire.frameWrite owner reached.1.2 ready reached.2 before result
            (by simpa only [outcome,RegistrationNativePlatformBeaconContinuation.afterPrepared] using continued)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles.finish
