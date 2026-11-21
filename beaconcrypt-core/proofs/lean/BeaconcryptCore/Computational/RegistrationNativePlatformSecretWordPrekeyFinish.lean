-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence
/-! The corrected symbolic finish preserves the exact captured public prekey through actual authentication, ordered preparation, assigned-ID installation and every material/record failure. This is a source field frame, independent of signing origin or a whole frontend equation. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyFinish
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι κ KemSK Auxiliary Value Next : Type} {base : OracleSpec ι} {target : OracleSpec κ}
variable {source : RegistrationNativeMldsa.Source}
private abbrev OM (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec κ) (Value : Type) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp target)) Value

def Sound (expected : Std.Array U8 32#usize) (owner : SelectedOwner source) : Prop :=
  owner.prekeyPublic = expected

private def Keeps (expected : Std.Array U8 32#usize) (work : OM source Auxiliary target Value) : Prop :=
  ∀ owner env result, Sound expected owner → result ∈ support ((work.run owner).run env) → Sound expected result.1.2

private theorem pure_keeps (expected : Std.Array U8 32#usize) (value : Value) :
    Keeps expected (pure value : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem bind_keeps (expected : Std.Array U8 32#usize) (work : OM source Auxiliary target Value)
    (next : Value → OM source Auxiliary target Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owner env result prior present
  simp only [StateT.run_bind, mem_support_bind_iff] at present
  obtain ⟨middle, called, continued⟩ := present
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle prior called) continued

private theorem lift_keeps (expected : Std.Array U8 32#usize) (work : StateT (EnvState Auxiliary) (OracleComp target) Value) :
    Keeps expected (StateT.lift work : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at present
  obtain ⟨middle, _called, returned⟩ := present
  cases returned
  exact prior

private theorem phase_keeps (expected : Std.Array U8 32#usize) (phase : RegistrationNativeBeaconFrontend.Phase)
    :
    Keeps expected ((modify fun (owner : SelectedOwner source) => {owner with phase}) : OM source Auxiliary target Unit) := by
  intro owner env result prior present
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem abort_keeps (expected : Std.Array U8 32#usize)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target)) (owner : SelectedOwner source) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.abort
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private theorem after_keeps (expected : Std.Array U8 32#usize)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target)) (owner : SelectedOwner source)
    (result : RustM RegistrationNativePairedBeaconService.Result) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.after environment owner result) := by
  cases result with
  | fail error | div =>
    rw [RegistrationNativePlatformBeaconMaterialFrontend.after, seqRight_eq_bind]
    exact bind_keeps expected _ _ (abort_keeps expected environment owner) (fun _ => pure_keeps expected _)
  | ok selected => cases selected with
    | Err error =>
      rw [RegistrationNativePlatformBeaconMaterialFrontend.after, seqRight_eq_bind]
      exact bind_keeps expected _ _ (abort_keeps expected environment owner) (fun _ => pure_keeps expected _)
    | Ok completed =>
      exact bind_keeps expected _ _ (phase_keeps expected (.established completed)) (fun _ => pure_keeps expected _)

private theorem material_program_keeps (expected : Std.Array U8 32#usize)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.program
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro _
  dsimp only
  split
  · exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ =>
      bind_keeps expected _ _ (lift_keeps expected _) (fun result => after_keeps expected _ owner result))
  · exact bind_keeps expected _ _ (lift_keeps expected _) (fun result => after_keeps expected _ owner result)

private theorem chosen_keeps (expected : Std.Array U8 32#usize)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer environment owner ready choice) := by
  intro current env result prior present
  exact material_program_keeps expected crypto writer owner ready choice current env result prior
    (RegistrationNativePublicSourceSupport.simulate_support environment _ result present)

private theorem complete_keeps (expected : Std.Array U8 32#usize)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationNativeSecretWordMessage.BeaconReady) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformSecretWordFinish.complete (n := n) (KemSK := KemSK) crypto writer owner ready) := by
  unfold RegistrationNativePlatformSecretWordFinish.complete
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro selected
  cases selected with
  | none =>
    rw [seqRight_eq_bind]
    exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
  | some choice => exact chosen_keeps expected crypto writer _ owner (ready.eval RegistrationNativeSecretWordMessage.zero) choice

private theorem prepared_keeps (expected : Std.Array U8 32#usize)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (result : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) :
    Keeps (Auxiliary := Auxiliary) expected
      (RegistrationNativePlatformSecretWordFinish.afterPrepared (n := n) (KemSK := KemSK) crypto writer owner result) := by
  unfold RegistrationNativePlatformSecretWordFinish.afterPrepared
  cases result with
  | fail error | div =>
    rw [seqRight_eq_bind]
    exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
  | ok selected => cases selected with
    | none =>
      rw [seqRight_eq_bind]
      exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
    | some ready => exact complete_keeps expected crypto writer owner ready

private theorem agreement_keeps (expected : Std.Array U8 32#usize) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformSecretWordFinish.phase (n := n) setup wire owner oneTime authenticated) := by
  unfold RegistrationNativePlatformSecretWordFinish.phase
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun result => prepared_keeps expected setup.source wire.frameWrite owner result)

/-- Every actual corrected finish outcome retains its captured public prekey. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (present : result ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    result.1.2.prekeyPublic = owner.prekeyPublic := by
  have valid : Sound owner.prekeyPublic owner := rfl
  simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind] at present
  cases current : owner.phase <;> simp only [current] at present
  all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at present; cases present; exact valid }
  case initSent pending oneTime =>
    cases stopped : pending.aborted_state with
    | fail error | div =>
      simp only [stopped, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
      cases present
      exact valid
    | ok aborted =>
      simp only [stopped] at present
      apply (bind_keeps owner.prekeyPublic _ _ (phase_keeps owner.prekeyPublic (.aborted aborted)) (fun _ => ?_)) owner env result valid present
      apply bind_keeps owner.prekeyPublic _ _ (lift_keeps owner.prekeyPublic _)
      intro authenticated
      cases authenticated with
      | fail error | div =>
        rw [seqRight_eq_bind]
        exact bind_keeps owner.prekeyPublic _ _ (abort_keeps owner.prekeyPublic _ owner) (fun _ => pure_keeps owner.prekeyPublic _)
      | ok selected => cases selected with
        | Err error =>
          rw [seqRight_eq_bind]
          exact bind_keeps owner.prekeyPublic _ _ (abort_keeps owner.prekeyPublic _ owner) (fun _ => pure_keeps owner.prekeyPublic _)
        | Ok accepted => exact agreement_keeps owner.prekeyPublic setup wire owner oneTime accepted

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyFinish.finish
