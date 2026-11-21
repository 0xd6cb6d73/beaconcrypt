-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence
/-! The literal corrected Word finish changes only owner phase. Retained KEM handles and public keys survive all authentication, agreement, material, record and install outcomes; roster transport preserves the same ordered metadata. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι κ KemSK Auxiliary Value Next : Type} {base : OracleSpec ι} {target : OracleSpec κ}
variable {source : RegistrationNativeMldsa.Source}
private abbrev OM (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec κ) (Value : Type) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp target)) Value

def Sound (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (owner : SelectedOwner source) : Prop :=
  (owner.kemHandle, owner.kemPublic) = expected

private def Keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (work : OM source Auxiliary target Value) : Prop :=
  ∀ owner env result, Sound expected owner → result ∈ support ((work.run owner).run env) → Sound expected result.1.2

private theorem pure_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (value : Value) :
    Keeps expected (pure value : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem bind_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (work : OM source Auxiliary target Value)
    (next : Value → OM source Auxiliary target Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owner env result prior present
  simp only [StateT.run_bind, mem_support_bind_iff] at present
  obtain ⟨middle, called, continued⟩ := present
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle prior called) continued

private theorem lift_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (work : StateT (EnvState Auxiliary) (OracleComp target) Value) :
    Keeps expected (StateT.lift work : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at present
  obtain ⟨middle, _called, returned⟩ := present
  cases returned
  exact prior

private theorem phase_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (phase : RegistrationNativeBeaconFrontend.Phase)
    :
    Keeps expected ((modify fun (owner : SelectedOwner source) => {owner with phase}) : OM source Auxiliary target Unit) := by
  intro owner env result prior present
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem abort_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target)) (owner : SelectedOwner source) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.abort
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private theorem after_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
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

private theorem material_program_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
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

private theorem chosen_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer environment owner ready choice) := by
  intro current env result prior present
  exact material_program_keeps expected crypto writer owner ready choice current env result prior
    (RegistrationNativePublicSourceSupport.simulate_support environment _ result present)

private theorem complete_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
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

private theorem prepared_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey)
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

private theorem agreement_keeps (expected : Nat × PqxdhKemIndCca.MlKem768PublicKey) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformSecretWordFinish.phase (n := n) setup wire owner oneTime authenticated) := by
  unfold RegistrationNativePlatformSecretWordFinish.phase
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun result => prepared_keeps expected setup.source wire.frameWrite owner result)

/-- Every literal corrected finish outcome retains the captured owner KEM handle and public key. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (present : result ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    (result.1.2.kemHandle, result.1.2.kemPublic) = (owner.kemHandle, owner.kemPublic) := by
  have valid : Sound (owner.kemHandle, owner.kemPublic) owner := rfl
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
      apply (bind_keeps (owner.kemHandle, owner.kemPublic) _ _ (phase_keeps (owner.kemHandle, owner.kemPublic) (.aborted aborted)) (fun _ => ?_)) owner env result valid present
      apply bind_keeps (owner.kemHandle, owner.kemPublic) _ _ (lift_keeps (owner.kemHandle, owner.kemPublic) _)
      intro authenticated
      cases authenticated with
      | fail error | div =>
        rw [seqRight_eq_bind]
        exact bind_keeps (owner.kemHandle, owner.kemPublic) _ _ (abort_keeps (owner.kemHandle, owner.kemPublic) _ owner) (fun _ => pure_keeps (owner.kemHandle, owner.kemPublic) _)
      | ok selected => cases selected with
        | Err error =>
          rw [seqRight_eq_bind]
          exact bind_keeps (owner.kemHandle, owner.kemPublic) _ _ (abort_keeps (owner.kemHandle, owner.kemPublic) _ owner) (fun _ => pure_keeps (owner.kemHandle, owner.kemPublic) _)
        | Ok accepted => exact agreement_keeps (owner.kemHandle, owner.kemPublic) setup wire owner oneTime accepted

/-- The literal common-platform incoming wrapper retains every roster handle and public key, with selected and ordinary preparation both covered. -/
theorem finish_keys (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    {Platform : Type} (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run before)) :
    result.2.1.beacons.map RegistrationNativeSecretWordTargetPublication.key = before.1.beacons.map RegistrationNativeSecretWordTargetPublication.key := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run] at supported
  cases found : before.1.beacons[index]? with
  | none =>
    simp only [found, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some owner =>
    simp only [found, support_map] at supported
    obtain ⟨middle, reached, equal⟩ := supported
    have localSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
    have original : middle ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) (KemSK := KemSK) setup wire source packet).run owner.view).run before.1.environment) := by
      cases own : owner.scalar with
      | none => simpa only [own, StateT.run] using localSupport
      | some scalar =>
        simp only [own] at localSupport
        exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ localSupport
    have kept := finish setup wire packet owner.view before.1.environment middle original
    cases equal
    rw [List.map_set]
    change (before.1.beacons.map RegistrationNativeSecretWordTargetPublication.key).set index (middle.1.2.kemHandle, middle.1.2.kemPublic) = _
    rw [kept]
    have present : (before.1.beacons.map RegistrationNativeSecretWordTargetPublication.key)[index]? = some (RegistrationNativeSecretWordTargetPublication.key owner) := by
      simp only [List.getElem?_map, found, Option.map_some]
    obtain ⟨below, current⟩ := List.getElem?_eq_some_iff.mp present
    change (before.1.beacons.map RegistrationNativeSecretWordTargetPublication.key).set index (RegistrationNativeSecretWordTargetPublication.key owner) = _
    rw [← current]
    exact List.set_getElem_self below

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish.finish_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish.finish_keys
