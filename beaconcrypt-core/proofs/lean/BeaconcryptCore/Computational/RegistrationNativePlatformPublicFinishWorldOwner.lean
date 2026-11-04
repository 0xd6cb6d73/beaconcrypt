-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
/-! The actual corrected scalar-free public finish updates only owner phase. Its physical World owner index survives authentication, agreement, material demand, assigned-ID installation and every failure; the ordered roster is retained beside the same platform state. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι κ KemSK Auxiliary Value Next : Type} {base : OracleSpec ι} {target : OracleSpec κ}
variable {source : RegistrationNativeMldsa.Source}
private abbrev OM (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec κ) (Value : Type) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp target)) Value

def Sound (expected : Nat) (owner : SelectedOwner source) : Prop :=
  owner.worldOwner = expected

private def Keeps (expected : Nat) (work : OM source Auxiliary target Value) : Prop :=
  ∀ owner env result, Sound expected owner → result ∈ support ((work.run owner).run env) → Sound expected result.1.2

private theorem pure_keeps (expected : Nat) (value : Value) :
    Keeps expected (pure value : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem bind_keeps (expected : Nat) (work : OM source Auxiliary target Value)
    (next : Value → OM source Auxiliary target Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owner env result prior present
  simp only [StateT.run_bind, mem_support_bind_iff] at present
  obtain ⟨middle, called, continued⟩ := present
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle prior called) continued

private theorem lift_keeps (expected : Nat) (work : StateT (EnvState Auxiliary) (OracleComp target) Value) :
    Keeps expected (StateT.lift work : OM source Auxiliary target Value) := by
  intro owner env result prior present
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at present
  obtain ⟨middle, _called, returned⟩ := present
  cases returned
  exact prior

private theorem phase_keeps (expected : Nat) (phase : RegistrationNativeBeaconFrontend.Phase)
    :
    Keeps expected ((modify fun (owner : SelectedOwner source) => {owner with phase}) : OM source Auxiliary target Unit) := by
  intro owner env result prior present
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem abort_keeps (expected : Nat)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target)) (owner : SelectedOwner source) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.abort environment owner) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.abort
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private theorem after_keeps (expected : Nat)
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

private theorem material_program_keeps (expected : Nat)
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

private theorem chosen_keeps (expected : Nat)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer environment owner ready choice) := by
  intro current env result prior present
  exact material_program_keeps expected crypto writer owner ready choice current env result prior
    (RegistrationNativePublicSourceSupport.simulate_support environment _ result present)

private theorem complete_keeps (expected : Nat)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp target))
    (demand : RegistrationNativeRelatedFamily.Message → OracleComp target (Option (RegistrationNativePairedChoice.Choice n)))
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    Keeps (Auxiliary := Auxiliary) expected (RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer environment demand owner ready) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.complete
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro selected
  cases selected with
  | none =>
    rw [seqRight_eq_bind]
    exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
  | some choice => exact chosen_keeps expected crypto writer environment owner ready choice

private theorem prepared_keeps (expected : Nat)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    Keeps (Auxiliary := Auxiliary) expected
      (RegistrationNativePlatformBeaconContinuation.afterPrepared (n := n) (KemSK := KemSK) crypto writer owner result) := by
  unfold RegistrationNativePlatformBeaconContinuation.afterPrepared
  cases result with
  | fail error | div =>
    rw [seqRight_eq_bind]
    exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
  | ok selected => cases selected with
    | none =>
      rw [seqRight_eq_bind]
      exact bind_keeps expected _ _ (abort_keeps expected _ owner) (fun _ => pure_keeps expected _)
    | some ready => exact complete_keeps expected crypto writer _ _ owner ready

private theorem agreement_keeps (expected : Nat) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    Keeps (Auxiliary := RegistrationServerRoleBackend.State) expected (RegistrationNativePlatformBeaconPhase.phase (n := n) setup wire owner oneTime authenticated) := by
  unfold RegistrationNativePlatformBeaconPhase.phase
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun result => prepared_keeps expected setup.source wire.frameWrite owner result)

/-- Every literal corrected public finish outcome retains the captured physical World owner index. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState RegistrationServerRoleBackend.State)
    (present : result ∈ support (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    result.1.2.worldOwner = owner.worldOwner := by
  have valid : Sound owner.worldOwner owner := rfl
  simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind] at present
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
      apply (bind_keeps owner.worldOwner _ _ (phase_keeps owner.worldOwner (.aborted aborted)) (fun _ => ?_)) owner env result valid present
      apply bind_keeps owner.worldOwner _ _ (lift_keeps owner.worldOwner _)
      intro authenticated
      cases authenticated with
      | fail error | div =>
        rw [seqRight_eq_bind]
        exact bind_keeps owner.worldOwner _ _ (abort_keeps owner.worldOwner _ owner) (fun _ => pure_keeps owner.worldOwner _)
      | ok selected => cases selected with
        | Err error =>
          rw [seqRight_eq_bind]
          exact bind_keeps owner.worldOwner _ _ (abort_keeps owner.worldOwner _ owner) (fun _ => pure_keeps owner.worldOwner _)
        | Ok accepted => exact agreement_keeps owner.worldOwner setup wire owner oneTime accepted

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _

/-- The complete actual selected/ordinary public finish wrapper retains the ordered physical-owner roster beside P. -/
theorem finish_keys (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) {Platform : Type}
    (owners : List (RegistrationNativePublicOwners.Owner source))
    (env : EnvState RegistrationServerRoleBackend.State) (previous : Platform)
    (result : ((RustM (Option Pqxdh.Bytes) × List (RegistrationNativePublicOwners.Owner source)) × EnvState RegistrationServerRoleBackend.State) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformPublicFrontend.finish (n := n) (Platform := Platform) setup wire source index packet).run owners).run env).run previous)) :
    result.1.1.2.map (fun owner => owner.view.worldOwner) = owners.map (fun owner => owner.view.worldOwner) := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run] at supported
  cases found : owners[index]? with
  | none =>
    simp only [found, pure_apply, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some owner =>
    simp only [found, map_apply, support_map] at supported
    obtain ⟨middle, reached, equal⟩ := supported
    have original : middle.1 ∈ support (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run env) := by
      have called : middle.1 ∈ support (match owner.scalar with
          | none => ((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run env
          | some scalar => simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
              (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run env)) := by
        apply OracleComp.support_simulateQ_run'_subset
          (RegistrationNativePlatformPublicFrontend.localHandler (n := n) (KemSK := KemSK) (Platform := Platform) false) _ previous
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst reached
      cases own : owner.scalar with
      | none => simpa only [own] using called
      | some scalar =>
        simp only [own] at called
        exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
    have kept := finish setup wire packet owner.view env middle.1 original
    cases equal
    dsimp only [Prod.map] at ⊢
    rw [List.map_set]
    change (owners.map (fun owner => owner.view.worldOwner)).set index middle.1.1.2.worldOwner = _
    rw [kept]
    have present : (owners.map (fun owner => owner.view.worldOwner))[index]? = some owner.view.worldOwner := by
      simp only [List.getElem?_map, found, Option.map_some]
    obtain ⟨below, current⟩ := List.getElem?_eq_some_iff.mp present
    rw [← current]
    exact List.set_getElem_self below

variable {E Platform : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The literal complete public dispatcher retains its physical-owner order and therefore every retained index/length correspondence. -/
theorem callback_keys (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformPublicFrontend.State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.finish index packet))).run before)) :
    result.2.1.beacons.map (fun owner => owner.view.worldOwner) = before.1.beacons.map (fun owner => owner.view.worldOwner) := by
  simp only [RegistrationNativePlatformPublicFrontend.handler, RegistrationNativePlatformPublicFrontend.executeLocal, StateT.run] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePlatformPublicFrontend.beacon, StateT.run, support_map] at original
  obtain ⟨reached, called, equal⟩ := original
  cases equal
  exact finish_keys setup wire index packet before.1.beacons before.1.environment before.2 reached called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.finish_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.finish_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.callback_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner.callback_keys
