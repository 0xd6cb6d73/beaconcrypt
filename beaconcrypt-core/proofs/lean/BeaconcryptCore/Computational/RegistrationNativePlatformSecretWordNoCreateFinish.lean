-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon
/-! Corrected symbolic finish never creates a private KEM row. Mandatory authentication, the unchanged indexed collector and preparation, actual assigned-ID first record and install retain every source failure and prior environment marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordInterface (effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordTargetNoCreateLocal (IsCreate)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsCreate, isQueryBoundP_query_iff]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (effect (n := n) (KemSK := KemSK)) owner).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    effect, IsCreate, isQueryBoundP_query_iff]

private theorem chosen_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.chosen source writer (effect (n := n) (KemSK := KemSK)) owner ready choice).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := effect_free _

private theorem complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.complete (n := n) (KemSK := KemSK) source writer owner ready).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.complete, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, RegistrationNativeSecretWordInterface.demand]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [IsCreate], ?_⟩
  intro choice
  cases choice with
  | none =>
    simpa only [IsCreate, ite_false, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      abort_free (n := n) (KemSK := KemSK) owner current before
  | some choice =>
    simpa only [IsCreate, ite_false] using chosen_free source writer owner current (ready.eval RegistrationNativeSecretWordMessage.zero) choice before

theorem afterPrepared_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (result : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.afterPrepared (n := n) (KemSK := KemSK) source writer owner result).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  cases result with
  | fail error | div =>
    simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      (abort_free (n := n) (KemSK := KemSK) owner current before).mono (Nat.zero_le 0)
  | ok result => cases result with
    | none =>
      simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
        StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
        (abort_free (n := n) (KemSK := KemSK) owner current before).mono (Nat.zero_le 0)
    | some ready => exact complete_bound source writer owner current ready before

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (RegistrationNativeSecretWordTargetNoCreateBeacon.collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
    simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    simp [RegistrationNativeSecretWordInterface.prepare, IsCreate, isQueryBoundP_query_iff]

theorem phase_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.phase (n := n) setup wire owner oneTime authenticated).run current).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0) (agreement_free setup owner oneTime authenticated before)
  intro result _
  exact afterPrepared_bound setup.source wire.frameWrite owner current result.1 result.2

/-- Every literal corrected finish branch has zero private KEM births through authentication, preparation and actual assigned-ID completion. -/
theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved, StateT.run_pure]; trivial
    | ok aborted =>
      simp only [moved, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left]
      apply isQueryBoundP_bind (n := 0) (m := 0) (effect_free _)
      intro authenticated _
      cases authenticated with
      | fail error | div =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
          bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
          (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before).mono (Nat.zero_le 0)
      | ok result => cases result with
        | Err error =>
          simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
            bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
            (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before).mono (Nat.zero_le 0)
        | Ok accepted => exact phase_bound setup wire owner {owner with phase := .aborted aborted} oneTime accepted before
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.afterPrepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.afterPrepared_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.phase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.phase_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish.finish_bound
