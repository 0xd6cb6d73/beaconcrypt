-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsBeacon
/-! The candidate-independent corrected Word finish derives at most one material request from its literal authentication, ordered preparation and actual first-record/install source syntax. Every failed prefix and returned state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordInterface (effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordFrontendCapsLocal (IsDemand)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, IsDemand, isQueryBoundP_query_iff]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (effect (n := n) (KemSK := KemSK)) owner).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    effect, IsDemand, isQueryBoundP_query_iff]

private theorem chosen_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.chosen source writer (effect (n := n) (KemSK := KemSK)) owner ready choice).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := effect_free _

private theorem complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.complete (n := n) (KemSK := KemSK) source writer owner ready).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePlatformSecretWordFinish.complete, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, RegistrationNativeSecretWordInterface.demand]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [IsDemand], ?_⟩
  intro choice
  cases choice with
  | none =>
    simpa only [IsDemand, ite_true, Nat.sub_self, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      abort_free (n := n) (KemSK := KemSK) owner current before
  | some choice =>
    simpa only [IsDemand, ite_true, Nat.sub_self] using chosen_free source writer owner current (ready.eval RegistrationNativeSecretWordMessage.zero) choice before

theorem afterPrepared_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (result : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.afterPrepared (n := n) (KemSK := KemSK) source writer owner result).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  cases result with
  | fail error | div =>
    simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      (abort_free (n := n) (KemSK := KemSK) owner current before).mono (Nat.zero_le 1)
  | ok result => cases result with
    | none =>
      simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
        StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
        (abort_free (n := n) (KemSK := KemSK) owner current before).mono (Nat.zero_le 1)
    | some ready => exact complete_bound source writer owner current ready before

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (RegistrationNativeSecretWordFrontendCapsBeacon.collect_free setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
    simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    simp [RegistrationNativeSecretWordInterface.prepare, IsDemand, isQueryBoundP_query_iff]

theorem phase_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.phase (n := n) setup wire owner oneTime authenticated).run current).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 1) (agreement_free setup owner oneTime authenticated before)
  intro result _
  exact afterPrepared_bound setup.source wire.frameWrite owner current result.1 result.2

/-- Every corrected finish path makes at most one material request, including failed authentication, missing preparation, rejected material and failed record installation. -/
theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved, StateT.run_pure]; trivial
    | ok aborted =>
      simp only [moved, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left]
      apply isQueryBoundP_bind (n := 0) (m := 1) (effect_free _)
      intro authenticated _
      cases authenticated with
      | fail error | div =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
          bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
          (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before).mono (Nat.zero_le 1)
      | ok result => cases result with
        | Err error =>
          simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
            bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
            (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before).mono (Nat.zero_le 1)
        | Ok accepted => exact phase_bound setup wire owner {owner with phase := .aborted aborted} oneTime accepted before
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.afterPrepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.afterPrepared_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.phase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.phase_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishCaps.finish_bound
