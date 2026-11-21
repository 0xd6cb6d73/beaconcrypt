-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconSafe
/-! The literal corrected assigned-ID Word finish cannot install the Server role. The actual source material program installs only Beacon peers, and every authentication, preparation, abort and record failure retains its original state and callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordInterface (effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
abbrev Install {n : Nat} {KemSK : Type} := LocalInstall (n := n) (KemSK := KemSK) .server
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (bounded : work.IsQueryBoundP (InstallEnv .server) 0) :
    (simulateQ (effect (KemSK := KemSK)) work).IsQueryBoundP (Install (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  by_cases installed : InstallEnv .server query <;>
    simp [effect, Install, LocalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, installed, isQueryBoundP_query_iff]

private theorem authentication_free (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    (simulateQ (effect (n := n) (KemSK := KemSK))
      (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) work)).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [QueryImpl.compose, RegistrationAuthenticationCompiler.callbacks, effect, Install, LocalInstall,
    RegistrationNativeSecretWordAtomInstallCaps.Install, InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem env_server_free (choice : RegistrationNativePairedChoice.Choice n)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (allowed : work.AllQueriesSatisfy (RegistrationNativePairedProvenance.Effect .beacon choice)) :
    work.IsQueryBoundP (InstallEnv .server) 0 := by
  classical
  have rejected := (isQueryBoundP_zero_iff work (RegistrationNativePairedProvenance.Effect .beacon choice)).2 allowed
  apply rejected.of_imp
  intro query installed good
  cases query with
  | inl coin => cases installed
  | inr capability => cases capability <;> simp_all [InstallEnv, RegistrationNativePairedProvenance.Effect]

private theorem abort_free {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (effect (n := n) (KemSK := KemSK)) owner).run current).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    effect, Install, LocalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, InstallEnv, isQueryBoundP_query_iff]

private theorem chosen_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.chosen source writer (effect (n := n) (KemSK := KemSK)) owner ready choice).run current).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  apply effect_free
  exact env_server_free choice _
    (RegistrationNativePlatformPairedBeaconSafe.program_facts source writer owner current ready choice before).2

private theorem complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.complete (n := n) (KemSK := KemSK) source writer owner ready).run current).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.complete, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, RegistrationNativeSecretWordInterface.demand]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Install, LocalInstall], ?_⟩
  intro choice
  cases choice with
  | none =>
    simpa only [Install, LocalInstall, ite_false, Nat.sub_zero, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      abort_free (n := n) (KemSK := KemSK) owner current before
  | some choice =>
    simpa only [Install, LocalInstall, ite_false, Nat.sub_zero] using chosen_free source writer owner current (ready.eval RegistrationNativeSecretWordMessage.zero) choice before

theorem afterPrepared_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (result : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady)) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformSecretWordFinish.afterPrepared (n := n) (KemSK := KemSK) source writer owner result).run current).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  cases result with
  | fail error | div =>
    simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
      (abort_free (n := n) (KemSK := KemSK) owner current before)
  | ok result => cases result with
    | none =>
      simpa only [RegistrationNativePlatformSecretWordFinish.afterPrepared, seqRight_eq_bind,
        StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
        (abort_free (n := n) (KemSK := KemSK) owner current before)
    | some ready => exact complete_bound source writer owner current ready before

private theorem agreement_free (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.agreement (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (RegistrationNativeSecretWordAtomOwnerInstallPrefix.collect_free .server setup owner oneTime authenticated before)
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
    simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    simp [RegistrationNativeSecretWordInterface.prepare, LocalInstall, isQueryBoundP_query_iff]

theorem phase_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.phase (n := n) setup wire owner oneTime authenticated).run current).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0) (agreement_free setup owner oneTime authenticated before)
  intro result _
  exact afterPrepared_bound setup.source wire.frameWrite owner current result.1 result.2

/-- Every corrected finish path has no Server installation request, including failed authentication, missing preparation, rejected material and failed record installation. -/
theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run before).IsQueryBoundP
      (Install (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved, StateT.run_pure]; trivial
    | ok aborted =>
      simp only [moved, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left]
      apply isQueryBoundP_bind (n := 0) (m := 0) (authentication_free setup.source.crypto source.verify _)
      intro authenticated _
      cases authenticated with
      | fail error | div =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
          bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
          (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before)
      | ok result => cases result with
        | Err error =>
          simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
            bind_pure_comp, StateT.run_map, map_apply, isQueryBoundP_map_iff] using
            (abort_free (n := n) (KemSK := KemSK) owner {owner with phase := .aborted aborted} before)
        | Ok accepted => exact phase_bound setup wire owner {owner with phase := .aborted aborted} oneTime accepted before
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.afterPrepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.afterPrepared_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.phase_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.phase_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall.finish_bound
