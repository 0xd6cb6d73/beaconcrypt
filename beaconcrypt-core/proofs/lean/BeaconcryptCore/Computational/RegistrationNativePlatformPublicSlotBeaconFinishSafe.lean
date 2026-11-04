-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRoute
/-! The literal corrected response-authentication/agreement/first-open controller is paired-safe under both private scalar preparation routes. The original request tree, returned owner, journals and all failure replies are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordAtomOwnerInstallPrefix (NativeInstall)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev M (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (A : Type) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK))) A

def compile (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : M (n := n) (KemSK := KemSK) source Auxiliary A) (owner : SelectedOwner source) (env : EnvState Auxiliary) :=
  simulateQ (RegistrationNativePlatformPairedBeaconRoute.route setup scalar) ((work.run owner).run env)

def Safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : M (n := n) (KemSK := KemSK) source Auxiliary A) : Prop :=
  ∀ owner env, RegistrationNativePlatformPublicSlotKind.Safe (compile setup scalar work owner env)

private theorem pure_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) (value : A) :
    Safe setup scalar (pure value : M (n := n) (KemSK := KemSK) source Auxiliary A) := by
  intro owner env
  exact RegistrationNativePlatformPublicSlotKind.pure_safe _
private theorem bind_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : M (n := n) (KemSK := KemSK) source Auxiliary A) (next : A → M (n := n) (KemSK := KemSK) source Auxiliary B)
    (prior : Safe setup scalar work) (later : ∀ value, Safe setup scalar (next value)) : Safe setup scalar (work >>= next) := by
  intro owner env
  simp only [compile, StateT.run_bind, simulateQ_bind]
  exact RegistrationNativePlatformPublicSlotKind.bind_safe _ _ (prior owner env) (fun reached => later reached.1.1 reached.1.2 reached.2)

/-- Routing the actual material body retains its demand reply and every source state component exactly. -/
theorem complete_run (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (owner current : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    compile setup scalar
      (RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source writer effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready)
      current env =
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source writer
        (RegistrationNativePairedCompile.effects (n := n) (KemSK := KemSK))
        (RegistrationNativePlatformPublicSlotEffects.demand (n := n) (KemSK := KemSK)) owner ready).run current).run env) := by
  simp only [compile, RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind]
  rw [RegistrationNativePlatformPairedBeaconRoute.demand]
  apply bind_congr
  intro selected
  cases selected with
  | none =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind,
      StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map]
    rw [← QueryImpl.apply_compose, RegistrationNativePlatformPairedBeaconRoute.environment]
  | some choice =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.chosen, StateT.run,
      ← QueryImpl.simulateQ_compose, RegistrationNativePlatformPairedBeaconRoute.environment]

private theorem native_map_safe (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (observe : A → B) (safe : RegistrationNativePlatformPublicSlotKind.Safe work) : RegistrationNativePlatformPublicSlotKind.Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact RegistrationNativePlatformPublicSlotKind.bind_safe _ _ safe (fun _ => RegistrationNativePlatformPublicSlotKind.pure_safe _)
private theorem lift_state_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) A)
    (free : ∀ role env, (work.run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0) :
    Safe setup scalar (StateT.lift work : M (n := n) (KemSK := KemSK) source Auxiliary A) := by
  intro owner env
  simp only [compile, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map]
  apply native_map_safe
  exact RegistrationNativePlatformPublicSlotKind.free_safe _ (fun role => RegistrationNativePlatformPairedBeaconRoute.bound role setup scalar _ 0 (free role env))
private theorem lift_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n KemSK) A)
    (free : ∀ role, work.IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0) :
    Safe setup scalar (StateT.lift (StateT.lift work) : M (n := n) (KemSK := KemSK) source Auxiliary A) := by
  apply lift_state_safe setup scalar
  intro role env
  simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using free role
private theorem get_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    Safe setup scalar (get : M (n := n) (KemSK := KemSK) source Auxiliary (SelectedOwner source)) := by
  intro owner env
  exact RegistrationNativePlatformPublicSlotKind.pure_safe _
private theorem modify_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (change : SelectedOwner source → SelectedOwner source) :
    Safe setup scalar (modify change : M (n := n) (KemSK := KemSK) source Auxiliary Unit) := by
  intro owner env
  exact RegistrationNativePlatformPublicSlotKind.pure_safe _
private theorem abort_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) (owner : SelectedOwner source) :
    Safe setup scalar (RegistrationNativePlatformBeaconMaterialFrontend.abort (n := n) effect owner : M (n := n) (KemSK := KemSK) source Auxiliary Unit) := by
  unfold RegistrationNativePlatformBeaconMaterialFrontend.abort
  apply bind_safe setup scalar _ _ (lift_safe setup scalar _ ?_) (fun _ => pure_safe setup scalar _)
  intro role
  simp [effect, NativeInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
    RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]

private theorem complete_safe (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    Safe setup scalar (RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source writer effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready : M (n := n) (KemSK := KemSK) source Auxiliary (RustM (Option Pqxdh.Bytes))) := by
  intro current env
  rw [complete_run]
  exact RegistrationNativePlatformPublicSlotBeaconSafe.complete setup.source writer owner current ready env

private theorem authentication_free (role : PqxdhRecordLiftInterface.Role) (crypto : Pqxdh.Crypto)
    (verify : MldsaTranscriptAuth.Verify) (work : OracleComp RegistrationAuthenticationExecutor.Spec A) :
    (simulateQ (effect (n := n) (KemSK := KemSK))
      (simulateQ (RegistrationAuthenticationCompiler.callbacks crypto verify) work)).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [QueryImpl.compose, RegistrationAuthenticationCompiler.callbacks, effect,
    NativeInstall, RegistrationNativeSecretWordAtomInstallCaps.Install,
    RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem prepare_free (role : PqxdhRecordLiftInterface.Role)
    (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec A) :
    (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationBeaconReferenceCompiler.prepare, NativeInstall, isQueryBoundP_query_iff]

private theorem agreement_free (role : PqxdhRecordLiftInterface.Role) (setup : Setup base KemSK)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : EnvState Auxiliary) :
    ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup owner oneTime authenticated).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 := by
  simp only [RegistrationBeaconReferenceCompiler.agreement, StateT.run_bind]
  have collected : ((RegistrationBeaconReferenceCompiler.collect (n := n) setup owner oneTime authenticated).run env).IsQueryBoundP (NativeInstall (KemSK := KemSK) role) 0 :=
    (RegistrationNativeInstallFreePreparation.collect_free role setup owner oneTime authenticated env).of_imp (fun _ installed => installed)
  apply isQueryBoundP_bind (n := 0) (m := 0) collected
  intro result _
  cases result.1 with
  | none => trivial
  | some pending =>
    simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using
      prepare_free role (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending)

/-- The corrected post-agreement continuation uses its literal material demand on every successful preparation and remains safe on every abort. -/
theorem afterPrepared (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (owner : SelectedOwner source)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) :
    Safe setup scalar (RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source writer owner result : M (n := n) (KemSK := KemSK) source Auxiliary (RustM (Option Pqxdh.Bytes))) := by
  cases result with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind]
    exact bind_safe setup scalar _ _ (abort_safe setup scalar owner) (fun _ => pure_safe setup scalar _)
  | ok result => cases result with
    | none =>
      simp only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind]
      exact bind_safe setup scalar _ _ (abort_safe setup scalar owner) (fun _ => pure_safe setup scalar _)
    | some ready => exact complete_safe setup scalar writer owner ready

/-- The actual incoming agreement prefix has no install; its actual returned Ready then supplies the same demand checked by the suffix. -/
theorem phase (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (wire : RegistrationNativeWire.Wire) (owner : SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Safe setup scalar (RegistrationNativePlatformBeaconPhase.phase (n := n) setup wire owner oneTime authenticated) := by
  unfold RegistrationNativePlatformBeaconPhase.phase
  exact bind_safe setup scalar _ _ (lift_state_safe setup scalar _ (fun role env => agreement_free role setup owner oneTime authenticated env))
    (fun result => afterPrepared setup scalar wire.frameWrite owner result)

/-- The literal corrected Beacon response/first-record source controller is paired-safe through every mutable owner and failure branch. -/
theorem finish (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket) :
    Safe setup scalar (RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet) := by
  unfold RegistrationNativePlatformBeaconReferenceFinish.finish
  apply bind_safe setup scalar _ _ (get_safe setup scalar)
  intro owner
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted previous =>
    exact pure_safe setup scalar _
  | initSent pending oneTime =>
    dsimp only
    cases moved : pending.aborted_state with
    | fail error | div => exact pure_safe setup scalar _
    | ok aborted =>
      apply bind_safe setup scalar _ _ (modify_safe setup scalar _)
      intro _
      apply bind_safe setup scalar _ _ (lift_safe setup scalar _ (fun role => authentication_free role setup.source.crypto source.verify _))
      intro authenticated
      cases authenticated with
      | fail error | div =>
        rw [seqRight_eq_bind]
        exact bind_safe setup scalar _ _ (abort_safe setup scalar owner) (fun _ => pure_safe setup scalar _)
      | ok result => cases result with
        | Err previous =>
          rw [seqRight_eq_bind]
          exact bind_safe setup scalar _ _ (abort_safe setup scalar owner) (fun _ => pure_safe setup scalar _)
        | Ok accepted => exact phase setup scalar wire owner oneTime accepted
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.complete_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.complete_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.afterPrepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.afterPrepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBeaconFinishSafe.finish
