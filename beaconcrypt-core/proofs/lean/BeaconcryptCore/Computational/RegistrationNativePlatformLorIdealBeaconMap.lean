-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap
/-! The literal corrected Beacon finish is natural in distinct persistent interpretations of its individual native, prepare, effect and material-demand leaves. All authentication errors, divergence, assigned-ID continuation and refused material branches remain explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK NativePrivate WordPrivate Auxiliary : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate)
    (leaves : RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate native symbolic frame)
    (demand : ∀ reference before,Prod.map id frame <$>
      (simulateQ symbolic (RegistrationNativeSecretWordInterface.demand reference)).run before =
      (simulateQ native (RegistrationNativePlatformBeaconMaterialInterpreter.demand
        (RegistrationNativeSecretWordMessage.eval candidate reference))).run (frame before))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable {source : RegistrationNativeMldsa.Source}
include leaves
private theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : WordPrivate) :
    Prod.map id frame <$> (simulateQ symbolic (RegistrationNativeSecretWordInterface.effect query)).run before =
      (simulateQ native (RegistrationBeaconReferenceCompiler.effect query)).run (frame before) := by
  have leaf := leaves.native_leaf (.inr (.inl (.inr (.inr query)))) before
  simpa only [QueryImpl.compose,RegistrationBeaconReferenceCompiler.effect,RegistrationNativeSecretWordInterface.effect,
    RegistrationNativeSecretWordServerSource.realize,RegistrationNativeSecretWordInterface.common,simulateQ_spec_query] using leaf
include leaves demand

theorem afterPrepared_source (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (prepared : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady))
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (((RegistrationNativePlatformSecretWordFinish.afterPrepared setup.source wire.frameWrite owner prepared).run current).run env)).run before =
      (simulateQ native (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner
        (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env)).run (frame before) :=
  RegistrationNativePlatformLorIdealFinishSuffixMap.afterPrepared_source native symbolic frame
    (effects candidate native symbolic frame leaves) candidate demand setup.source wire.frameWrite owner current prepared env before

theorem phase_source (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic
        (((RegistrationNativePlatformSecretWordFinish.phase setup wire owner oneTime authenticated).run current).run env)).run before =
      (simulateQ native
        (((RegistrationNativePlatformBeaconPhase.phase setup wire owner oneTime authenticated).run current).run env)).run (frame before) := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase,RegistrationNativePlatformBeaconPhase.phase,
    StateT.run_bind,StateT.run_lift,bind_pure_comp,simulateQ_bind,bind_map_left,map_bind]
  have sourceEq := RegistrationNativePlatformLorIdealBeaconCore.agreement_source candidate native symbolic frame leaves setup
    owner oneTime authenticated env before
  rw [←sourceEq,bind_map_left]
  apply bind_congr
  rintro ⟨⟨prepared,envAfter⟩,after⟩
  simp only [Prod.map_apply,id_eq]
  exact afterPrepared_source candidate native symbolic frame leaves demand setup wire
    owner current prepared envAfter after
omit demand in
private theorem effects_source {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : WordPrivate) :
    Prod.map id frame <$> (simulateQ symbolic
      (simulateQ RegistrationNativeSecretWordInterface.effect work)).run before =
      (simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run (frame before) := by
  simp only [←QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ frame (effects candidate native symbolic frame leaves) work before

theorem finish_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (packet : Option registration.ResponsePacket)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic
        (((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner).run env)).run before =
      (simulateQ native
        (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)).run (frame before) := by
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformSecretWordFinish.finish,RegistrationNativePlatformBeaconReferenceFinish.finish,
      StateT.run_bind,StateT.run_get,pure_bind,phase,StateT.run_pure,simulateQ_pure,map_pure]
    rfl
  | initSent pending oneTime =>
    simp only [RegistrationNativePlatformSecretWordFinish.finish,RegistrationNativePlatformBeaconReferenceFinish.finish,
      StateT.run_bind,StateT.run_get,pure_bind,phase]
    cases moved : pending.aborted_state with
    | fail error | div =>
      simp only [StateT.run_pure,simulateQ_pure,map_pure]
      rfl
    | ok aborted =>
      simp only [StateT.run_modify,pure_bind,StateT.run_bind,StateT.run_lift,
        bind_pure_comp,simulateQ_bind,map_bind,bind_map_left]
      have authEq := effects_source candidate native symbolic frame leaves
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))) before
      simp only [StateT.run] at authEq ⊢
      refine Eq.trans ?_ (congrArg (fun work => work >>= _) authEq)
      simp only [bind_map_left]
      apply bind_congr
      rintro ⟨authenticated,after⟩
      simp only [Prod.map_apply,id_eq]
      cases authenticated with
      | fail error =>
        exact afterPrepared_source candidate native symbolic frame leaves demand setup wire
          owner {owner with phase := .aborted aborted} (.fail error) env after
      | div =>
        exact afterPrepared_source candidate native symbolic frame leaves demand setup wire
          owner {owner with phase := .aborted aborted} .div env after
      | ok result => cases result with
        | Err error =>
          exact afterPrepared_source candidate native symbolic frame leaves demand setup wire
            owner {owner with phase := .aborted aborted} (.ok none) env after
        | Ok accepted =>
          exact phase_source candidate native symbolic frame leaves demand setup wire
            owner {owner with phase := .aborted aborted} oneTime accepted env after

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.afterPrepared_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.phase_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap.finish_source
