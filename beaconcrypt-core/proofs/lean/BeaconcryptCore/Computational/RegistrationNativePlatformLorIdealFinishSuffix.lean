-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
/-! The corrected Beacon material continuation is natural in any lawful persistent interpretation of its individual effect and evaluated-demand leaves. Hidden, known and absent material choices remain arbitrary, with actual assigned-ID installation, source first-record failures, owner and complete environment retained. Agreement, authentication and the full finish dispatcher are separate source obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordMessage (BeaconReady zero)
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) m)
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (effects : ∀ query, simulateQ native (RegistrationBeaconReferenceCompiler.effect query) =
      simulateQ symbolic (RegistrationNativeSecretWordInterface.effect query))

include effects in
private theorem effects_program {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.effect work) =
      simulateQ symbolic (simulateQ RegistrationNativeSecretWordInterface.effect work) := by
  rw [←QueryImpl.simulateQ_compose,←QueryImpl.simulateQ_compose]
  have same : native ∘ₛ RegistrationBeaconReferenceCompiler.effect = symbolic ∘ₛ RegistrationNativeSecretWordInterface.effect := by
    funext query
    exact effects query
  rw [same]

include effects in
/-- The same chosen material program retains every assigned-ID and failure effect under arbitrary persistent effect interpreters. -/
theorem chosen_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (owner current : SelectedOwner source) (ready : BeaconReady) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState Auxiliary) :
    simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationBeaconReferenceCompiler.effect owner
      (ready.eval candidate) choice).run current).run env) =
    simulateQ symbolic (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationNativeSecretWordInterface.effect owner
      (ready.eval zero) choice).run current).run env) := by
  change simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.effect
    (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner (ready.eval candidate) choice).run current).run env)) = _
  rw [effects_program native symbolic effects]
  rfl

include effects in
/-- An abort retains the actual reached owner/environment and the same public World transition. -/
theorem abort_source (owner current : SelectedOwner source) (env : EnvState Auxiliary) :
    simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner).run current).run env) =
    simulateQ symbolic (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort,StateT.run_lift,bind_pure_comp,StateT.run_map,simulateQ_map]
  rw [effects]

variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (demand : ∀ reference, simulateQ native
      (RegistrationNativePlatformBeaconMaterialInterpreter.demand (RegistrationNativeSecretWordMessage.eval candidate reference)) =
      simulateQ symbolic (RegistrationNativeSecretWordInterface.demand reference))

include effects demand in
/-- Evaluating the one demanded material address preserves every actual continuation, including hidden, known and failed replies. -/
theorem complete_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (env : EnvState Auxiliary) :
    simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
      RegistrationNativePlatformBeaconMaterialInterpreter.demand owner (ready.eval candidate)).run current).run env) =
    simulateQ symbolic (((RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,RegistrationNativePlatformSecretWordFinish.complete,
    StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,simulateQ_bind,BeaconReady.eval]
  rw [demand]
  apply bind_congr
  intro choice
  cases choice with
  | none =>
    simp only [seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure]
    rw [abort_source native symbolic effects owner current env]
  | some choice => exact chosen_source native symbolic effects crypto writer candidate owner current ready choice env

include effects demand in
/-- The whole post-preparation suffix retains the original error/divergence/absence branches and corrected assigned-ID completion under the same individual leaf relations. -/
theorem afterPrepared_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (prepared : RustM (Option BeaconReady)) (env : EnvState Auxiliary) :
    simulateQ native (((RegistrationNativePlatformBeaconContinuation.afterPrepared crypto writer owner
      (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env) =
    simulateQ symbolic (((RegistrationNativePlatformSecretWordFinish.afterPrepared crypto writer owner prepared).run current).run env) := by
  cases prepared with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordBeaconRoot.restore,RegistrationNativePlatformBeaconContinuation.afterPrepared,
      RegistrationNativePlatformSecretWordFinish.afterPrepared,seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure]
    rw [abort_source native symbolic effects owner current env]
  | ok selected => cases selected with
    | none =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore,Option.map_none,RegistrationNativePlatformBeaconContinuation.afterPrepared,
        RegistrationNativePlatformSecretWordFinish.afterPrepared,seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure]
      rw [abort_source native symbolic effects owner current env]
    | some ready =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore,Option.map_some,RegistrationNativePlatformBeaconContinuation.afterPrepared,
        RegistrationNativePlatformSecretWordFinish.afterPrepared]
      exact complete_source native symbolic effects candidate demand crypto writer owner current ready env

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.chosen_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix.afterPrepared_source
