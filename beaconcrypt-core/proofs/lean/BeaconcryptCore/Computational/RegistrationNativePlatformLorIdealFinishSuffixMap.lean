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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordMessage (BeaconReady zero)
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
variable {NativePrivate WordPrivate : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate)
    (effects : ∀ query before, Prod.map id frame <$>
      (simulateQ symbolic (RegistrationNativeSecretWordInterface.effect query)).run before =
      (simulateQ native (RegistrationBeaconReferenceCompiler.effect query)).run (frame before))

include effects in
private theorem effects_program {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (simulateQ RegistrationNativeSecretWordInterface.effect work)).run before =
      (simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run (frame before) := by
  simp only [←QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (symbolic ∘ₛ RegistrationNativeSecretWordInterface.effect) (native ∘ₛ RegistrationBeaconReferenceCompiler.effect) frame effects work before

include effects in
/-- The chosen arbitrary material retains assigned-ID effects and all failures under the projected private-state relation. -/
theorem chosen_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (owner current : SelectedOwner source) (ready : BeaconReady) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationNativeSecretWordInterface.effect owner
        (ready.eval zero) choice).run current).run env)).run before =
      (simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationBeaconReferenceCompiler.effect owner
        (ready.eval candidate) choice).run current).run env)).run (frame before) := by
  change Prod.map id frame <$>
    (simulateQ symbolic (simulateQ RegistrationNativeSecretWordInterface.effect
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner (ready.eval candidate) choice).run current).run env))).run before = _
  rw [effects_program native symbolic frame effects]
  rfl

include effects in
/-- An abort retains the actual reached owner, environment and projected private poststate. -/
theorem abort_source (owner current : SelectedOwner source) (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationNativeSecretWordInterface.effect owner).run current).run env)).run before =
      (simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner).run current).run env)).run (frame before) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort,StateT.run_lift,bind_pure_comp,StateT.run_map,simulateQ_map,Functor.map_map]
  rw [←effects]
  simp only [Functor.map_map,Prod.map_def,id_eq]

variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (demand : ∀ reference before, Prod.map id frame <$>
      (simulateQ symbolic (RegistrationNativeSecretWordInterface.demand reference)).run before =
      (simulateQ native (RegistrationNativePlatformBeaconMaterialInterpreter.demand
        (RegistrationNativeSecretWordMessage.eval candidate reference))).run (frame before))

include effects demand in
/-- The material demand and every hidden, known or absent reply retain their same projected persistent continuation. -/
theorem complete_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (((RegistrationNativePlatformSecretWordFinish.complete crypto writer owner ready).run current).run env)).run before =
      (simulateQ native (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner (ready.eval candidate)).run current).run env)).run (frame before) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,RegistrationNativePlatformSecretWordFinish.complete,
    StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,simulateQ_bind,BeaconReady.eval,map_bind]
  rw [←demand,bind_map_left]
  apply bind_congr
  rintro ⟨choice,after⟩
  dsimp only [Prod.map,id]
  cases choice with
  | none =>
    simp only [seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure,map_bind]
    rw [←abort_source native symbolic frame effects owner current env after,bind_map_left]
    simp only [map_pure,Prod.map_def,id_eq]
  | some choice => exact chosen_source native symbolic frame effects crypto writer candidate owner current ready choice env after

include effects demand in
/-- The full post-preparation suffix preserves its original absence, error and divergence branches. -/
theorem afterPrepared_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (prepared : RustM (Option BeaconReady)) (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ symbolic (((RegistrationNativePlatformSecretWordFinish.afterPrepared crypto writer owner prepared).run current).run env)).run before =
      (simulateQ native (((RegistrationNativePlatformBeaconContinuation.afterPrepared crypto writer owner
        (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env)).run (frame before) := by
  cases prepared with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordBeaconRoot.restore,RegistrationNativePlatformBeaconContinuation.afterPrepared,
      RegistrationNativePlatformSecretWordFinish.afterPrepared,seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure,map_bind]
    rw [←abort_source native symbolic frame effects owner current env before,bind_map_left]
    simp only [map_pure,Prod.map_def,id_eq]
  | ok optional => cases optional with
    | none =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore,Option.map_none,RegistrationNativePlatformBeaconContinuation.afterPrepared,
        RegistrationNativePlatformSecretWordFinish.afterPrepared,seqRight_eq_bind,StateT.run_bind,StateT.run_pure,simulateQ_bind,simulateQ_pure,map_bind]
      rw [←abort_source native symbolic frame effects owner current env before,bind_map_left]
      simp only [map_pure,Prod.map_def,id_eq]
    | some ready =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore,Option.map_some,RegistrationNativePlatformBeaconContinuation.afterPrepared,
        RegistrationNativePlatformSecretWordFinish.afterPrepared]
      exact complete_source native symbolic frame effects candidate demand crypto writer owner current ready env before

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.chosen_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffixMap.afterPrepared_source
