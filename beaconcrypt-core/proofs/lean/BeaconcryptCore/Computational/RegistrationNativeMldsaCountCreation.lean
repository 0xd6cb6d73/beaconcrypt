-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative

/-! The actual reified owner-creation controller satisfies free ML count normalization. Its supplied-generation suffix never reads the private record-kind instrumentation; both the narrow counting view and the original source Main view therefore apply, including every failed pin/KEM/owner-allocation prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaMainView (project)
open RegistrationNativeMldsaCountRules (Correct)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : Source}

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commuting : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : RegistrationNativeKemCounterIndependence.Stable first work)
    (right : RegistrationNativeKemCounterIndependence.Stable second work) :
    RegistrationNativeKemCounterIndependence.Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commuting] at following
  exact initial.trans following

/-- The current actual creation has the source-proved complete Main accounting-input independence. -/
theorem sourceCreate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    :
    RegistrationNativeKemCounterIndependence.Stable (project (n := n))
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)) := by
  have commuting (before : RegistrationNativeExperiment.State n KemSK source) :
      RegistrationNativePublicSourceState.nativeView (RegistrationNativeMldsaNativeView.project before) =
        RegistrationNativeMldsaNativeView.project (RegistrationNativePublicSourceState.nativeView before) := by
    simp only [RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
      RegistrationServerRecordWorldSource.project, RegistrationNativeMldsaNativeView.project,
      RegistrationNativeMldsaNativeView.server, RegistrationNativeMldsaWorldView.project,
      RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
      RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]
  have sameProjection : (fun before : RegistrationNativeExperiment.State n KemSK source =>
      RegistrationNativeMldsaNativeView.project (RegistrationNativePublicSourceState.nativeView before)) = project := by
    funext before
    simp only [RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
      RegistrationServerRecordWorldSource.project, RegistrationNativeMldsaNativeView.project,
      RegistrationNativeMldsaNativeView.server, project, RegistrationNativeMldsaMainView.uniform,
      RegistrationNativeKemServerState.maskServer, RegistrationNativeMldsaWorldView.project,
      RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
      RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]
  have law := compose_stable RegistrationNativePublicSourceState.nativeView RegistrationNativeMldsaNativeView.project
    commuting _ (RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
      (RegistrationNativeBeaconEnvCreate.create_stable setup edPin mlPin keyId))
      (RegistrationNativeMldsaNativeView.beacon setup checks representation created _)
  rw [sameProjection] at law
  exact law

/-- Current ordinary Beacon creation retain the source behavior after count normalization. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Correct (project (n := n))
      (RegistrationNativeMldsaCreation.create (source := source) setup checks representation created edPin mlPin keyId) := by
  unfold RegistrationNativeMldsaCreation.create
  exact RegistrationNativeMldsaCountRules.closed _ _
    (sourceCreate setup checks representation created edPin mlPin keyId)
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.sourceCreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.sourceCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.create
