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

private theorem afterGenerated (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (generated : Option (Credential source)) :
    RegistrationNativeBeaconEnvView.Stable
      (RegistrationNativeMldsaCreation.afterGenerated (n := n) (KemSK := KemSK) edPin mlPin keyId generated) := by
  unfold RegistrationNativeMldsaCreation.afterGenerated
  cases generated with
  | none => exact RegistrationNativeBeaconEnvView.pure_stable _
  | some credential =>
      cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
      | ok pending =>
          simp only
          cases pending.request with
          | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
          | ok request =>
              simp only
              apply RegistrationNativeBeaconEnvView.bind_stable
              · exact RegistrationNativeBeaconEnvCallbacks.hash_stable request
              · intro digest
                cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
                | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
                | ok option => cases option with
                  | none => exact RegistrationNativeBeaconEnvView.pure_stable _
                  | some pin =>
                      exact RegistrationNativeBeaconEnvView.bind_stable _ _
                        (RegistrationNativeBeaconEnvCallbacks.sample_stable _) (fun _ =>
                          RegistrationNativeBeaconEnvView.bind_stable _ _
                            (RegistrationNativeBeaconEnvCallbacks.sample_stable _) (fun _ =>
                              RegistrationNativeBeaconEnvView.pure_stable _))

private theorem suffix_env (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) (generated : Option (Credential source)) :
    RegistrationNativeBeaconEnvView.Stable
      (RegistrationNativeMldsaCreation.createSuffix (n := n) setup edPin mlPin keyId generated) := by
  unfold RegistrationNativeMldsaCreation.createSuffix
  apply RegistrationNativeBeaconEnvView.bind_stable _ _ (afterGenerated edPin mlPin keyId generated)
  intro prepared
  cases prepared with
  | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
  | ok option => cases option with
    | none => exact RegistrationNativeBeaconEnvView.pure_stable _
    | some prepared =>
        exact RegistrationNativeBeaconEnvCreate.append_stable setup edPin keyId
          prepared.pin prepared.credentials prepared.identity prepared.prekey

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

/-- The unchanged actual creation suffix has the source-proved complete Main accounting-input independence. -/
theorem sourceSuffix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (generated : Option (Credential source)) :
    RegistrationNativeKemCounterIndependence.Stable (project (n := n))
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId generated)) := by
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
      (suffix_env setup edPin mlPin keyId generated))
      (RegistrationNativeMldsaNativeView.beacon setup checks representation created _)
  rw [sameProjection] at law
  exact law

/-- Actual free ML generation and its complete creation suffix retain the source behavior after count normalization. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Correct (project (n := n))
      (RegistrationNativeMldsaCreation.create (source := source) setup checks representation created edPin mlPin keyId) := by
  unfold RegistrationNativeMldsaCreation.create
  exact RegistrationNativeMldsaCountRules.bind project _ _
    (RegistrationNativeMldsaCountNative.call .environment .generate)
    (fun generated => RegistrationNativeMldsaCountRules.closed _ _
      (sourceSuffix setup checks representation created edPin mlPin keyId generated))
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.sourceSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.sourceSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation.create
