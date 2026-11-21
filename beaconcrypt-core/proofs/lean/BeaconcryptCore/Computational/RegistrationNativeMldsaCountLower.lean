-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Actual ordinary Beacon subprograms lower through the same counted trusted native service. Their source-derived Env record-kind noninterference combines with the checked native accounting view, retaining every optional reply, mutable owner, auxiliary state and signing/cache receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeMldsaMainView (project)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem commuting (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativePublicSourceState.nativeView (RegistrationNativeMldsaNativeView.project before) =
      RegistrationNativeMldsaNativeView.project (RegistrationNativePublicSourceState.nativeView before) := by
  simp only [RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerRecordWorldSource.project, RegistrationNativeMldsaNativeView.project,
    RegistrationNativeMldsaNativeView.server, RegistrationNativeMldsaWorldView.project,
    RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

private theorem sameProjection : (fun before : RegistrationNativeExperiment.State n KemSK source =>
    RegistrationNativeMldsaNativeView.project (RegistrationNativePublicSourceState.nativeView before)) = project := by
  funext before
  simp only [RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerRecordWorldSource.project, RegistrationNativeMldsaNativeView.project,
    RegistrationNativeMldsaNativeView.server, project, RegistrationNativeMldsaMainView.uniform,
    RegistrationNativeKemServerState.maskServer, RegistrationNativeMldsaWorldView.project,
    RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commute : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : RegistrationNativeKemCounterIndependence.Stable first work)
    (right : RegistrationNativeKemCounterIndependence.Stable second work) :
    RegistrationNativeKemCounterIndependence.Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commute] at following
  exact initial.trans following

/-- The actual trusted native service ignores exactly the complete Main accounting-input view. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    RegistrationNativeKemCounterIndependence.Stable project
      (RegistrationNativeExperiment.trusted setup checks representation created source query) := by
  have law := compose_stable RegistrationNativePublicSourceState.nativeView RegistrationNativeMldsaNativeView.project
    (commuting (source := source))
      (RegistrationNativeExperiment.trusted setup checks representation created source query)
      (RegistrationNativeMainViewLift.trusted_input (mlSource := source) setup checks representation created query)
      (RegistrationNativeMldsaNativeView.trusted (source := source) setup checks representation created query)
  rw [sameProjection] at law
  exact law

def localProject (before : Local n KemSK source) : Local n KemSK source :=
  (before.1, (RegistrationNativeBeaconEnvView.erase before.2.1, project before.2.2))

/-- Repeated local projection preserves all reached owner and receipt data. -/
theorem idempotent (before : Local n KemSK source) : localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeBeaconEnvView.erase, RegistrationNativeMldsaMainView.idempotent]

/-- Actual lower execution retains both its mutable local Env and the shared native poststate under the source-proved accounting-input view. -/
theorem lower_stable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (stable : RegistrationNativeBeaconEnvView.Stable work) :
    RegistrationNativeKemCounterIndependence.Stable localProject (lower setup checks representation created work) := by
  intro before
  let implementation := RegistrationNativeExperiment.trusted (n := n) setup checks representation created source
  let script := (work.run before.1).run before.2.1
  have first := congrArg (fun computation => Prod.map (Prod.map id RegistrationNativeBeaconEnvView.erase) id <$> computation)
    (RegistrationStateView.program_stable project RegistrationNativeMldsaMainView.idempotent implementation
      (trusted setup checks representation created) script before.2.2)
  have environment := RegistrationNativeBeaconEnvView.run_input work stable before.1 before.2.1
  have interpreted := congrArg (fun program => (simulateQ implementation program).run (project before.2.2)) environment
  simp only [simulateQ_map, StateT.run_map] at interpreted
  have second := congrArg (fun computation => Prod.map id project <$> computation) interpreted
  simp only [Functor.map_map, Prod.map, id_eq] at first second
  have combined := first.trans second
  have final := congrArg (fun computation => (fun (result :
      ((Value × RegistrationNativeBeaconFrontend.State source) ×
        RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
          RegistrationNativeExperiment.State n KemSK source) =>
      (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$> computation) combined
  simp only [lower, StateT.run, Functor.map_map, Prod.map, id_eq, localProject,
    implementation, script] at final ⊢
  exact final

/-- Every actual source-proved ordinary Beacon subprogram supplies both free ML count-continuation laws. -/
theorem native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (stable : RegistrationNativeBeaconEnvView.Stable work) :
    RegistrationNativeMldsaCountRules.Correct localProject (RegistrationNativeMldsaBundle.native setup checks representation created work) :=
  RegistrationNativeMldsaCountRules.closed _ _ (RegistrationNativeMldsaCountLower.lower_stable setup checks representation created work stable)
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.lower_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.lower_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountLower.native
