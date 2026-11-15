-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativeMainViewLift
/-! The literal effectful bundle preserves its exact reply and full Native/P execution under only the named native-call, Env-coin and record-kind marker view. Real uniform counts, physical cache, generated private pool, owner histories and arbitrary writer failures remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {I KemSK E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Actual primitive source sampling commutes with marker erasure in the same arbitrary lawful common monad. -/
theorem trusted (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Stable nativeView (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source query) := by
  intro before
  have actual := congrArg (simulateQ coins) (RegistrationNativeMainViewLift.trusted_input setup checks representation created query before)
  simpa only [RegistrationNativePlatformExperiment.trusted, RegistrationNativePlatformExperiment.liftNative,
    StateT.run, simulateQ_map] using actual

private theorem external (work : m A) :
    Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source)) (StateT.lift work) := by
  intro before
  simp only [StateT.run_lift, map_bind, map_pure, Prod.map_def, id_eq,
    RegistrationNativeMainViewLift.view_idempotent]

/-- Each actual source trusted/registration-writer request retains the same common state and literal optional reply. -/
theorem program (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A) :
    Stable nativeView (simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work) := by
  apply RegistrationStateView.program_stable nativeView RegistrationNativeMainViewLift.view_idempotent
  intro query
  cases query with
  | inl query => exact trusted coins setup checks representation created query
  | inr query => exact external (writer query)

abbrev LocalOutput (source : RegistrationNativeMldsa.Source) :=
  (RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State

def output (result : LocalOutput source × RegistrationNativeExperiment.State n KemSK source) :
    RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source :=
  ((do let optional ← result.1.1.1; .ok (optional.map TranscriptAuthParts.absSlice)),
    nativeView { result.2 with
      beacons := result.1.1.2
      server := { result.2.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })
private theorem output_native (result : LocalOutput source × RegistrationNativeExperiment.State n KemSK source) :
    output (result.1, nativeView result.2) = output result := by
  simp only [output, nativeView, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerRecordWorldSource.project, RegistrationWorldAgreementCompiler.join,
    RegistrationNativeWorldView.project_idempotent]
private theorem output_env (result : LocalOutput source × RegistrationNativeExperiment.State n KemSK source) :
    output ((result.1.1, RegistrationNativeBeaconEnvView.erase result.1.2), result.2) = output result := rfl


/-- The complete literal source bundle ignores only instrumentation markers, retaining true uniform costs and all allocation/serializer poststates in the same common monad. -/
theorem bundle (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat) :
    Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source))
      (RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index) := by
  intro before
  let handler := RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer
  let original := ((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run before.beacons).run
    (RegistrationWorldAgreementCompiler.erase before.server.world)
  let viewed := ((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run before.beacons).run
    (RegistrationNativeBeaconEnvView.erase (RegistrationWorldAgreementCompiler.erase before.server.world))
  have inputLaw := RegistrationNativePlatformBundleEnvMetricView.program (n := n) E setup index before.beacons
    (RegistrationWorldAgreementCompiler.erase before.server.world)
  have envLaw := congrArg (fun tree => output <$> (simulateQ handler tree).run before) inputLaw
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq] at envLaw
  have first : output <$> (simulateQ handler original).run before = output <$> (simulateQ handler viewed).run before := by
    simpa only [original, viewed, output_env] using envLaw
  have sourceLaw := program coins setup checks representation created writer viewed before
  have second := congrArg (fun action => output <$> action) sourceLaw
  simp only [Functor.map_map, Prod.map_def, id_eq, output_native] at second
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_pure_comp, Functor.map_map]
  change output <$> (simulateQ handler original).run before = output <$>
    (simulateQ handler viewed).run (nativeView before)
  exact first.trans second
end BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetricView.bundle
