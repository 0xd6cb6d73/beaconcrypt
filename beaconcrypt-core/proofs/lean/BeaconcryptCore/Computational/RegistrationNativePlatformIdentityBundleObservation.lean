-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun

/-! Private realization of the complete effectful opaque-Ed bundle uses the actual generated source row at the reached same-run state. Equality of the private seed prefix is derived from all-outcome execution; no history, platform, cache or native counter coordinate is discarded. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleObservation
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityRealization (owners Owned)
variable {n : Nat} {ι KemSK Auxiliary Platform E Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def observe (result : (((Value × RegistrationNativeIdentityFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform) × RegistrationNativeIdentityWorld.State n KemSK) :=
  ((((result.1.1.1.1, owners result.2.identities result.1.1.1.2), result.1.1.2), result.1.2), result.2.context)

/-- The same private source projection restores actual bundle execution without assuming ownership or history facts about a later reconstructed state. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (current : RegistrationNativeIdentityFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (previous : Platform) (before : RegistrationNativeIdentityWorld.State n KemSK)
    (owned : Owned setup.joint before.identities current) :
    observe <$>
      (simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created)
        ((((RegistrationNativePlatformIdentityBundleRun.bundle setup index writer).run current).run env).run previous)).run before =
      (simulateQ (RegistrationNativePlatformIdentityProgram.originalImplementation (source := source) setup checks representation created)
        ((((RegistrationNativePlatformIdentityBundleRun.originalBundle setup index writer).run (owners before.identities current)).run env).run previous)).run before.context := by
  have equal := RegistrationNativePlatformIdentityBundleRun.bundle_source setup checks representation created before.identities.seeds index writer
    (((current, env), before), previous) rfl owned
  have projected := congrArg (fun evaluated =>
    (fun result : RustM (Option (alloc.vec.Vec U8)) × (RegistrationNativeIdentitySourceSimulation.OldState n KemSK Auxiliary source × Platform) =>
      ((((result.1, result.2.1.1.1), result.2.1.1.2), result.2.2), result.2.1.2)) <$> evaluated) equal
  simp only [RegistrationNativePlatformIdentityProgram.runNew, RegistrationNativePlatformIdentityProgram.runOld,
    RegistrationNativePlatformIdentityProgram.project, RegistrationNativeIdentitySourceSimulation.view,
    Functor.map_map, Prod.map, id_eq, Prod.mk.eta, id_map'] at projected
  have priorOwners : owners ⟨before.identities.seeds, []⟩ current = owners before.identities current := rfl
  rw [priorOwners] at projected
  rw [← projected, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have stored := RegistrationNativePlatformIdentityBundleRun.bundle_keeps setup checks representation created index writer
    (((current, env), before), previous)
    (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.2), result.1.2)) (by
      simp only [RegistrationNativePlatformIdentityProgram.runNew, support_map]
      exact Set.mem_image_of_mem _ reached)
  change result.2.identities.seeds = before.identities.seeds at stored
  have same : RegistrationNativeIdentityRealization.owner (source := source) result.2.identities =
      RegistrationNativeIdentityRealization.owner ⟨before.identities.seeds, []⟩ := by
    funext selected
    unfold RegistrationNativeIdentityRealization.owner RegistrationNativeIdentityRealization.seedFor
    rw [stored]
  simp only [Function.comp_def, observe, RegistrationNativeIdentityRealization.owners, same]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleObservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleObservation.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleObservation.bundle_source
