-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun

/-! Whole bundle source equality uses the same private realization projection as actual constructor source equality. Preservation of the private seed prefix is derived from the reached bundle execution, including failed publication; no history, Env or World projection is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleObservation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityRealization (observe owners Owned)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- Actual bundle execution privately realizes exactly the original complete native bundle operation, retaining all mutable source fields and optional failures. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeIdentityWorld.State n KemSK) (owned : Owned setup.joint before.identities current) :
    observe (fun _ value => value) <$>
      (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.bundle setup source wire index).run current).run env)).run before =
      (simulateQ (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created)
        (((RegistrationNativeBeaconFrontend.bundle setup source wire index).run (owners before.identities current)).run env)).run before.context := by
  have equal := RegistrationNativeIdentityBundleRun.bundle_source setup checks representation created wire index before.identities.seeds
    ((current, env), before) rfl owned
  have projected := congrArg (fun evaluated =>
    (fun (result : RustM (Option Pqxdh.Bytes) × OldState n KemSK Auxiliary source) =>
      (((result.1, result.2.1.1), result.2.1.2), result.2.2)) <$> evaluated) equal
  simp only [runNew, runOld, view, Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, id_map'] at projected
  have priorOwners : owners ⟨before.identities.seeds, []⟩ current = owners before.identities current := rfl
  rw [priorOwners] at projected
  rw [← projected, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have stored := RegistrationNativeIdentityBundleRun.bundle_keeps setup checks representation created wire index
    ((current, env), before) (result.1.1.1, ((result.1.1.2, result.1.2), result.2)) (by
      simp only [runNew, support_map]
      exact Set.mem_image_of_mem _ reached)
  change result.2.identities.seeds = before.identities.seeds at stored
  have same : RegistrationNativeIdentityRealization.owner (source := source) result.2.identities =
      RegistrationNativeIdentityRealization.owner ⟨before.identities.seeds, []⟩ := by
    funext selected
    unfold RegistrationNativeIdentityRealization.owner RegistrationNativeIdentityRealization.seedFor
    rw [stored]
  simp only [observe, Function.comp_def, RegistrationNativeIdentityRealization.owners, same]

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleObservation.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleObservation.bundle_source
