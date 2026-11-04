-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun

/-! Whole finish source equality uses the same private realization projection as actual constructor source equality. Preservation of the private seed prefix is derived from the reached finish execution, including failed opening; no history, Env or World projection is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishObservation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityRealization (observe owners Owned)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- Actual finish execution privately realizes exactly the original complete native finish operation, retaining all mutable source fields and optional failures. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeIdentityWorld.State n KemSK) (owned : Owned setup.joint before.identities current) :
    observe (fun _ value => value) <$>
      (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativePlatformIdentityFinishRun.finish setup source wire index packet).run current).run env)).run before =
      (simulateQ (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created)
        (((RegistrationNativePlatformBeaconFinish.finish setup source wire index packet).run (owners before.identities current)).run env)).run before.context := by
  have equal := RegistrationNativePlatformIdentityFinishRun.finish_source setup checks representation created wire index packet before.identities.seeds
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
  have stored := RegistrationNativePlatformIdentityFinishRun.finish_keeps setup checks representation created wire index packet
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

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishObservation.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishObservation.finish_source
