-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks

/-! Current Beacon construction is ordinary native work and leaves the ML key table unchanged. Its source transport is parametric in the phantom Beacon ML source type; the mandatory Server credential remains a separate live table row. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaTableProgram (runState)
open RegistrationNativeMldsaTableRestore (observe)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)

/-- The complete actual constructor restores without extending the ML table or sampling an ML key. -/
theorem restored (fallback : Credential source) (pool : Pool source)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    observe source fallback <$> runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool =
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run
          (nativeState (restore source fallback pool) before) := by
  rw [RegistrationNativeMldsaCreation.create, RegistrationNativeMldsaTableProgram.run_liftState]
  simp only [Functor.map_map, observe]
  exact RegistrationNativeMldsaGlobalMap.create_natural (restore source fallback pool)
    setup checks representation created edPin mlPin keyId before

/-- Each reached constructor outcome retains the original ML table and the same-run ordinary source outcome. -/
theorem reached_ordinary (pool : Pool source) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    result.2 = pool ∧ result.1 ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup (handleSource source) edPin mlPin keyId)).run before) := by
  rw [RegistrationNativeMldsaCreation.create, RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
  obtain ⟨answer, possible, same⟩ := supported
  cases same
  exact ⟨rfl, possible⟩

/-- Beacon construction retains the same mandatory Server credential row. -/
theorem key_live (pool : Pool source) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (handle : Credential (handleSource source)) (key : Credential source)
    (old : RegistrationNativeMldsaOpaque.Live source pool handle key)
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    RegistrationNativeMldsaOpaque.Live source result.2 handle key := by
  rw [(reached_ordinary source pool setup checks representation created edPin mlPin keyId before result supported).1]
  exact old

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.restored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.reached_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.reached_ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.key_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation.key_live
