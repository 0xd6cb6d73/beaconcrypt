-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation

/-! Actual owner generation uses the existing real-count private table and creation suffix. The external platform state is retained literally while the extended table restores the newly born credential and every previous live owner. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (StateLive)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaTableRestore (observe)
variable {n : Nat} {KemSK Platform ι : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)
variable (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)

/-- Actual successful and failed creation restores the complete native result and unchanged external state. -/
theorem restored (fallback : Credential source) (pool : Pool source)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (live : StateLive source pool before) :
    observe source fallback <$> runState source
      (RegistrationNativePlatformMldsaProgram.inject
        (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId)) before previous pool =
      (fun result => (result, previous)) <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run
            (nativeState (restore source fallback pool) before) := by
  rw [RegistrationNativePlatformMldsaTableProgram.run_inject]
  have same := congrArg (fun action => (fun result => (result, previous)) <$> action)
    (RegistrationNativeMldsaTableCreation.restored source fallback pool setup checks representation created
      edPin mlPin keyId before live)
  simpa only [Functor.map_map, observe, RegistrationNativeMldsaTableRestore.observe] using same

/-- Every actual creation retains previous live owners and its actual generated owner in the reached extended table. -/
theorem live (pool : Pool source)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (old : StateLive source pool before)
    (result : ((RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativePlatformMldsaProgram.inject
        (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId)) before previous pool)) :
    StateLive source result.2 result.1.1.2 := by
  rw [RegistrationNativePlatformMldsaTableProgram.run_inject, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  exact RegistrationNativeMldsaTableCreation.live source pool setup checks representation created
    edPin mlPin keyId before old original reached

/-- The actual Server key row survives every owner-generation attempt, including failed creation suffixes. -/
theorem key_live (pool : Pool source)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (credential : Credential (handleSource source)) (key : Credential source) (old : Live source pool credential key)
    (result : ((RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativePlatformMldsaProgram.inject
        (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId)) before previous pool)) :
    Live source result.2 credential key := by
  rw [RegistrationNativePlatformMldsaTableProgram.run_inject, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  exact RegistrationNativeMldsaTableCreation.key_live source pool setup checks representation created
    edPin mlPin keyId before credential key old original reached
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.restored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.key_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation.key_live
