-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCreation

/-! The complete actual native handler restores through its reached private key table, including dynamic owner creation. Each callback preserves the same actual Server key and every reached live owner; these source-derived invariants support arbitrary adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaTableProgram (runState)
open RegistrationNativeMldsaTableRestore (observe)
open RegistrationNativeMldsaLiveOwners (NonCreate)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : Credential (handleSource source)) (fallback : Credential source) (pool : Pool source)
local notation "callback" => RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- The entire actual table-backed native handler restores its literal real-key source counterpart. -/
theorem restored (server : Live source pool credential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    observe source fallback <$> runState source (callback query) before pool =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source fallback query).run
        (nativeState (restore source fallback pool) before) := by
  have ordinary (allowed : NonCreate query) :
      observe source fallback <$> runState source (callback query) before pool =
        (RegistrationNativeExperiment.handler setup checks wire route representation created source fallback query).run
          (nativeState (restore source fallback pool) before) := by
    have same := RegistrationNativeMldsaTableCallbacks.restored source setup checks wire route representation created
      credential pool fallback ⟨fallback, server⟩ query allowed before
    rw [RegistrationNativeMldsaOpaque.restore_live source fallback pool credential fallback server] at same
    exact same
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
        simp only [RegistrationNativeMldsaProfile.handler, RegistrationNativeExperiment.handler]
        exact RegistrationNativeMldsaTableCreation.restored source fallback pool setup checks representation created
          edPin mlPin keyId before
    | _ => exact ordinary trivial

/-- The owned Server handle keeps its same actual real key across every callback, including failed and successful owner generation. -/
theorem server_live (server : Live source pool credential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source (callback query) before pool)) : Live source result.2 credential fallback := by
  have ordinary (allowed : NonCreate query) : Live source result.2 credential fallback := by
    have rows := RegistrationNativeMldsaTableCallbacks.keys source setup checks wire route representation created
      credential pool ⟨fallback, server⟩ query allowed before result supported
    exact ⟨by rw [rows]; exact server.1, server.2⟩
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeMldsaTableCreation.key_live source pool setup checks representation created
          edPin mlPin keyId before credential fallback server result supported
    | _ => exact ordinary trivial
end BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler.restored


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler.server_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableHandler.server_live
