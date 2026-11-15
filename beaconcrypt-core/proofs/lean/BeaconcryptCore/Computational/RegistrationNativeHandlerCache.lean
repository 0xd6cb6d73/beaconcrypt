-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHandlerCacheCore
import BeaconcryptCore.Computational.RegistrationNativeMldsaFamilyCover

/-! All complete original native typed callbacks extend their single shared CTX cache. Actual opaque-table restoration preserves that cache literally, so the same monotonicity applies to the true-count dynamic generation family. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHandlerCache
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept RegistrationServerSdkSource.build
/-- The exact actual private-table callback extends the same literal cache; dynamic key restoration changes only credentials. -/
theorem table (mlSource : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource mlSource))
    (fallback : RegistrationNativeMldsa.Credential mlSource) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) mlSource)
    (safe : RegistrationNativeMldsaTableStop.Safe mlSource credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) mlSource)
    (supported : result ∈ support ((RegistrationNativeMldsaTableStop.callback mlSource setup checks wire route representation created credential query).run before)) :
    RegistrationNativeWorldCache.cache before.1 ≤ RegistrationNativeWorldCache.cache result.2.1 := by
  simp only [RegistrationNativeMldsaTableStop.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  have restored : RegistrationNativeMldsaTableRestore.observe mlSource fallback inner ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource fallback query).run
        (RegistrationNativeMldsaMap.nativeState (RegistrationNativeMldsaOpaque.restore mlSource fallback before.2) before.1)) := by
    rw [← RegistrationNativeMldsaTableHandler.restored mlSource setup checks wire route representation created credential fallback before.2
      safe.server query before.1, support_map]
    exact ⟨inner, reached, rfl⟩
  exact handler setup checks wire route representation created fallback query _ _ restored

/-- A single actual simultaneous-family callback extends its retained global cache, including every failed generation or signing path. -/
theorem family {cap : Nat} (mlSource : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource mlSource))
    (fallback : RegistrationNativeMldsa.Credential mlSource) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaGhostFamily.State mlSource cap n KemSK)
    (safe : RegistrationNativeMldsaFamilyCover.Safe mlSource credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeMldsaGhostFamily.State mlSource cap n KemSK)
    (supported : result ∈ support ((RegistrationNativeMldsaGhostFamily.callback mlSource setup checks wire route representation created credential query).run before)) :
    RegistrationNativeWorldCache.cache before.1 ≤ RegistrationNativeWorldCache.cache result.2.1 := by
  apply table mlSource setup checks wire route representation created credential fallback query
    (RegistrationNativeMldsaGhostFamily.nativeState mlSource before) safe.1.safe
    (result.1, RegistrationNativeMldsaGhostFamily.nativeState mlSource result.2)
  rw [← RegistrationNativeMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeHandlerCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHandlerCache.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHandlerCache.table

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHandlerCache.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHandlerCache.family
