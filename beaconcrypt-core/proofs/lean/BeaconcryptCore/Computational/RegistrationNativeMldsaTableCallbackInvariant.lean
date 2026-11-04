-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCached

/-! The actual dynamic ML table preserves the original cached signing receipts at each typed callback, together with the independently derived private-attempt/native-payload chronology and reached credential ownership. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbackInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaPoolMap (StateLive)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaTableProgram (runState)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

/-- Actual source restoration derives the per-callback cached-history invariant of the table-backed interpreter. -/
theorem cached (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential (handleSource source)) (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (server : Live source pool credential fallback) (owners : StateLive source pool before)
    (valid : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before pool)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.1.2) := by
  have reached : RegistrationNativeMldsaTableRestore.observe source fallback result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source fallback query).run
        (RegistrationNativeMldsaMap.nativeState (restore source fallback pool) before)) := by
    rw [← RegistrationNativeMldsaTableHandler.restored source setup checks wire route representation created
      credential fallback pool server query before owners, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativeMldsaInvariant.handler setup checks wire route representation created fallback query
    (RegistrationNativeMldsaMap.nativeState (restore source fallback pool) before) valid
    (RegistrationNativeMldsaTableRestore.observe source fallback result) reached

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbackInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbackInvariant.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbackInvariant.cached
