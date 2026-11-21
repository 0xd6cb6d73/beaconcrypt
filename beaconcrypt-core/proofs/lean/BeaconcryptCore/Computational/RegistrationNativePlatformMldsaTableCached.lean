-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCachedInvariant
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler

/-! Exact true-count private-table restoration derives the cached signing-history invariant for the actual corrected callback. Restoration changes only credential representation; complete native history/cache and external platform state are literal. Reached credential ownership is an execution invariant and no callback validity or source-security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCached
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaTableRestore (observe)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
variable [primitive : AdapterSealPrimitive.Operations]

/-- The actual corrected source callback preserves every cached ML receipt at the same reached private-table/platform cut. -/
theorem cached (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential (handleSource source)) (fallback : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) (pool : Pool source)
    (server : Live source pool credential fallback)
    (valid : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) before previous pool)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.1.1.2) := by
  have reached : observe source fallback result ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source fallback view failure allocation
        reserveRegistration reservePeer erased helper writer query).run
          (RegistrationNativeMldsaMap.nativeState (restore source fallback pool) before)).run previous) := by
    rw [← RegistrationNativePlatformMldsaTableHandler.restored source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer fallback pool server query before previous, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativePlatformCachedInvariant.handler setup checks wire route representation created fallback view failure allocation
    reserveRegistration reservePeer erased helper writer query
    (RegistrationNativeMldsaMap.nativeState (restore source fallback pool) before) previous (observe source fallback result) valid reached

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCached.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCached.cached
