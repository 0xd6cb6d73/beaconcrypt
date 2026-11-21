-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole
import BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation

/-! Every actual corrected typed callback outside response build preserves the literal Server-role signing subsequence. Honest key byte aliases and all failed publication/authentication/assigned-ID completion paths remain admitted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRoleFrame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaRoleFrame (NonBuild serverReceipts)
open RegistrationNativeMldsaShared (nativeProject)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Only an actual source response build can introduce a Server-role signing receipt. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonBuild query)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    serverReceipts (nativeProject result.1.2).1 = serverReceipts (nativeProject before).1 := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer erased helper writer query = RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      serverReceipts (nativeProject result.1.2).1 = serverReceipts (nativeProject before).1 := by
    rw [same] at supported
    exact RegistrationNativeMldsaRoleFrame.handler setup checks wire route representation created credential query allowed before result.1
      (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)
  have incoming (free : RegistrationNativeMldsaReceiptPreservation.NonSigning query) :
      serverReceipts (nativeProject result.1.2).1 = serverReceipts (nativeProject before).1 := by
    have same := RegistrationNativePlatformReceiptPreservation.source_handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query free before previous result supported
    exact congrArg serverReceipts same
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index => exact RegistrationNativePlatformBundleRole.native_bundle source setup checks representation created writer index before previous result supported
    | build index application => exact False.elim allowed
    | accept packet | finish index packet => exact incoming trivial
    | _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformRoleFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRoleFrame.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRoleFrame.handler
