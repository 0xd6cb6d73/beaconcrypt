-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix

/-! Immutable owner tuples extend monotonically in the literal typed CTX runtime. Handle distinctness uses the actual generated-row ownership invariant only as an internal induction hypothesis; public keys may alias. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMetadata (keys)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "ambient" => RegistrationNativePlatformIdentityCtxDispatch.step setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

def NotCreate : TypedSpec.Domain → Prop
  | .inr (.create _ _ _) => False
  | _ => True

private theorem ambient_keys (query : TypedSpec.Domain) (before : Full n KemSK Platform source)
    (result : TypedSpec.Range query × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (ambient query)).run before)) :
    keys result.2.1.1.beacons = keys before.1.1.beacons :=
  congrArg keys (RegistrationNativePlatformIdentityCtxKeyPrefix.ordinary_keys setup.joint _ before result reached)

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step
  RegistrationNativePlatformIdentityMainAmbient.command

/-- Every nonconstructor callback preserves each immutable owner tuple at the same position. -/
theorem handler_keys (query : TypedSpec.Domain) (allowed : NotCreate query)
    (before : Full n KemSK Platform source) (result : TypedSpec.Range query × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (frontend query)).run before)) :
    keys result.2.1.1.beacons = keys before.1.1.beacons := by
  cases query with
  | inl coin => exact ambient_keys setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached
  | inr query => cases query with
    | create edPin mlPin keyId => cases allowed
    | bundle index => exact RegistrationNativePlatformIdentityCtxKeyPrefix.bundle_keys setup checks representation created writer index before result reached
    | finish index packet => exact RegistrationNativePlatformIdentityCtxKeyPrefix.finish_keys setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before result reached
    | accept packet =>
      unfold RegistrationNativePlatformIdentityCtxTyped.handler at reached
      rw [RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind,
        RegistrationNativePlatformIdentityCtxOrdinary.report_source, pure_bind] at reached
      exact ambient_keys setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached
    | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      exact ambient_keys setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result reached

/-- The complete typed callback keeps every prior immutable tuple as an ordered prefix, including failures. -/
theorem handler_prefix (query : TypedSpec.Domain)
    (before : Full n KemSK Platform source) (result : TypedSpec.Range query × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (frontend query)).run before)) :
    keys before.1.1.beacons <+: keys result.2.1.1.beacons := by
  by_cases allowed : NotCreate query
  · rw [handler_keys setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query allowed before result reached]
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxKeyPrefix.create_prefix setup checks representation created edPin mlPin keyId before result reached
      | bundle index | finish index packet | accept packet | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw => exact False.elim (allowed trivial)

/-- Genuine source creation is the only extending callback and assigns a fresh private handle. -/
theorem handler_distinct (query : TypedSpec.Domain)
    (before : Full n KemSK Platform source) (result : TypedSpec.Range query × Full n KemSK Platform source)
    (owned : Owned setup.joint before) (distinct : RegistrationNativeIdentityHistorySync.Distinct before.1.1.beacons)
    (reached : result ∈ support ((interpret setup.joint (frontend query)).run before)) :
    RegistrationNativeIdentityHistorySync.Distinct result.2.1.1.beacons := by
  by_cases allowed : NotCreate query
  · exact RegistrationNativeIdentityHistorySync.distinct_fields _ _
      (handler_keys setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query allowed before result reached) distinct
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxKeyPrefix.create_distinct setup checks representation created edPin mlPin keyId before result owned distinct reached
      | bundle index | finish index packet | accept packet | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw => exact False.elim (allowed trivial)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys.handler_distinct
