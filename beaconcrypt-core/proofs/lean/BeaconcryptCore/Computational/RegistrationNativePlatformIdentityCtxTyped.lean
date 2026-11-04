-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary

/-! Every actual typed callback of the corrected dynamic-writer runtime has the executable ordinary joint-Ed source interpretation. Generated-handle ownership is preserved internally on every callback outcome, with all original source failures and native/P poststates retained. The invariant is not a restriction on an adversary's public event. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ambient" => RegistrationNativePlatformIdentityCtxDispatch.step setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "callback" => RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

noncomputable def handler : QueryImpl TypedSpec (M n KemSK Platform source)
  | .inr (.create edPin mlPin keyId) => RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created
  | .inr (.bundle index) => RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index
  | .inr (.finish index packet) => RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet
  | .inr (.accept packet) => do
      RegistrationNativePlatformIdentityCtxOrdinary.report packet
      ambient (.inr (.accept packet))
  | query => ambient query

noncomputable def target : QueryImpl TypedSpec (StateT (RegistrationNativeExperiment.State n KemSK source × Platform) ProbComp) :=
  fun query => RegistrationNativePlatformPackedState.pack (callback query)

private theorem ambient_owned (query : TypedSpec.Domain) (before : Full n KemSK Platform source)
    (result : TypedSpec.Range query × (Full n KemSK Platform source))
    (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (ambient query)).run before)) : Owned setup.joint result.2 := by
  apply RegistrationNativePlatformIdentityCtxDispatch.step_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before result owned
  exact reached

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step RegistrationNativePlatformIdentityMainAmbient.command

/-- Every actual source callback preserves genuine generated-row ownership on all failed and successful paths. -/
theorem handler_owned (query : TypedSpec.Domain) (before : Full n KemSK Platform source)
    (result : TypedSpec.Range query × (Full n KemSK Platform source))
    (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint
      (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run before)) :
    Owned setup.joint result.2 := by
  cases query with
  | inl coin => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) before result owned reached
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxLifecycle.create_owned setup checks representation created edPin mlPin keyId before result owned reached
    | bundle index => exact RegistrationNativePlatformIdentityCtxLifecycle.bundle_owned setup checks representation created writer index before result owned reached
    | finish index packet => exact RegistrationNativePlatformIdentityCtxLifecycle.finish_owned setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before result owned reached
    | accept packet =>
      unfold handler at reached
      rw [RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind,
        RegistrationNativePlatformIdentityCtxOrdinary.report_source, pure_bind] at reached
      exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)) before result owned reached
    | build session application => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application)) before result owned reached
    | hmac key message => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message)) before result owned reached
    | hash bytes => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes)) before result owned reached
    | serverSend keyId plaintext => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext)) before result owned reached
    | serverRaw raw => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw)) before result owned reached
    | beaconSend index plaintext => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext)) before result owned reached
    | beaconRaw index raw => exact ambient_owned setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw)) before result owned reached

/-- The complete typed runtime exposes every actual CTX query and restores the same native/P distribution without a whole-handler source hypothesis. -/
theorem query_source (query : TypedSpec.Domain) (before : Full n KemSK Platform source)
    (owned : Owned setup.joint before) :
    Prod.map id native <$> (interpret setup.joint
      (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run before =
      (target setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run (native before) := by
  cases query with
  | inl coin => exact RegistrationNativePlatformIdentityCtxDispatch.step_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ (by trivial) before
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxLifecycle.create_source setup checks representation created edPin mlPin keyId before owned
    | bundle index => exact RegistrationNativePlatformIdentityCtxLifecycle.bundle_source setup checks representation created writer index before owned
    | finish index packet => exact RegistrationNativePlatformIdentityCtxLifecycle.finish_source setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet before owned
    | accept packet =>
      unfold handler
      rw [RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, StateT.run_bind,
        RegistrationNativePlatformIdentityCtxOrdinary.report_source, pure_bind]
      exact RegistrationNativePlatformIdentityCtxDispatch.step_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ (by trivial) before
    | build session application | hmac key message | hash bytes | serverSend keyId plaintext | serverRaw raw | beaconSend index plaintext | beaconRaw index raw =>
      exact RegistrationNativePlatformIdentityCtxDispatch.step_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ (by trivial) before

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped.handler_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped.handler_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped.query_source
