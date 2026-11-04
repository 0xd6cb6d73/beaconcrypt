-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleNoCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateRecords
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCaps
/-! The corrected material callback macros have zero private KEM births. Each bound comes from its actual common-state source language, including stateful reservations, assigned-ID finish and all failed results. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePlatformSecretWordFrontend
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- No actual callback except owner creation can introduce a new private KEM row. -/
theorem handler_free (query : TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State source Platform) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  cases query with
  | inl coin =>
    simp [handler, RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp,
      RegistrationNativeSecretWordFrontend.effect, RegistrationNativeSecretWordTargetPoolFrame.IsCreate,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  | inr command => cases command with
    | create edPin mlPin keyId => exact (quiet rfl).elim
    | bundle index => exact RegistrationNativePlatformSecretWordAliasBundleNoCreate.bundle_zero setup selectedOwner publicPrekey reserveFrame writer index before
    | accept packet => exact RegistrationNativePlatformSecretWordNoCreateMaterial.accept_bound setup checks source selectedAccept reserveRegistration packet before
    | build handle application => exact RegistrationNativePlatformSecretWordNoCreateMaterial.build_bound setup source sign view failure allocation reservePeer erased helper writer handle application before
    | finish index packet => exact RegistrationNativePlatformSecretWordNoCreateMaterial.finish_bound setup wire source index packet before
    | hmac key bytes => trivial
    | hash bytes =>
      simp [handler, RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp,
        RegistrationNativeSecretWordFrontend.effect, RegistrationNativeSecretWordTargetPoolFrame.IsCreate,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | serverSend keyId plaintext => exact RegistrationNativePlatformSecretWordNoCreateRecords.record_free reserveFrame (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact RegistrationNativePlatformSecretWordNoCreateRecords.record_free reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact RegistrationNativePlatformSecretWordNoCreateRecords.record_free reserveFrame (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact RegistrationNativePlatformSecretWordNoCreateRecords.record_free reserveFrame (.inr (index, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend.handler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend.handler_free
