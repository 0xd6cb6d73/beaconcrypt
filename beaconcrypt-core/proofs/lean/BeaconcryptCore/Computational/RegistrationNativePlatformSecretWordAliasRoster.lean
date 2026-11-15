-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundle
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! Every actual symbolic controller preserves the ordered KEM metadata of all earlier owners. Creation only extends that metadata after its actual complete constructor, and bundle/finish retain it through arbitrary material and authentication failures. No owner/private-pool index equality is included in this structural property. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetPublication (key pack_keys restore_keys)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem server_keys
    (work : RegistrationNativePlatformSecretWordOpen.PublicM (RegistrationNativePlatformSecretWordFrontend.Base n KemSK Platform) Value)
    (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.serverOpen work).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

private theorem record_keys (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  rcases query with (send | raw) | ⟨index, send | raw⟩
  · simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨_, _, ⟨_, _, returned⟩⟩ := supported
    cases returned
    rfl
  · simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · cases found : before.1.beacons[index]? with
    | none =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some owner =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, found, mem_support_bind_iff] at supported
      obtain ⟨_, _, ⟨_, _, returned⟩⟩ := supported
      cases returned
      rfl
  · cases found : before.1.beacons[index]? with
    | none =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some owner =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run, found, support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl

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

/-- Every actual nonconstructor callback retains the ordered KEM metadata, including dynamic writers and corrected finish. -/
theorem handler_keys (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordOrdinary.handler,
      StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  | inr command => cases command with
    | create edPin mlPin keyId => exact (quiet rfl).elim
    | bundle index => exact RegistrationNativePlatformSecretWordAliasBundle.bundle_keys setup selectedOwner publicPrekey reserveFrame writer index before result supported
    | finish index packet => exact RegistrationNativePlatformSecretWordAliasFinish.finish_keys setup wire index packet before result supported
    | accept packet =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.accept,
        StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind] at supported
      exact server_keys _ ({before.1 with parsedAccepts := before.1.parsedAccepts + 1}, before.2) result supported
    | build handle application =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.build,
        StateT.run, support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
    | hmac key bytes =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | hash bytes =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
    | serverSend keyId plaintext => exact record_keys reserveFrame (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_keys reserveFrame (.inl (.inr raw)) before result supported
    | beaconSend index plaintext => exact record_keys reserveFrame (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index raw => exact record_keys reserveFrame (.inr (index, .inr raw)) before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster.handler_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster.handler_keys
