-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerWorldBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishWorldOwner
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend (State)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
private def key (owner : RegistrationNativePublicOwners.Owner source) := owner.view.worldOwner
private theorem execute_support (work : RegistrationNativePlatformPublicFrontend.LocalM n KemSK Platform source Value)
    (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.executeLocal work).run before)) :
    result ∈ support (work.run before) := by
  exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
private theorem server_keys
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) Value)
    (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.serverOpen work).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  simp only [RegistrationNativePlatformPublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

private theorem record_keys (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  rcases query with (send | raw) | ⟨index, send | raw⟩
  · simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨_, _, ⟨_, _, returned⟩⟩ := supported
    cases returned
    rfl
  · simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · cases found : before.1.beacons[index]? with
    | none =>
      simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some owner =>
      simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, mem_support_bind_iff] at supported
      obtain ⟨_, _, ⟨_, _, returned⟩⟩ := supported
      cases returned
      rfl
  · cases found : before.1.beacons[index]? with
    | none =>
      simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      rfl
    | some owner =>
      simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, support_map] at supported
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


/-- Every actual nonconstructor public callback preserves ordered physical owner addresses through arbitrary platform outcomes. -/
theorem handler_worlds (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    result.2.1.beacons.map key = before.1.beacons.map key := by
  cases query with
  | inl coin =>
    have localResult := execute_support _ before result supported
    simp only [StateT.run_lift, bind_pure_comp, support_map] at localResult
    obtain ⟨_, _, rfl⟩ := localResult
    rfl
  | inr command => cases command with
    | create edPin mlPin keyId => exact (quiet rfl).elim
    | bundle index =>
      have localResult := execute_support _ before result supported
      rw [StateT.run_map, support_map] at localResult
      obtain ⟨raw, possible, equal⟩ := localResult
      simp only [RegistrationNativePlatformPublicFrontend.beacon, StateT.run, support_map] at possible
      obtain ⟨middle, reached, same⟩ := possible
      have kept := RegistrationNativePlatformPublicOwnerWorldBundle.public_worlds setup RegistrationNativePlatformPublicFrontend.trusted
        (RegistrationNativePlatformPublicFrontend.writer writer) selectedOwner index publicPrekey before.1.beacons before.1.environment before.2 middle reached
      cases equal
      cases same
      exact kept
    | finish index packet =>
      exact RegistrationNativePlatformPublicFinishWorldOwner.callback_keys setup checks wire source sign
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index packet before result supported
    | accept packet =>
      have localResult := execute_support _ before result supported
      simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind] at localResult
      exact server_keys _ ({before.1 with parsedAccepts := before.1.parsedAccepts + 1}, before.2) result localResult
    | build handle application =>
      have localResult := execute_support _ before result supported
      simp only [RegistrationNativePlatformPublicFrontend.build, StateT.run, support_map] at localResult
      obtain ⟨_, _, rfl⟩ := localResult
      rfl
    | hmac key bytes =>
      simp only [RegistrationNativePlatformPublicFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | hash bytes =>
      have localResult := execute_support _ before result supported
      simp only [StateT.run_lift, bind_pure_comp, support_map] at localResult
      obtain ⟨_, _, rfl⟩ := localResult
      rfl
    | serverSend keyId plaintext => exact record_keys reserveFrame (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_keys reserveFrame (.inl (.inr raw)) before result supported
    | beaconSend index plaintext => exact record_keys reserveFrame (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index raw => exact record_keys reserveFrame (.inr (index, .inr raw)) before result supported

/-- The actual ordered physical-address frame retains both roster length and all existing index assignments. -/
theorem handler_fields (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (prior : RegistrationNativeHiddenAllocationOwners.Indexed before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    result.2.1.beacons.length = before.1.beacons.length ∧ RegistrationNativeHiddenAllocationOwners.Indexed result.2.1.beacons := by
  have worlds := handler_worlds setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query quiet before result supported
  refine ⟨by simpa only [List.length_map] using congrArg List.length worlds, ?_⟩
  intro index owner found
  have selected : (result.2.1.beacons.map key)[index]? = some (key owner) := by
    simp only [List.getElem?_map, found, Option.map_some]
  rw [worlds, List.getElem?_map] at selected
  obtain ⟨original, present, equal⟩ := Option.map_eq_some_iff.mp selected
  exact equal.symm.trans (prior index original present)
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames.handler_worlds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames.handler_worlds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames.handler_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationOwnerFrames.handler_fields
