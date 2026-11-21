-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState
/-! Actual common-state Word callbacks outside Server acceptance and build preserve the complete retained session table. Their shared platform state and failed record writers remain in the supported execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State M)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Good (input : Message → Option Key) (before : State source Platform)
    (context : RegistrationNativeSecretWordInterpreter.State n KemSK) : Prop :=
  RegistrationNativeSecretWordLiveFlags.Valid input context ∧
    RegistrationNativeSecretWordLiveSessions.Live before.1.server context.flags

private theorem beacon_server
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A)
    (before : State source Platform) (result : A × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.beacon work).run before)) :
    result.2.1.server = before.1.server := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon, StateT.run, support_map] at supported
  obtain ⟨reached, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.1.server) equal).symm

private theorem record_server
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    result.2.1.server = before.1.server := by
  rcases query with (_ | _) | ⟨index, _ | _⟩
  all_goals simp only [RegistrationNativePlatformSecretWordOrdinary.record, StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; rfl
    | rw [support_map] at supported; obtain ⟨reached, _possible, equal⟩ := supported; exact (congrArg (fun output => output.2.1.server) equal).symm
    | rw [mem_support_bind_iff] at supported; obtain ⟨reply, _called, supported⟩ := supported
      rw [mem_support_bind_iff] at supported; obtain ⟨reached, _called, supported⟩ := supported
      rw [mem_support_pure_iff] at supported; cases supported; rfl

/-- Every ordinary Word callback retains the full symbolic Server state under all reached replies. -/
theorem ordinary_server (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) setup source selectedOwner publicPrekey reserve writer query).run before)) :
    result.2.1.server = before.1.server := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      exact (congrArg (fun output => output.2.1.server) equal).symm
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_server _ before result supported
    | bundle index =>
      rw [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_map, support_map] at supported
      obtain ⟨reached, possible, equal⟩ := supported
      cases equal
      exact beacon_server _ before reached possible
    | accept packet | build handle application | finish index packet | hmac key bytes =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
    | hash bytes =>
      simp only [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      exact (congrArg (fun output => output.2.1.server) equal).symm
    | serverSend keyId plaintext => exact record_server reserve (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_server reserve (.inl (.inr raw)) before result supported
    | beaconSend index plaintext => exact record_server reserve (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index raw => exact record_server reserve (.inr (index, .inr raw)) before result supported

/-- Corrected incoming completion changes its owner and environment while retaining every Server capability. -/
theorem finish_server (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State source Platform) (result : RustM (Option Pqxdh.Bytes) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run before)) :
    result.2.1.server = before.1.server := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run] at supported
  split at supported
  · rw [mem_support_pure_iff] at supported
    cases supported
    rfl
  · rw [support_map] at supported
    obtain ⟨reached, _possible, equal⟩ := supported
    exact (congrArg (fun output => output.2.1.server) equal).symm

/-- Every callback outside acceptance and build retains the exact live-session carrier. -/
theorem quiet_server [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 3 ∧ RegistrationNativeRawAdapter.kind query ≠ 4)
    (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    result.2.1.server = before.1.server := by
  cases query with
  | inl coin => exact ordinary_server setup source selectedOwner publicPrekey reserveFrame writer _ before result supported
  | inr query => cases query with
    | accept packet => exact False.elim (quiet.1 rfl)
    | build handle application => exact False.elim (quiet.2 rfl)
    | finish index packet => exact finish_server setup wire source index packet before result supported
    | _ => exact ordinary_server setup source selectedOwner publicPrekey reserveFrame writer _ before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.ordinary_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.ordinary_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.finish_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.finish_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.quiet_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState.quiet_server
