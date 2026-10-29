-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

/-!
Successful authentication retains the actual decoded packet through all three Ed25519 stages. The stored PQ and prekey arrays are precisely the earlier accepted opened replies; final validation reads the original identity field and the exact three attached suffixes. The accepted registration therefore has an actual native validator receipt for those packet fields, without a caller-supplied credential correspondence.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationCredentialMetadata

open RegistrationAuthentication RegistrationInbound RegistrationAuthenticationFlow

def Credential (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex) : Prop :=
  ∃ input : pqxdh.InitKex,
    input.identity_key = packet.identity_key ∧
    input.prekey.val = packet.pre_key.val.drop 64 ∧
    input.one_time_key.val = packet.one_time_key.val.drop 64 ∧
    input.pq_key.val = packet.pq_key.val.drop 64 ∧
    pqxdh.validate_init_kex input = .ok (.Ok verified)

def EdStored (packet : registration.InitPacket) (before : registration.InitEd25519Verification) : Prop :=
  match before.stage with
  | .PqKey => True
  | .PreKey => before.pq_key.val = packet.pq_key.val.drop 64
  | .OneTimeKey => before.pq_key.val = packet.pq_key.val.drop 64 ∧
      before.pre_key.val = packet.pre_key.val.drop 64

def Metadata (packet : registration.InitPacket) : registration.InitAuthentication → Prop
  | .HashRequested before => before.packet = packet
  | .MldsaVerificationRequested before => before.state.packet = packet
  | .Ed25519VerificationRequested before => before.state.packet = packet ∧ EdStored packet before
  | .ServerFingerprintRequested before => Credential packet before.registration
  | .BeaconFingerprintRequested before => Credential packet before.registration
  | .Accepted accepted => Credential packet accepted.registration
  | .Rejected => True

private theorem ed_metadata (packet : registration.InitPacket) (before : registration.InitEd25519Verification)
    (opened : Opened) (after : registration.InitAuthentication)
    (prior : Metadata packet (.Ed25519VerificationRequested before))
    (run : before.resume opened = .ok after) : Metadata packet after := by
  obtain ⟨result, actual, progress⟩ := init_ed_resume_refines before opened
  have facts : edProgress before opened after := (RustM.ok.inj (actual.symm.trans run)) ▸ progress
  cases after
  all_goals simp only [edProgress] at facts
  case Rejected => trivial
  case Ed25519VerificationRequested next =>
    obtain ⟨bytes, _reply, suffix, stateSame, _key, transition⟩ := facts
    refine ⟨(congrArg (fun state => state.packet) stateSame).trans prior.1, ?_⟩
    rcases transition with ⟨oldStage, nextStage, _pre, pq⟩ | ⟨oldStage, nextStage, pre, pq⟩
    · have openedPq : bytes.val = packet.pq_key.val.drop 64 := by
        simpa only [edSignedBytes, oldStage, prior.1] using suffix
      simpa only [EdStored, nextStage] using pq.trans openedPq
    · have storedPq : before.pq_key.val = packet.pq_key.val.drop 64 := by
        simpa only [Metadata, EdStored, oldStage] using prior.2
      have openedPre : bytes.val = packet.pre_key.val.drop 64 := by
        simpa only [edSignedBytes, oldStage, prior.1] using suffix
      simpa only [EdStored, nextStage] using And.intro (congrArg Subtype.val pq |>.trans storedPq) (pre.trans openedPre)
  case ServerFingerprintRequested next =>
    obtain ⟨bytes, _reply, suffix, oldStage, _state, key, keyBytes, validation⟩ := facts
    have stored : before.pq_key.val = packet.pq_key.val.drop 64 ∧
        before.pre_key.val = packet.pre_key.val.drop 64 := by
      simpa only [Metadata, EdStored, oldStage] using prior.2
    have openedOneTime : bytes.val = packet.one_time_key.val.drop 64 := by
      simpa only [edSignedBytes, oldStage, prior.1] using suffix
    exact ⟨⟨before.state.packet.identity_key, before.pre_key, key, before.pq_key⟩,
      congrArg registration.InitPacket.identity_key prior.1, stored.2,
      keyBytes.trans openedOneTime, stored.1, validation⟩

theorem step_metadata (packet : registration.InitPacket) {before after : registration.InitAuthentication}
    {event : Event} (edge : Step before event after) (prior : Metadata packet before) : Metadata packet after := by
  cases edge with
  | ed25519 before opened after run => exact ed_metadata packet before opened after prior run
  | hash before reply after run =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ True.intro
      | some digest =>
          obtain ⟨next, resumed, packetSame, _pin, _digest, _input⟩ := init_hash_success before digest
          exact (RustM.ok.inj (resumed.symm.trans run)) ▸
            (show Metadata packet (.MldsaVerificationRequested next) from packetSame.trans prior)
  | mldsa before verified after run =>
      obtain ⟨result, resumed, outcome⟩ := init_mldsa_exact before verified
      have facts : initMldsaOutcome before verified after := (RustM.ok.inj (resumed.symm.trans run)) ▸ outcome
      cases after
      all_goals simp only [initMldsaOutcome] at facts
      case Rejected => trivial
      case Ed25519VerificationRequested next =>
        obtain ⟨_verified, _tag, stateSame, stage, _key⟩ := facts
        exact ⟨by simpa only [Metadata, stateSame] using prior,
          by simp only [EdStored, stage]⟩
  | serverFingerprint before reply after run =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ True.intro
      | some fingerprint =>
          obtain ⟨next, resumed, _state, registrationSame, _binding, _key, _fingerprint⟩ :=
            init_server_fingerprint_exact before fingerprint
          exact (RustM.ok.inj (resumed.symm.trans run)) ▸
            (show Metadata packet (.BeaconFingerprintRequested next) from
              by simpa only [Metadata, registrationSame] using prior)
  | beaconFingerprint before reply after run =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ True.intro
      | some fingerprint =>
          obtain ⟨accepted, resumed, registrationSame, _pin, _digest, _identity, _fingerprint, _ad⟩ :=
            init_beacon_fingerprint_exact before fingerprint
          exact (RustM.ok.inj (resumed.symm.trans run)) ▸
            (show Metadata packet (.Accepted accepted) from
              by simpa only [Metadata, registrationSame] using prior)

theorem run_metadata (packet : registration.InitPacket) {start final : registration.InitAuthentication}
    {events : List Event} (run : Run start events final) (prior : Metadata packet start) : Metadata packet final := by
  induction run with
  | refl => exact prior
  | step previous edge ih => exact step_metadata packet edge ih

theorem accepted_credential (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) : Credential packet accepted.registration := by
  obtain ⟨initial, started, run⟩ := execution
  obtain ⟨before, began, packetSame, _pin, _input⟩ := begin_init_exact pin packet
  have initialMetadata : Metadata packet initial :=
    (RustM.ok.inj (began.symm.trans started)) ▸
      (show Metadata packet (.HashRequested before) from packetSame)
  exact run_metadata packet run initialMetadata

end BeaconcryptCore.Refinement.RegistrationCredentialMetadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationCredentialMetadata.step_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCredentialMetadata.step_metadata
/-- info: 'BeaconcryptCore.Refinement.RegistrationCredentialMetadata.run_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCredentialMetadata.run_metadata
/-- info: 'BeaconcryptCore.Refinement.RegistrationCredentialMetadata.accepted_credential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCredentialMetadata.accepted_credential
