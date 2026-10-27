-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.KeyAgreement
import BeaconcryptCore.PanicFreedom.RegistrationPublication

/-! Unconditional normal returns of the extracted peer owner and collection continuations, including arbitrary represented states and all rejected external replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.PeerOwnership

theorem Peer_from_trusted_parts_total {Ratchet : Type} (binding : session.SessionBinding) (ratchet : Ratchet) :
    ∃ result, peer.Peer.from_trusted_parts binding ratchet = ok result :=
  ⟨_, rfl⟩

theorem Peer_key_id_total {Ratchet : Type} (self : peer.Peer Ratchet) :
    ∃ result, self.key_id = ok result :=
  ⟨_, rfl⟩

theorem Peer_binding_total {Ratchet : Type} (self : peer.Peer Ratchet) :
    ∃ result, peer.Peer.impl.binding self = ok result :=
  ⟨_, rfl⟩

theorem Peer_ratchet_total {Ratchet : Type} (self : peer.Peer Ratchet) :
    ∃ result, peer.Peer.impl.ratchet self = ok result :=
  ⟨_, rfl⟩

theorem Peer_ratchet_mut_total {Ratchet : Type} (self : peer.Peer Ratchet) :
    ∃ result, self.ratchet_mut = ok result :=
  ⟨_, rfl⟩

theorem Peer_into_parts_total {Ratchet : Type} (self : peer.Peer Ratchet) :
    ∃ result, self.into_parts = ok result :=
  ⟨_, rfl⟩

theorem begin_registration_lookup_total (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) :
    ∃ result, peer.begin_registration_lookup control authenticated = ok result :=
  ⟨_, rfl⟩

theorem RegistrationLookup_request_total (self : peer.RegistrationLookup) :
    ∃ result, self.request = ok result :=
  BeaconcryptCore.PanicFreedom.registration_id_ok self.authenticated.registration

theorem RegistrationLookup_resume_total (self : peer.RegistrationLookup) (consumed : Bool) :
    ∃ result, self.resume consumed = ok result :=
  match consumed with
  | true => ⟨_, rfl⟩
  | false => by
    simpa [peer.RegistrationLookup.resume] using
      KeyAgreement.begin_server_agreement_total self.control .Fresh self.authenticated

theorem begin_registration_insert_total (accepted : agreement.ServerAgreement) :
    ∃ result, peer.begin_registration_insert accepted = ok result :=
  ⟨_, rfl⟩

theorem RegistrationInsert_request_total (self : peer.RegistrationInsert) :
    ∃ result, self.request = ok result :=
  ⟨_, rfl⟩

theorem RegistrationInsert_resume_total (self : peer.RegistrationInsert) (inserted : Bool) :
    ∃ result, self.resume inserted = ok result :=
  match inserted with
  | true => ⟨_, rfl⟩
  | false => ⟨_, rfl⟩

theorem begin_completion_lookup_total (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (registration : peer.ConsumedRegistration)
    (application : Slice Std.U8) :
    ∃ result, peer.begin_completion_lookup control pin registration application = ok result :=
  (BeaconcryptCore.PanicFreedom.server_next_key_id_ok control).elim fun next nextRun =>
    match next with
    | .Err _ => ⟨.Err control, by simp [peer.begin_completion_lookup, nextRun]⟩
    | .Ok key => ⟨.Ok ⟨control, pin, registration, application, key⟩,
        by simp [peer.begin_completion_lookup, nextRun]⟩

theorem CompletionLookup_request_total (self : peer.CompletionLookup) :
    ∃ result, self.request = ok result :=
  ⟨_, rfl⟩

theorem CompletionLookup_resume_total (self : peer.CompletionLookup) (occupied : Bool) :
    ∃ result, self.resume occupied = ok result :=
  match occupied with
  | false => by
    simpa [peer.CompletionLookup.resume] using
      RegistrationPublication.begin_server_completion_total self.control self.pin .Available
        self.registration.agreement self.application
  | true => by
    simpa [peer.CompletionLookup.resume] using
      RegistrationPublication.begin_server_completion_total self.control self.pin .Occupied
        self.registration.agreement self.application

theorem begin_peer_insert_total {Encoded : Type} (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) :
    ∃ result, peer.begin_peer_insert control published = ok result := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next
  · simp only [peer.begin_peer_insert, nextRun, registration.PublishedServerResponse.into_parts,
      pqxdh.ServerState.impl.last_key_id, peer.Peer.from_trusted_parts, bind_tc_ok]
    dsimp! only
    split <;> exact ⟨_, rfl⟩
  · exact ⟨.Err control, by simp [peer.begin_peer_insert, nextRun]⟩

theorem PeerInsert_request_total {Encoded : Type} (self : peer.PeerInsert Encoded) :
    ∃ result, self.request = ok result :=
  ⟨_, rfl⟩

theorem PeerInsert_into_parts_total {Encoded : Type} (self : peer.PeerInsert Encoded) :
    ∃ result, self.into_parts = ok result :=
  ⟨_, rfl⟩

theorem PublicationFinish_finish_total {Encoded : Type} (self : peer.PublicationFinish Encoded)
    (inserted : Bool) :
    ∃ result, self.finish inserted = ok result :=
  match inserted with
  | true => ⟨_, rfl⟩
  | false => ⟨_, rfl⟩

theorem PublishedPeer_into_parts_total {Encoded : Type} (self : peer.PublishedPeer Encoded) :
    ∃ result, self.into_parts = ok result :=
  ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.PeerOwnership

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_from_trusted_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_from_trusted_parts_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_key_id_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_key_id_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_binding_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_binding_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_ratchet_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_ratchet_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_ratchet_mut_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_ratchet_mut_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.Peer_into_parts_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.begin_registration_lookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.begin_registration_lookup_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationLookup_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationLookup_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationLookup_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationLookup_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.begin_registration_insert_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.begin_registration_insert_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationInsert_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationInsert_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationInsert_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.RegistrationInsert_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.begin_completion_lookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.begin_completion_lookup_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.CompletionLookup_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.begin_peer_insert_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.begin_peer_insert_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_into_parts_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.PeerInsert_into_parts_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.PublicationFinish_finish_total' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.PublicationFinish_finish_total

/-- info: 'BeaconcryptCore.PanicFreedom.PeerOwnership.PublishedPeer_into_parts_total' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.PeerOwnership.PublishedPeer_into_parts_total
