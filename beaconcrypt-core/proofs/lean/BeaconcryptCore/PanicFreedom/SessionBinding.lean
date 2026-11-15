-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.SessionBinding
import BeaconcryptCore.Refinement.SessionTranscript

/-!
Every extracted session operation returns normally for arbitrary represented inputs. Constructor and owner-check certificates reuse their exact behavioral refinements; no valid-state, hash, signature or persistence premise is required.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.SessionBinding

theorem ServerAuthenticationPin_clone_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.Insts.CoreCloneClone.clone self = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_new_total (binding : pqxdh.ServerBinding) (public_key : Array Std.U8 1952#usize)
  :
    ∃ result, session.ServerAuthenticationPin.new binding public_key = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_binding_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.impl.binding self = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_public_key_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.impl.public_key self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_new_total (server_pin : session.ServerAuthenticationPin)
  (init_hash : Array Std.U8 64#usize)
  (fields : authentication.OwnedInitFields) :
    ∃ result, session.RegistrationBinding.new server_pin init_hash fields = ok result :=
  (BeaconcryptCore.Refinement.SessionBinding.registration_new_refines server_pin init_hash fields).imp (fun _ h => h.1)

theorem RegistrationBinding_init_hash_total (self : session.RegistrationBinding) :
    ∃ result, session.RegistrationBinding.impl.init_hash self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_server_pin_total (self : session.RegistrationBinding) :
    ∃ result, session.RegistrationBinding.impl.server_pin self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_matches_server_total (self : session.RegistrationBinding)
  (current : session.ServerAuthenticationPin) :
    ∃ result, session.RegistrationBinding.matches_server self current = ok result :=
  ⟨_, BeaconcryptCore.Refinement.SessionBinding.matches_server_refines self current⟩

theorem CompletedRegistrationBinding_finish_total (self : session.CompletedRegistrationBinding) (assigned_key_id : Std.U64) :
    ∃ result, session.CompletedRegistrationBinding.finish self assigned_key_id = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_clone_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.Insts.CoreCloneClone.clone self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_from_trusted_metadata_total (server_binding : pqxdh.ServerBinding) (assigned_key_id : Std.U64)
  (beacon_identity_public_key : Array Std.U8 32#usize)
  (session_transcript_hash : Array Std.U8 64#usize) :
    ∃ result, session.SessionBinding.from_trusted_metadata server_binding assigned_key_id beacon_identity_public_key session_transcript_hash = ok result :=
  (BeaconcryptCore.Refinement.SessionBinding.trusted_metadata_refines server_binding assigned_key_id beacon_identity_public_key session_transcript_hash).imp (fun _ h => h.1)

theorem SessionBinding_server_binding_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.server_binding self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_assigned_key_id_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.assigned_key_id self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_beacon_identity_public_key_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.beacon_identity_public_key self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_associated_data_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.associated_data self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_complete_total (self : session.RegistrationBinding)
    (digest : Array Std.U8 64#usize) :
    ∃ result, self.complete digest = ok result :=
  (BeaconcryptCore.Refinement.SessionBinding.complete_refines self digest).imp (fun _ h => h.1)

theorem RegistrationBinding_ad_transcript_total (self : session.RegistrationBinding)
    (response : authentication.AdResponseFields) :
    ∃ result, self.ad_transcript response = ok result := by
  obtain ⟨output, run⟩ := SessionTranscriptRefinement.build_record_ad_transcript_total
    ⟨self.init_fields.identity_key, self.init_fields.pre_key, self.init_fields.one_time_key, self.init_fields.pq_key⟩ response
  exact ⟨output, by simpa only [session.RegistrationBinding.ad_transcript, authentication.OwnedInitFields.fields, bind_tc_ok] using run⟩

theorem CompletedRegistrationBinding_observers_total (self : session.CompletedRegistrationBinding) :
    session.CompletedRegistrationBinding.impl.init_hash self = ok self.init_hash ∧
      session.CompletedRegistrationBinding.impl.server_pin self = ok self.server_pin ∧
      session.CompletedRegistrationBinding.impl.associated_data self = ok self.associated_data := ⟨rfl, rfl, rfl⟩

theorem SessionBinding_session_transcript_hash_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.session_transcript_hash self = ok result := ⟨_, rfl⟩

theorem CompletedRegistrationBinding_associated_data_total (self : session.CompletedRegistrationBinding) :
    ∃ result, session.CompletedRegistrationBinding.impl.associated_data self = ok result := ⟨_, rfl⟩

theorem CompletedRegistrationBinding_init_hash_total (self : session.CompletedRegistrationBinding) :
    ∃ result, session.CompletedRegistrationBinding.impl.init_hash self = ok result := ⟨_, rfl⟩

theorem CompletedRegistrationBinding_server_pin_total (self : session.CompletedRegistrationBinding) :
    ∃ result, session.CompletedRegistrationBinding.impl.server_pin self = ok result := ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.SessionBinding

/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_clone_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_clone_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_new_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_binding_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_binding_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_public_key_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_public_key_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_new_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_init_hash_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_init_hash_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_server_pin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_server_pin_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.CompletedRegistrationBinding_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.CompletedRegistrationBinding_finish_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_clone_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_clone_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_from_trusted_metadata_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_from_trusted_metadata_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_server_binding_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_server_binding_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_assigned_key_id_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_assigned_key_id_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_beacon_identity_public_key_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_beacon_identity_public_key_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_associated_data_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_associated_data_total
