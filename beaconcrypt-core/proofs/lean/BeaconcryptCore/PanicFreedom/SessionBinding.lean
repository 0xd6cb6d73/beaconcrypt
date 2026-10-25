-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.SessionBinding

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
  (fingerprint : Array Std.U8 64#usize) :
    ∃ result, session.ServerAuthenticationPin.new binding public_key fingerprint = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_binding_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.impl.binding self = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_public_key_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.impl.public_key self = ok result :=
  ⟨_, rfl⟩

theorem ServerAuthenticationPin_fingerprint_total (self : session.ServerAuthenticationPin) :
    ∃ result, session.ServerAuthenticationPin.impl.fingerprint self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_new_total (server_pin : session.ServerAuthenticationPin)
  (init_hash : Array Std.U8 64#usize)
  (beacon_identity_public_key : Array Std.U8 32#usize)
  (beacon_fingerprint : Array Std.U8 64#usize) :
    ∃ result, session.RegistrationBinding.new server_pin init_hash beacon_identity_public_key beacon_fingerprint = ok result :=
  (BeaconcryptCore.Refinement.SessionBinding.registration_new_refines server_pin init_hash beacon_identity_public_key beacon_fingerprint).imp (fun _ h => h.1)

theorem RegistrationBinding_init_hash_total (self : session.RegistrationBinding) :
    ∃ result, session.RegistrationBinding.impl.init_hash self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_server_pin_total (self : session.RegistrationBinding) :
    ∃ result, session.RegistrationBinding.impl.server_pin self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_associated_data_total (self : session.RegistrationBinding) :
    ∃ result, session.RegistrationBinding.impl.associated_data self = ok result :=
  ⟨_, rfl⟩

theorem RegistrationBinding_matches_server_total (self : session.RegistrationBinding)
  (current : session.ServerAuthenticationPin) :
    ∃ result, session.RegistrationBinding.matches_server self current = ok result :=
  ⟨_, BeaconcryptCore.Refinement.SessionBinding.matches_server_refines self current⟩

theorem RegistrationBinding_finish_total (self : session.RegistrationBinding) (assigned_key_id : Std.U64) :
    ∃ result, session.RegistrationBinding.finish self assigned_key_id = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_clone_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.Insts.CoreCloneClone.clone self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_from_trusted_metadata_total (server_binding : pqxdh.ServerBinding) (assigned_key_id : Std.U64)
  (beacon_identity_public_key : Array Std.U8 32#usize)
  (server_fingerprint : Array Std.U8 64#usize)
  (beacon_fingerprint : Array Std.U8 64#usize) :
    ∃ result, session.SessionBinding.from_trusted_metadata server_binding assigned_key_id beacon_identity_public_key server_fingerprint beacon_fingerprint = ok result :=
  (BeaconcryptCore.Refinement.SessionBinding.trusted_metadata_refines server_binding assigned_key_id beacon_identity_public_key server_fingerprint beacon_fingerprint).imp (fun _ h => h.1)

theorem SessionBinding_server_binding_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.server_binding self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_assigned_key_id_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.assigned_key_id self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_beacon_identity_public_key_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.beacon_identity_public_key self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_server_fingerprint_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.server_fingerprint self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_beacon_fingerprint_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.beacon_fingerprint self = ok result :=
  ⟨_, rfl⟩

theorem SessionBinding_associated_data_total (self : session.SessionBinding) :
    ∃ result, session.SessionBinding.impl.associated_data self = ok result :=
  ⟨_, rfl⟩

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
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_fingerprint_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.ServerAuthenticationPin_fingerprint_total
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
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_associated_data_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_associated_data_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_finish_total
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
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_server_fingerprint_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_server_fingerprint_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_beacon_fingerprint_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_beacon_fingerprint_total
/-- info: 'BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_associated_data_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.SessionBinding.SessionBinding_associated_data_total
