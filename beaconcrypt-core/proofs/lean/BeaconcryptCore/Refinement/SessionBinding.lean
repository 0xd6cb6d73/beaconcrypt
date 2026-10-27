-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.TranscriptAuth

/-!
The extracted session boundary retains the selected server pin, request digest and final record associated data. Its semantic specification uses the existing ideal identity/domain prefix and ordered fingerprint extension. These facts do not authenticate primitive replies or persistence metadata.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.SessionBinding

/-- The protocol's ordered identities/domains followed by the supplied server and beacon fingerprints. -/
def boundAssociatedData (serverIdentity beaconIdentity serverFingerprint beaconFingerprint : Pqxdh.Bytes) :
    Pqxdh.Bytes :=
  Pqxdh.TranscriptAuth.fillAssociatedData (Pqxdh.assocData serverIdentity beaconIdentity)
    serverFingerprint beaconFingerprint

/-- Pin construction retains all supplied identity, ML-key and fingerprint bytes. -/
theorem server_pin_refines (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array Std.U8 1952#usize) (fingerprint : Std.Array Std.U8 64#usize) :
    ∃ result, session.ServerAuthenticationPin.new binding publicKey fingerprint = ok result ∧
      result.binding = binding ∧ result.public_key = publicKey ∧ result.fingerprint = fingerprint := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Reading or copying a pin exposes the same complete selected owner metadata. -/
theorem server_pin_observers (pin : session.ServerAuthenticationPin) :
    session.ServerAuthenticationPin.impl.binding pin = ok pin.binding ∧
      session.ServerAuthenticationPin.impl.public_key pin = ok pin.public_key ∧
      session.ServerAuthenticationPin.impl.fingerprint pin = ok pin.fingerprint ∧
      session.ServerAuthenticationPin.Insts.CoreCloneClone.clone pin = ok pin := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every newly retained request carries exactly its input provenance and the final populated AD. -/
theorem registration_new_refines (pin : session.ServerAuthenticationPin)
    (initHash : Std.Array Std.U8 64#usize) (beaconIdentity : Std.Array Std.U8 32#usize)
    (beaconFingerprint : Std.Array Std.U8 64#usize) :
    ∃ result, session.RegistrationBinding.new pin initHash beaconIdentity beaconFingerprint = ok result ∧
      result.server_pin = pin ∧ result.init_hash = initHash ∧
      result.beacon_identity_public_key = beaconIdentity ∧
      result.beacon_fingerprint = beaconFingerprint ∧
      absBytes result.associated_data = boundAssociatedData
        (absBytes pin.binding.identity_public_key) (absBytes beaconIdentity)
        (absBytes pin.fingerprint) (absBytes beaconFingerprint) := by
  obtain ⟨base, baseRun, baseBytes⟩ := build_associated_data_abs
    pin.binding.identity_public_key beaconIdentity
  obtain ⟨ad, adRun, adBytes⟩ := TranscriptAuthInputsRefinement.bind_associated_data_abs
    base pin.fingerprint beaconFingerprint
  refine ⟨⟨pin, initHash, beaconIdentity, beaconFingerprint, ad⟩, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp [session.RegistrationBinding.new, baseRun, adRun]
  · simpa [boundAssociatedData, baseBytes] using adBytes

/-- Pending authentication and record operations read the same retained request and final AD. -/
theorem registration_observers (pending : session.RegistrationBinding) :
    session.RegistrationBinding.impl.init_hash pending = ok pending.init_hash ∧
      session.RegistrationBinding.impl.server_pin pending = ok pending.server_pin ∧
      session.RegistrationBinding.impl.associated_data pending = ok pending.associated_data := by
  exact ⟨rfl, rfl, rfl⟩

/-- Matching an owner requires its numeric identity, classical key, ML key and fingerprint. -/
abbrev sameServerPin (left right : session.ServerAuthenticationPin) : Prop :=
  left.binding.identity_key_id = right.binding.identity_key_id ∧
    absBytes left.binding.identity_public_key = absBytes right.binding.identity_public_key ∧
    absBytes left.public_key = absBytes right.public_key ∧
    absBytes left.fingerprint = absBytes right.fingerprint

/-- The full owner comparison has no unverified membership or hash-equality shortcut. -/
theorem matches_server_refines (pending : session.RegistrationBinding)
    (current : session.ServerAuthenticationPin) :
    pending.matches_server current = ok (decide (sameServerPin pending.server_pin current)) := by
  simp [session.RegistrationBinding.matches_server, array_eq_abs, sameServerPin]
  split_ifs
  all_goals simp_all

/-- A retained request's AD agrees with its own selected identities and fingerprints. -/
def registrationConsistent (pending : session.RegistrationBinding) : Prop :=
  absBytes pending.associated_data = boundAssociatedData
    (absBytes pending.server_pin.binding.identity_public_key)
    (absBytes pending.beacon_identity_public_key) (absBytes pending.server_pin.fingerprint)
    (absBytes pending.beacon_fingerprint)

/-- An established session's AD agrees with its retained identities and fingerprints. -/
def sessionConsistent (established : session.SessionBinding) : Prop :=
  absBytes established.associated_data = boundAssociatedData
    (absBytes established.server_binding.identity_public_key)
    (absBytes established.beacon_identity_public_key) (absBytes established.server_fingerprint)
    (absBytes established.beacon_fingerprint)

/-- Finishing preserves all retained record metadata and validity for every represented request. -/
theorem finish_refines (pending : session.RegistrationBinding) (assignedId : Std.U64) :
    ∃ result, pending.finish assignedId = ok result ∧
      result.server_binding = pending.server_pin.binding ∧ result.assigned_key_id = assignedId ∧
      result.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      result.server_fingerprint = pending.server_pin.fingerprint ∧
      result.beacon_fingerprint = pending.beacon_fingerprint ∧
      result.associated_data = pending.associated_data ∧
      (registrationConsistent pending → sessionConsistent result) := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => h⟩

/-- Reconstruction preserves supplied metadata and recomputes the protocol AD, without asserting its provenance. -/
theorem trusted_metadata_refines (server : pqxdh.ServerBinding) (assignedId : Std.U64)
    (beaconIdentity : Std.Array Std.U8 32#usize)
    (serverFingerprint beaconFingerprint : Std.Array Std.U8 64#usize) :
    ∃ result, session.SessionBinding.from_trusted_metadata server assignedId beaconIdentity
        serverFingerprint beaconFingerprint = ok result ∧
      result.server_binding = server ∧ result.assigned_key_id = assignedId ∧
      result.beacon_identity_public_key = beaconIdentity ∧
      result.server_fingerprint = serverFingerprint ∧ result.beacon_fingerprint = beaconFingerprint ∧
      sessionConsistent result := by
  obtain ⟨base, baseRun, baseBytes⟩ := build_associated_data_abs server.identity_public_key beaconIdentity
  obtain ⟨ad, adRun, adBytes⟩ := TranscriptAuthInputsRefinement.bind_associated_data_abs
    base serverFingerprint beaconFingerprint
  refine ⟨⟨server, assignedId, beaconIdentity, serverFingerprint, beaconFingerprint, ad⟩,
    ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [session.SessionBinding.from_trusted_metadata, baseRun, adRun]
  · simpa [sessionConsistent, boundAssociatedData, baseBytes] using adBytes

/-- Record routing, AD reads and snapshot metadata all observe the same established binding. -/
theorem session_observers (established : session.SessionBinding) :
    session.SessionBinding.impl.server_binding established = ok established.server_binding ∧
      session.SessionBinding.impl.assigned_key_id established = ok established.assigned_key_id ∧
      session.SessionBinding.impl.beacon_identity_public_key established =
        ok established.beacon_identity_public_key ∧
      session.SessionBinding.impl.server_fingerprint established = ok established.server_fingerprint ∧
      session.SessionBinding.impl.beacon_fingerprint established = ok established.beacon_fingerprint ∧
      session.SessionBinding.impl.associated_data established = ok established.associated_data ∧
      session.SessionBinding.Insts.CoreCloneClone.clone established = ok established := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.SessionBinding

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.server_pin_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.server_pin_refines
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.registration_new_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.registration_new_refines
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.matches_server_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.matches_server_refines
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.finish_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.finish_refines
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.trusted_metadata_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.trusted_metadata_refines

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.server_pin_observers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.server_pin_observers
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.registration_observers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.registration_observers
/-- info: 'BeaconcryptCore.Refinement.SessionBinding.session_observers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.session_observers
