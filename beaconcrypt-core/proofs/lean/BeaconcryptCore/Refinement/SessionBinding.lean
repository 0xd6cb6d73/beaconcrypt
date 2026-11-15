-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.TranscriptAuthInputs
import BeaconcryptCore.Model.Pqxdh.SessionTranscript

/-!
The pending binding retains the exact published request and the selected Server pin. Final AD exists only after the transcript hash continuation succeeds. Completed and restored bindings retain context87 followed by the exact transcript digest; primitive hash authenticity and trusted persistence integrity remain external obligations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.SessionBinding

/-- The authoritative context outside the digest is independent of the current KDF labels. -/
def boundAssociatedData (transcriptHash : Pqxdh.Bytes) : Pqxdh.Bytes :=
  Pqxdh.SessionTranscript.associatedData transcriptHash

/-- Pin construction preserves the exact classical binding and mandatory Server ML key. -/
theorem server_pin_refines (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array Std.U8 1952#usize) :
    ∃ result, session.ServerAuthenticationPin.new binding publicKey = ok result ∧
      result.binding = binding ∧ result.public_key = publicKey := by
  exact ⟨_, rfl, rfl, rfl⟩

/-- Reading or copying a pin exposes the same complete selected owner metadata. -/
theorem server_pin_observers (pin : session.ServerAuthenticationPin) :
    session.ServerAuthenticationPin.impl.binding pin = ok pin.binding ∧
      session.ServerAuthenticationPin.impl.public_key pin = ok pin.public_key ∧
      session.ServerAuthenticationPin.Insts.CoreCloneClone.clone pin = ok pin := by
  exact ⟨rfl, rfl, rfl⟩

/-- Pending state preserves complete signed request buffers without constructing provisional AD. -/
theorem registration_new_refines (pin : session.ServerAuthenticationPin)
    (initHash : Std.Array Std.U8 64#usize) (fields : authentication.OwnedInitFields) :
    ∃ result, session.RegistrationBinding.new pin initHash fields = ok result ∧
      result.server_pin = pin ∧ result.init_hash = initHash ∧ result.init_fields = fields := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Pending authentication reads the same retained request digest and pin. -/
theorem registration_observers (pending : session.RegistrationBinding) :
    session.RegistrationBinding.impl.init_hash pending = ok pending.init_hash ∧
      session.RegistrationBinding.impl.server_pin pending = ok pending.server_pin := by
  exact ⟨rfl, rfl⟩

/-- Matching an owner requires its numeric identity, classical key and exact ML public key. -/
abbrev sameServerPin (left right : session.ServerAuthenticationPin) : Prop :=
  left.binding.identity_key_id = right.binding.identity_key_id ∧
    absBytes left.binding.identity_public_key = absBytes right.binding.identity_public_key ∧
    absBytes left.public_key = absBytes right.public_key

/-- The exact pin comparison has no credential-membership or fingerprint shortcut. -/
theorem matches_server_refines (pending : session.RegistrationBinding)
    (current : session.ServerAuthenticationPin) :
    pending.matches_server current = ok (decide (sameServerPin pending.server_pin current)) := by
  simp [session.RegistrationBinding.matches_server, array_eq_abs, sameServerPin]
  split_ifs <;> simp_all

/-- A completed registration's AD agrees with the digest returned for its retained transcript. -/
def registrationConsistent (completed : session.CompletedRegistrationBinding) : Prop :=
  absBytes completed.associated_data = boundAssociatedData (absBytes completed.session_transcript_hash)

/-- An established session uses the same complete AD for every record. -/
def sessionConsistent (established : session.SessionBinding) : Prop :=
  absBytes established.associated_data = boundAssociatedData (absBytes established.session_transcript_hash)

/-- A successful AD-hash reply completes the retained request with its exact digest and fixed context. -/
theorem complete_refines (pending : session.RegistrationBinding)
    (transcriptHash : Std.Array Std.U8 64#usize) :
    ∃ result, pending.complete transcriptHash = ok result ∧
      result.server_pin = pending.server_pin ∧ result.init_hash = pending.init_hash ∧
      result.beacon_identity_public_key.val = (List.range (32#usize).val).map
        (fun index => pending.init_fields.identity_key.val[index + 1]!) ∧
      result.session_transcript_hash = transcriptHash ∧ registrationConsistent result := by
  obtain ⟨identity, identityRun, identityBytes⟩ :=
    TranscriptAuthInputsRefinement.identity_public_key_exact pending.init_fields
  obtain ⟨ad, adRun, adBytes⟩ :=
    TranscriptAuthInputsRefinement.assemble_associated_data_abs transcriptHash
  refine ⟨⟨pending.server_pin, pending.init_hash, identity, transcriptHash, ad⟩,
    ?_, rfl, rfl, identityBytes, rfl, ?_⟩
  · simp [session.RegistrationBinding.complete, identityRun, adRun]
  · simpa [registrationConsistent, boundAssociatedData] using adBytes

/-- Completed registration copies the same raw identity that was retained with the request. -/
theorem complete_identity (pending : session.RegistrationBinding)
    (digest : Std.Array Std.U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (resumed : pending.complete digest = ok completed) :
    authentication.OwnedInitFields.identity_public_key pending.init_fields = ok completed.beacon_identity_public_key := by
  obtain ⟨expected, expectedRun, _pin, _initHash, identityBytes, _hash, _consistent⟩ := complete_refines pending digest
  have same : expected = completed := RustM.ok.inj (expectedRun.symm.trans resumed)
  obtain ⟨key, keyRun, keyBytes⟩ := TranscriptAuthInputsRefinement.identity_public_key_exact pending.init_fields
  have keySame : key = completed.beacon_identity_public_key := Subtype.ext
    (keyBytes.trans ((congrArg (fun value : session.CompletedRegistrationBinding => value.beacon_identity_public_key.val) same).symm.trans identityBytes).symm)
  exact keySame ▸ keyRun

/-- Finishing preserves all completed record metadata and its consistency. -/
theorem finish_refines (completed : session.CompletedRegistrationBinding) (assignedId : Std.U64) :
    ∃ result, completed.finish assignedId = ok result ∧
      result.server_binding = completed.server_pin.binding ∧ result.assigned_key_id = assignedId ∧
      result.beacon_identity_public_key = completed.beacon_identity_public_key ∧
      result.session_transcript_hash = completed.session_transcript_hash ∧
      result.associated_data = completed.associated_data ∧
      (registrationConsistent completed → sessionConsistent result) := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun h => h⟩

/-- Trusted restoration rebuilds the authoritative context around the exact persisted digest. -/
theorem trusted_metadata_refines (server : pqxdh.ServerBinding) (assignedId : Std.U64)
    (beaconIdentity : Std.Array Std.U8 32#usize) (transcriptHash : Std.Array Std.U8 64#usize) :
    ∃ result, session.SessionBinding.from_trusted_metadata server assignedId beaconIdentity
        transcriptHash = ok result ∧
      result.server_binding = server ∧ result.assigned_key_id = assignedId ∧
      result.beacon_identity_public_key = beaconIdentity ∧
      result.session_transcript_hash = transcriptHash ∧ sessionConsistent result := by
  obtain ⟨ad, adRun, adBytes⟩ := TranscriptAuthInputsRefinement.assemble_associated_data_abs transcriptHash
  refine ⟨⟨server, assignedId, beaconIdentity, transcriptHash, ad⟩, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp [session.SessionBinding.from_trusted_metadata, adRun]
  · simpa [sessionConsistent, boundAssociatedData] using adBytes

/-- Records, routing and persistence all observe the same established binding. -/
theorem session_observers (established : session.SessionBinding) :
    session.SessionBinding.impl.server_binding established = ok established.server_binding ∧
      session.SessionBinding.impl.assigned_key_id established = ok established.assigned_key_id ∧
      session.SessionBinding.impl.beacon_identity_public_key established = ok established.beacon_identity_public_key ∧
      session.SessionBinding.impl.session_transcript_hash established = ok established.session_transcript_hash ∧
      session.SessionBinding.impl.associated_data established = ok established.associated_data ∧
      session.SessionBinding.Insts.CoreCloneClone.clone established = ok established := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.SessionBinding

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.server_pin_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.server_pin_refines

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.server_pin_observers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.server_pin_observers

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.registration_new_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.registration_new_refines

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.registration_observers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.registration_observers

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

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.session_observers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.session_observers

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.complete_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.complete_refines

/-- info: 'BeaconcryptCore.Refinement.SessionBinding.complete_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.SessionBinding.complete_identity
