-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.ServerTransactionRefinement
import BeaconcryptCore.Refinement.PqxdhSurface

/-! Allocation and response-input metadata for the current extracted candidate. The former identity-derived AD publication correspondence has been retired. Current AD source correspondence is proved by SessionTranscript, SessionBinding, RegistrationAd, RegistrationRecords and RegistrationPublication; no identity-derived historical AD is equated to the current session transcript. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ServerTransactionRefinement

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.ServerPublicationRefinement

structure CandidateMetadataRefines (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (identity kemCipher ephemeral : Pqxdh.Bytes) (candidate : pqxdh.ServerRegistrationCandidate) : Prop where
  previousCounter : candidate.previous_state.last_key_id.val = entry.n
  nextCounter : candidate.next_state.last_key_id.val = entry.n + 1
  assignedId : candidate.key_id.val = entry.n + 1
  beaconIdentity : absBytes candidate.beacon_identity_public_key = identity
  serverIdentity : absBytes candidate.server_identity_public_key = c.edPub entry.ikSk
  serverId : candidate.server_identity_key_id.val = entry.sid
  ephemeralKey : absBytes candidate.ephemeral_public_key = ephemeral
  kemCiphertext : absBytes candidate.kem_ciphertext = kemCipher

/-- Available preparation derives every candidate field from extracted allocation and associated-data construction. -/
theorem prepare_candidate_metadata_refines (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (identity kemCipher ephemeral : Pqxdh.Bytes)
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (hserverId : binding.identity_key_id.val = entry.sid)
    (hidentity : absBytes pending.beacon_identity_public_key = identity)
    (hkem : absBytes pending.kem_ciphertext = kemCipher)
    (hephem : absBytes pending.ephemeral_public_key = ephemeral)
    (hmax : entry.n ≠ Pqxdh.maxKeyId) :
    ∃ candidate, pqxdh.server_prepare_commit state pending binding .Available = ok (.Ok candidate) ∧
      CandidateMetadataRefines c entry identity kemCipher ephemeral candidate := by
  have hne : state.last_key_id ≠ core.num.U64.MAX :=
    fun heq => hmax (hcounter.symm.trans (congrArg UScalar.val heq))
  obtain ⟨next, _allocated, hnext, hprepare⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.available_server_key_id_candidate_shape
      state pending binding hne hbinding
  exact ⟨_, hprepare, ⟨hcounter, by simpa only [hcounter] using hnext,
    by simpa only [hcounter] using hnext, hidentity, hserverIdentity, hserverId, hephem, hkem⟩⟩

theorem prepare_binding_changed (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability)
    (hmismatch : pending.server_binding.identity_key_id ≠ binding.identity_key_id ∨
      pending.server_binding.identity_public_key ≠ binding.identity_public_key) :
    pqxdh.server_prepare_commit state pending binding availability = ok (.Err .IdentityMismatch) :=
  BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
    state pending binding availability hmismatch

theorem prepare_allocation_rejections_refine (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (identity root kemCipher ephemeral application : Pqxdh.Bytes) (sealed : Bool)
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (havail : availability = .Occupied ↔ (entry.peers.lookup (entry.n + 1)).isSome) :
    (entry.n = Pqxdh.maxKeyId →
      pqxdh.server_prepare_commit state pending binding availability = ok (.Err .KeyIdExhausted) ∧
      idealPublication c entry identity root kemCipher ephemeral application sealed =
        (.rejected .keyIdExhausted, entry)) ∧
    (entry.n ≠ Pqxdh.maxKeyId → (entry.peers.lookup (entry.n + 1)).isSome →
      pqxdh.server_prepare_commit state pending binding availability = ok (.Err .KeyIdCollision) ∧
      idealPublication c entry identity root kemCipher ephemeral application sealed =
        (.rejected .keyIdCollision, entry)) := by
  obtain ⟨hexhausted, hcollision, _⟩ := server_prepare_commit_metadata_refines c entry state pending
    binding availability hcounter hbinding hserverIdentity havail
  exact ⟨fun hmax => ⟨hexhausted hmax, by simp [idealPublication, Pqxdh.serverEmit, hmax]⟩,
    fun hmax hoccupied => ⟨hcollision hmax hoccupied,
      by simp [idealPublication, Pqxdh.serverEmit, hmax, hoccupied]⟩⟩

end BeaconcryptCore.Refinement.ServerPublicationRefinement

/-- info: 'BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_candidate_metadata_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_candidate_metadata_refines

/-- info: 'BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_binding_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_binding_changed

/-- info: 'BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_allocation_rejections_refine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.ServerPublicationRefinement.prepare_allocation_rejections_refine
