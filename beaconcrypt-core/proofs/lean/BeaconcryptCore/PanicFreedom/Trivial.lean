import BeaconcryptCore.Extraction.Funs

/-! Definitionally total constructors, accessors, and derived copies. Every declaration has its full universally quantified extracted type. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open beaconcrypt_core

namespace BeaconcryptCore.PanicFreedom.Trivial

theorem commitment_CommitmentTranscript_as_bytes_total (self : commitment.CommitmentTranscript) :
    ∃ result, commitment.CommitmentTranscript.as_bytes self = ok result := ⟨_, rfl⟩

theorem commitment_CommitmentTranscript_as_mut_bytes_total (self : commitment.CommitmentTranscript) :
    ∃ result, commitment.CommitmentTranscript.as_mut_bytes self = ok result := ⟨_, rfl⟩

theorem pqxdh_concrete_InitialRatchetKdfPending_impl_request_total (self : pqxdh.concrete.InitialRatchetKdfPending) :
    ∃ result, pqxdh.concrete.InitialRatchetKdfPending.impl.request self = ok result := ⟨_, rfl⟩

theorem pqxdh_concrete_InitialRatchetKdfResponse_from_bytes_total (bytes : Array Std.U8 64#usize) :
    ∃ result, pqxdh.concrete.InitialRatchetKdfResponse.from_bytes bytes = ok result := ⟨_, rfl⟩

theorem pqxdh_concrete_InitialRatchetKdfResponse_as_bytes_total (self : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, pqxdh.concrete.InitialRatchetKdfResponse.as_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_SymmetricRatchetKdfRequest_new_total (input : Array Std.U8 32#usize) :
    ∃ result, ratchet.SymmetricRatchetKdfRequest.new input = ok result := ⟨_, rfl⟩

theorem ratchet_control_SequenceCache_empty_total  :
    ∃ result, ratchet.control.SequenceCache.empty  = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetChain_from_bytes_total (bytes : Array Std.U8 32#usize) :
    ∃ result, ratchet.RatchetChain.from_bytes bytes = ok result := ⟨_, rfl⟩

theorem pqxdh_InitialRatchetChains_into_parts_total (self : pqxdh.InitialRatchetChains) :
    ∃ result, pqxdh.InitialRatchetChains.into_parts self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationError_Insts_CoreCloneClone_clone_total (self : pqxdh.RegistrationError) :
    ∃ result, pqxdh.RegistrationError.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerBinding_Insts_CoreCloneClone_clone_total (self : pqxdh.ServerBinding) :
    ∃ result, pqxdh.ServerBinding.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconStartInputs_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconStartInputs) :
    ∃ result, pqxdh.BeaconStartInputs.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconCoins_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconCoins) :
    ∃ result, pqxdh.BeaconCoins.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_Insts_CoreCloneClone_clone_total (self : pqxdh.InitKex) :
    ∃ result, pqxdh.InitKex.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_from_encoded_total (identity_key : Array Std.U8 33#usize) (prekey : Array Std.U8 34#usize)
  (one_time_key : Array Std.U8 34#usize) (pq_key : Array Std.U8 1185#usize) :
    ∃ result, pqxdh.InitKex.from_encoded identity_key prekey one_time_key pq_key = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_impl_identity_key_total (self : pqxdh.InitKex) :
    ∃ result, pqxdh.InitKex.impl.identity_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_impl_prekey_total (self : pqxdh.InitKex) :
    ∃ result, pqxdh.InitKex.impl.prekey self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_impl_one_time_key_total (self : pqxdh.InitKex) :
    ∃ result, pqxdh.InitKex.impl.one_time_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitKex_impl_pq_key_total (self : pqxdh.InitKex) :
    ∃ result, pqxdh.InitKex.impl.pq_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_VerifiedInitKex_Insts_CoreCloneClone_clone_total (self : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_VerifiedInitKex_impl_beacon_identity_public_key_total (self : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.impl.beacon_identity_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_VerifiedInitKex_impl_beacon_prekey_public_key_total (self : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.impl.beacon_prekey_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_VerifiedInitKex_impl_beacon_one_time_public_key_total (self : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.impl.beacon_one_time_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_VerifiedInitKex_impl_beacon_pq_public_key_total (self : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.impl.beacon_pq_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationId_Insts_CoreCloneClone_clone_total (self : pqxdh.RegistrationId) :
    ∃ result, pqxdh.RegistrationId.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationId_as_bytes_total (self : pqxdh.RegistrationId) :
    ∃ result, pqxdh.RegistrationId.as_bytes self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationStatus_Insts_CoreCloneClone_clone_total (self : pqxdh.RegistrationStatus) :
    ∃ result, pqxdh.RegistrationStatus.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconFresh_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconFresh) :
    ∃ result, pqxdh.BeaconFresh.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconFresh_new_total (expected_server_binding : pqxdh.ServerBinding) :
    ∃ result, pqxdh.BeaconFresh.new expected_server_binding = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconFresh_server_key_id_total (self : pqxdh.BeaconFresh) :
    ∃ result, pqxdh.BeaconFresh.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconFresh_impl_expected_server_binding_total (self : pqxdh.BeaconFresh) :
    ∃ result, pqxdh.BeaconFresh.impl.expected_server_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconInitSent_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconInitSent) :
    ∃ result, pqxdh.BeaconInitSent.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconInitSent_server_key_id_total (self : pqxdh.BeaconInitSent) :
    ∃ result, pqxdh.BeaconInitSent.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconInitSent_impl_expected_server_binding_total (self : pqxdh.BeaconInitSent) :
    ∃ result, pqxdh.BeaconInitSent.impl.expected_server_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconStart_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconStart) :
    ∃ result, pqxdh.BeaconStart.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_RootKeyInput_as_bytes_total (self : pqxdh.RootKeyInput) :
    ∃ result, pqxdh.RootKeyInput.as_bytes self = ok result := ⟨_, rfl⟩

theorem pqxdh_RootKeyInput_as_mut_bytes_total (self : pqxdh.RootKeyInput) :
    ∃ result, pqxdh.RootKeyInput.as_mut_bytes self = ok result := ⟨_, rfl⟩

theorem pqxdh_RatchetInitialization_Insts_CoreCloneClone_clone_total (self : pqxdh.RatchetInitialization) :
    ∃ result, pqxdh.RatchetInitialization.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_RatchetInitialization_impl_send_offset_total (self : pqxdh.RatchetInitialization) :
    ∃ result, pqxdh.RatchetInitialization.impl.send_offset self = ok result := ⟨_, rfl⟩

theorem pqxdh_RatchetInitialization_impl_receive_offset_total (self : pqxdh.RatchetInitialization) :
    ∃ result, pqxdh.RatchetInitialization.impl.receive_offset self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitialRatchetChains_impl_send_chain_total (self : pqxdh.InitialRatchetChains) :
    ∃ result, pqxdh.InitialRatchetChains.impl.send_chain self = ok result := ⟨_, rfl⟩

theorem pqxdh_InitialRatchetChains_impl_receive_chain_total (self : pqxdh.InitialRatchetChains) :
    ∃ result, pqxdh.InitialRatchetChains.impl.receive_chain self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_server_key_id_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_impl_server_binding_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.impl.server_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_impl_assigned_key_id_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.impl.assigned_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_impl_root_key_input_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.impl.root_key_input self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_root_key_input_mut_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.root_key_input_mut self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconRegistrationCandidate_impl_associated_data_total (self : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.BeaconRegistrationCandidate.impl.associated_data self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationKeyIdBinding_Insts_CoreCloneClone_clone_total (self : pqxdh.RegistrationKeyIdBinding) :
    ∃ result, pqxdh.RegistrationKeyIdBinding.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_RegistrationKeyIdBinding_as_bytes_total (self : pqxdh.RegistrationKeyIdBinding) :
    ∃ result, pqxdh.RegistrationKeyIdBinding.as_bytes self = ok result := ⟨_, rfl⟩

theorem pqxdh_AuthenticatedBeaconRegistration_server_binding_total (self : pqxdh.AuthenticatedBeaconRegistration) :
    ∃ result, pqxdh.AuthenticatedBeaconRegistration.server_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_AuthenticatedBeaconRegistration_server_key_id_total (self : pqxdh.AuthenticatedBeaconRegistration) :
    ∃ result, pqxdh.AuthenticatedBeaconRegistration.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_AuthenticatedBeaconRegistration_assigned_key_id_total (self : pqxdh.AuthenticatedBeaconRegistration) :
    ∃ result, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconEstablished_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconEstablished) :
    ∃ result, pqxdh.BeaconEstablished.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconEstablished_server_key_id_total (self : pqxdh.BeaconEstablished) :
    ∃ result, pqxdh.BeaconEstablished.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconEstablished_impl_server_binding_total (self : pqxdh.BeaconEstablished) :
    ∃ result, pqxdh.BeaconEstablished.impl.server_binding self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconEstablished_impl_assigned_key_id_total (self : pqxdh.BeaconEstablished) :
    ∃ result, pqxdh.BeaconEstablished.impl.assigned_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconAborted_Insts_CoreCloneClone_clone_total (self : pqxdh.BeaconAborted) :
    ∃ result, pqxdh.BeaconAborted.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconAborted_new_total (server_key_id : Std.U64) :
    ∃ result, pqxdh.BeaconAborted.new server_key_id = ok result := ⟨_, rfl⟩

theorem pqxdh_BeaconAborted_impl_server_key_id_total (self : pqxdh.BeaconAborted) :
    ∃ result, pqxdh.BeaconAborted.impl.server_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_beacon_abort_candidate_total (candidate : pqxdh.BeaconRegistrationCandidate) :
    ∃ result, pqxdh.beacon_abort_candidate candidate = ok result := ⟨_, rfl⟩

theorem pqxdh_beacon_abort_init_total (state : pqxdh.BeaconInitSent) :
    ∃ result, pqxdh.beacon_abort_init state = ok result := ⟨_, rfl⟩

theorem pqxdh_beacon_abort_fresh_total (state : pqxdh.BeaconFresh) :
    ∃ result, pqxdh.beacon_abort_fresh state = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerState_Insts_CoreCloneClone_clone_total (self : pqxdh.ServerState) :
    ∃ result, pqxdh.ServerState.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerState_new_total (last_key_id : Std.U64) :
    ∃ result, pqxdh.ServerState.new last_key_id = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerState_impl_last_key_id_total (self : pqxdh.ServerState) :
    ∃ result, pqxdh.ServerState.impl.last_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerCoins_Insts_CoreCloneClone_clone_total (self : pqxdh.ServerCoins) :
    ∃ result, pqxdh.ServerCoins.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_PendingServerRegistration_impl_registration_id_total (self : pqxdh.PendingServerRegistration) :
    ∃ result, pqxdh.PendingServerRegistration.impl.registration_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_PendingServerRegistration_impl_beacon_identity_public_key_total (self : pqxdh.PendingServerRegistration) :
    ∃ result, pqxdh.PendingServerRegistration.impl.beacon_identity_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_PendingServerRegistration_impl_root_key_input_total (self : pqxdh.PendingServerRegistration) :
    ∃ result, pqxdh.PendingServerRegistration.impl.root_key_input self = ok result := ⟨_, rfl⟩

theorem pqxdh_PendingServerRegistration_root_key_input_mut_total (self : pqxdh.PendingServerRegistration) :
    ∃ result, pqxdh.PendingServerRegistration.root_key_input_mut self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_key_id_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_beacon_identity_public_key_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.beacon_identity_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_server_identity_public_key_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_server_identity_key_id_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_ephemeral_public_key_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_kem_ciphertext_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext self = ok result := ⟨_, rfl⟩

theorem pqxdh_ServerRegistrationCandidate_impl_associated_data_total (self : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.ServerRegistrationCandidate.impl.associated_data self = ok result := ⟨_, rfl⟩

theorem pqxdh_KeyIdAvailability_Insts_CoreCloneClone_clone_total (self : pqxdh.KeyIdAvailability) :
    ∃ result, pqxdh.KeyIdAvailability.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem pqxdh_server_commit_total (candidate : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.server_commit candidate = ok result := ⟨_, rfl⟩

theorem pqxdh_server_abort_candidate_total (candidate : pqxdh.ServerRegistrationCandidate) :
    ∃ result, pqxdh.server_abort_candidate candidate = ok result := ⟨_, rfl⟩

theorem ratchet_control_RatchetState_impl_send_sequence_total (self : ratchet.control.RatchetState) :
    ∃ result, ratchet.control.RatchetState.impl.send_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_control_RatchetState_impl_receive_sequence_total (self : ratchet.control.RatchetState) :
    ∃ result, ratchet.control.RatchetState.impl.receive_sequence self = ok result := ⟨_, rfl⟩

theorem ratchet_control_RatchetState_receive_cache_len_total (self : ratchet.control.RatchetState) :
    ∃ result, ratchet.control.RatchetState.receive_cache_len self = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_impl_send_chain_total {SendChain : Type} {ReceiveChain : Type} {Material : Type}
  (self : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) :
    ∃ result, ratchet.refined.RefinedRatchet.impl.send_chain (SendChain := SendChain) (ReceiveChain := ReceiveChain) (Material := Material) self = ok result := ⟨_, rfl⟩

theorem ratchet_refined_RefinedRatchet_impl_receive_chain_total {SendChain : Type} {ReceiveChain : Type} {Material : Type}
  (self : ratchet.refined.RefinedRatchet SendChain ReceiveChain Material) :
    ∃ result, ratchet.refined.RefinedRatchet.impl.receive_chain (SendChain := SendChain) (ReceiveChain := ReceiveChain) (Material := Material) self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetNonce_from_bytes_total (bytes : Array Std.U8 12#usize) :
    ∃ result, ratchet.RatchetNonce.from_bytes bytes = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKey_from_bytes_total (bytes : Array Std.U8 32#usize) :
    ∃ result, ratchet.RatchetKey.from_bytes bytes = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKdfResponse_as_bytes_total (self : ratchet.RatchetKdfResponse) :
    ∃ result, ratchet.RatchetKdfResponse.as_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetChain_as_bytes_total (self : ratchet.RatchetChain) :
    ∃ result, ratchet.RatchetChain.as_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_control_SendKey_unavailable_total  :
    ∃ result, ratchet.control.SendKey.unavailable  = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_SendKdf_impl_request_total {Context : Type} (self : ratchet.concrete.SendKdf Context) :
    ∃ result, ratchet.concrete.SendKdf.impl.request (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_SendKdf_cancel_total {Context : Type} (self : ratchet.concrete.SendKdf Context) :
    ∃ result, ratchet.concrete.SendKdf.cancel (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_SendSeal_impl_sequence_total {Context : Type} (self : ratchet.concrete.SendSeal Context) :
    ∃ result, ratchet.concrete.SendSeal.impl.sequence (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_SendSeal_impl_material_total {Context : Type} (self : ratchet.concrete.SendSeal Context) :
    ∃ result, ratchet.concrete.SendSeal.impl.material (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_SendSeal_impl_context_total {Context : Type} (self : ratchet.concrete.SendSeal Context) :
    ∃ result, ratchet.concrete.SendSeal.impl.context (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_receive_rejected_total {Context : Type} (kernel : ratchet.concrete.ConcreteRatchetKernel)
  (context : Context) :
    ∃ result, ratchet.concrete.receive_rejected (Context := Context) kernel context = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ReceiveKdf_impl_request_total {Context : Type} (self : ratchet.concrete.ReceiveKdf Context) :
    ∃ result, ratchet.concrete.ReceiveKdf.impl.request (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ReceiveKdf_cancel_total {Context : Type} (self : ratchet.concrete.ReceiveKdf Context) :
    ∃ result, ratchet.concrete.ReceiveKdf.cancel (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ReceiveOpen_impl_context_total {Context : Type} (self : ratchet.concrete.ReceiveOpen Context) :
    ∃ result, ratchet.concrete.ReceiveOpen.impl.context (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_concrete_ReceiveOpen_reject_total {Context : Type} (self : ratchet.concrete.ReceiveOpen Context) :
    ∃ result, ratchet.concrete.ReceiveOpen.reject (Context := Context) self = ok result := ⟨_, rfl⟩

theorem ratchet_control_finish_restore_total (restore : ratchet.control.RatchetRestore) :
    ∃ result, ratchet.control.finish_restore restore = ok result := ⟨_, rfl⟩

theorem ratchet_control_SequenceCache_Insts_CoreCloneClone_clone_total (self : ratchet.control.SequenceCache) :
    ∃ result, ratchet.control.SequenceCache.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_RatchetState_Insts_CoreCloneClone_clone_total (self : ratchet.control.RatchetState) :
    ∃ result, ratchet.control.RatchetState.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_SendKey_Insts_CoreCloneClone_clone_total (self : ratchet.control.SendKey) :
    ∃ result, ratchet.control.SendKey.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_SendKey_is_available_total (self : ratchet.control.SendKey) :
    ∃ result, ratchet.control.SendKey.is_available self = ok result := ⟨_, rfl⟩

theorem ratchet_control_SendAdvance_Insts_CoreCloneClone_clone_total (self : ratchet.control.SendAdvance) :
    ∃ result, ratchet.control.SendAdvance.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_SendFinish_Insts_CoreCloneClone_clone_total (self : ratchet.control.SendFinish) :
    ∃ result, ratchet.control.SendFinish.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceivePlan_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceivePlan) :
    ∃ result, ratchet.control.ReceivePlan.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveTargetAdvance_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveTargetAdvance) :
    ∃ result, ratchet.control.ReceiveTargetAdvance.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveAdvance_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveAdvance) :
    ∃ result, ratchet.control.ReceiveAdvance.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveDisposition_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveDisposition) :
    ∃ result, ratchet.control.ReceiveDisposition.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveFinish_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveFinish) :
    ∃ result, ratchet.control.ReceiveFinish.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveRemoval_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveRemoval) :
    ∃ result, ratchet.control.ReceiveRemoval.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveFinishWithRemoval_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveFinishWithRemoval) :
    ∃ result, ratchet.control.ReceiveFinishWithRemoval.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_RatchetRestore_Insts_CoreCloneClone_clone_total (self : ratchet.control.RatchetRestore) :
    ∃ result, ratchet.control.RatchetRestore.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_ReceiveRestoreStep_Insts_CoreCloneClone_clone_total (self : ratchet.control.ReceiveRestoreStep) :
    ∃ result, ratchet.control.ReceiveRestoreStep.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_PeerRatchetState_Insts_CoreCloneClone_clone_total (self : ratchet.control.PeerRatchetState) :
    ∃ result, ratchet.control.PeerRatchetState.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_control_PeerSendAdvance_Insts_CoreCloneClone_clone_total (self : ratchet.control.PeerSendAdvance) :
    ∃ result, ratchet.control.PeerSendAdvance.Insts.CoreCloneClone.clone self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetChain_into_bytes_total (self : ratchet.RatchetChain) :
    ∃ result, ratchet.RatchetChain.into_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKey_as_bytes_total (self : ratchet.RatchetKey) :
    ∃ result, ratchet.RatchetKey.as_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKey_into_bytes_total (self : ratchet.RatchetKey) :
    ∃ result, ratchet.RatchetKey.into_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetNonce_as_bytes_total (self : ratchet.RatchetNonce) :
    ∃ result, ratchet.RatchetNonce.as_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetNonce_into_bytes_total (self : ratchet.RatchetNonce) :
    ∃ result, ratchet.RatchetNonce.into_bytes self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetMaterial_from_parts_total (key : ratchet.RatchetKey) (nonce : ratchet.RatchetNonce) :
    ∃ result, ratchet.RatchetMaterial.from_parts key nonce = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetMaterial_impl_key_total (self : ratchet.RatchetMaterial) :
    ∃ result, ratchet.RatchetMaterial.impl.key self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetMaterial_impl_nonce_total (self : ratchet.RatchetMaterial) :
    ∃ result, ratchet.RatchetMaterial.impl.nonce self = ok result := ⟨_, rfl⟩

theorem ratchet_SymmetricRatchetKdfRequest_impl_input_total (self : ratchet.SymmetricRatchetKdfRequest) :
    ∃ result, ratchet.SymmetricRatchetKdfRequest.impl.input self = ok result := ⟨_, rfl⟩

theorem ratchet_SymmetricRatchetKdfRequest_impl_info_total (self : ratchet.SymmetricRatchetKdfRequest) :
    ∃ result, ratchet.SymmetricRatchetKdfRequest.impl.info self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKdfResponse_from_bytes_total (bytes : Array Std.U8 76#usize) :
    ∃ result, ratchet.RatchetKdfResponse.from_bytes bytes = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKdfOutput_impl_key_total (self : ratchet.RatchetKdfOutput) :
    ∃ result, ratchet.RatchetKdfOutput.impl.key self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKdfOutput_impl_next_chain_total (self : ratchet.RatchetKdfOutput) :
    ∃ result, ratchet.RatchetKdfOutput.impl.next_chain self = ok result := ⟨_, rfl⟩

theorem ratchet_RatchetKdfOutput_impl_nonce_total (self : ratchet.RatchetKdfOutput) :
    ∃ result, ratchet.RatchetKdfOutput.impl.nonce self = ok result := ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.Trivial
