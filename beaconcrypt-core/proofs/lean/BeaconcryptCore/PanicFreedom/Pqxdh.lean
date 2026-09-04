import BeaconcryptCore.Refinement.PqxdhCommitment
import BeaconcryptCore.Refinement.PqxdhProtocol

/-! Panic freedom of PQXDH parsing, registration, and commitment operations, including rejected inputs. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom

theorem tag_sign_key_ok (key : Std.Array Std.U8 32#usize) :
    ∃ result, pqxdh.tag_sign_key key = ok result :=
  (tag_sign_key_abs key).imp (fun _ h => h.1)

theorem tag_x25519_key_ok (role : Std.U8) (key : Std.Array Std.U8 32#usize) :
    ∃ result, pqxdh.tag_x25519_key role key = ok result :=
  (tag_x25519_key_abs role key).imp (fun _ h => h.1)

theorem tag_mlkem768_key_ok (key : Std.Array Std.U8 1184#usize) :
    ∃ result, pqxdh.tag_mlkem768_key key = ok result :=
  (tag_mlkem768_key_abs key).imp (fun _ h => h.1)

theorem untag_sign_key_ok (encoded : Std.Array Std.U8 33#usize) :
    ∃ result, pqxdh.untag_sign_key encoded = ok result :=
  (untag_sign_key_abs encoded).elim
    (fun h => h.elim (fun key hk => ⟨.Some key, hk.1⟩)) (fun h => ⟨.None, h.1⟩)

theorem untag_x25519_key_ok (encoded : Std.Array Std.U8 34#usize) (role : Std.U8) :
    ∃ result, pqxdh.untag_x25519_key encoded role = ok result :=
  (untag_x25519_key_abs encoded role).elim
    (fun h => h.elim (fun key hk => ⟨.Some key, hk.1⟩)) (fun h => ⟨.None, h.1⟩)

theorem untag_mlkem768_key_ok (encoded : Std.Array Std.U8 1185#usize) :
    ∃ result, pqxdh.untag_mlkem768_key encoded = ok result :=
  (untag_mlkem768_key_abs encoded).elim
    (fun h => h.elim (fun key hk => ⟨.Some key, hk.1⟩)) (fun h => ⟨.None, h.1⟩)

theorem build_associated_data_ok (server beacon : Std.Array Std.U8 32#usize) :
    ∃ result, pqxdh.build_associated_data server beacon = ok result :=
  (build_associated_data_abs server beacon).imp (fun _ h => h.1)

theorem registration_id_ok (registration : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.registration_id registration = ok result :=
  (registration_id_abs registration).imp (fun _ h => h.1)

theorem registration_key_id_binding_ok (keyId : Std.U64) :
    ∃ result, pqxdh.registration_key_id_binding keyId = ok result :=
  (registration_key_id_binding_abs keyId).imp (fun _ h => h.1)

theorem commitment_encode_u64_le_ok (value : Std.U64) :
    ∃ result, commitment.encode_u64_le value = ok result :=
  (commitment_encode_u64_le_abs value).imp (fun _ h => h.1)

theorem build_commitment_transcript_ok (key : Std.Array Std.U8 32#usize)
    (nonce : Std.Array Std.U8 12#usize) (associatedData : Std.Array Std.U8 153#usize)
    (tag : Std.Array Std.U8 16#usize) (sequence senderId : Std.U64) :
    ∃ result, commitment.build_commitment_transcript key nonce associatedData tag sequence senderId = ok result :=
  (build_commitment_transcript_abs key nonce associatedData tag sequence senderId).imp (fun _ h => h.1)

theorem build_root_key_input_ok (secrets : pqxdh.PqxdhSharedSecrets) :
    ∃ result, pqxdh.build_root_key_input secrets = ok result :=
  (Classical.em _).elim
    (fun h => ((build_root_key_input_abs secrets).1 h).elim (fun root hr => ⟨.Ok root, hr.1⟩))
    (fun h => ⟨.Err .InvalidDhOutput, (build_root_key_input_abs secrets).2 h⟩)

/-- Starting a registration is total for arbitrary supplied public-key bytes. -/
theorem beacon_start_ok (state : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) :
    ∃ result, pqxdh.beacon_start state inputs coins = ok result :=
  (tag_sign_key_ok inputs.identity_public_key).elim fun _ hid =>
  (tag_x25519_key_ok pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key).elim fun _ hpre =>
  (tag_x25519_key_ok pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key).elim fun _ hot =>
  (tag_mlkem768_key_ok inputs.pq_public_key).elim fun _ hpq =>
  by simp [pqxdh.beacon_start, hid, hpre, hot, hpq]

/-- Every encoded key bundle either validates or returns an ordinary Rust error. -/
theorem validate_init_kex_ok (message : pqxdh.InitKex) :
    ∃ result, pqxdh.validate_init_kex message = ok result :=
  (untag_sign_key_ok message.identity_key).elim fun identity hid =>
  (untag_x25519_key_ok message.prekey pqxdh.KEY_ROLE_PREKEY).elim fun prekey hpre =>
  (untag_x25519_key_ok message.one_time_key pqxdh.KEY_ROLE_ONE_TIME).elim fun oneTime hot =>
  (untag_mlkem768_key_ok message.pq_key).elim fun pq hpq => by
    cases identity <;> cases prekey <;> cases oneTime <;> cases pq <;>
      simp [pqxdh.validate_init_kex, hid, hpre, hot, hpq]

/-- Finish preparation is total even for identity mismatches or zero DH outputs. -/
theorem beacon_prepare_finish_ok (state : pqxdh.BeaconInitSent)
    (inputs : pqxdh.BeaconFinishInputs) :
    ∃ result, pqxdh.beacon_prepare_finish state inputs = ok result :=
  (build_root_key_input_ok inputs.shared_secrets).elim fun root hroot =>
  (build_associated_data_ok state.expected_server_binding.identity_public_key
    state.beacon_identity_public_key).elim fun _ had => by
    cases root <;>
      by_cases hid : absBytes state.expected_server_binding.identity_public_key =
        absBytes inputs.response_server_identity <;>
      simp [pqxdh.beacon_prepare_finish, array_eq_abs, hid, hroot, had]

/-- Authentication rejects mismatching sender IDs or binding bytes without panicking. -/
theorem authenticate_registration_key_id_binding_ok (candidate : pqxdh.BeaconRegistrationCandidate)
    (senderId : Std.U64) (binding : Std.Array Std.U8 8#usize) :
    ∃ result, pqxdh.authenticate_registration_key_id_binding candidate senderId binding = ok result :=
  (registration_key_id_binding_ok candidate.assigned_key_id).elim fun expected hexpected => by
    by_cases hid : senderId = candidate.server_binding.identity_key_id <;>
      by_cases hbinding : absBytes binding = absBytes expected.bytes <;>
      simp [pqxdh.authenticate_registration_key_id_binding,
        pqxdh.BeaconRegistrationCandidate.key_id_binding, hid, hexpected, array_eq_abs, hbinding]

/-- Registration admission has a normal return for both fresh and consumed registrations. -/
theorem server_accept_ok (state : pqxdh.ServerState) (registration : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding)
    (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets) :
    ∃ result, pqxdh.server_accept state registration status binding coins secrets = ok result :=
  (build_root_key_input_ok secrets).elim fun root hroot =>
  (registration_id_ok registration).elim fun _ hid => by
    cases root <;> cases status <;>
      simp [pqxdh.server_accept, pqxdh.validate_registration_status, hroot, hid]

/-- Key-ID exhaustion is returned as an ordinary error instead of overflowing the counter. -/
theorem server_next_key_id_ok (state : pqxdh.ServerState) :
    ∃ result, pqxdh.server_next_key_id state = ok result :=
  if h : state.last_key_id = core.num.U64.MAX then
    ⟨.Err .KeyIdExhausted, by simp [pqxdh.server_next_key_id, h]⟩
  else
    (u64_add_one state.last_key_id (by
      have hne : state.last_key_id.val ≠ 2 ^ 64 - 1 :=
        fun hv => h (UScalar.eq_of_val_eq (hv.trans u64_max_val.symm))
      scalar_tac)).elim fun id hid =>
      ⟨.Ok id, by simp [pqxdh.server_next_key_id, h, hid.1]⟩

/-- Commit preparation is total for every binding, allocation verdict, and current counter. -/
theorem server_prepare_commit_ok (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability) :
    ∃ result, pqxdh.server_prepare_commit state pending binding availability = ok result :=
  (server_next_key_id_ok state).elim fun id hid =>
  (build_associated_data_ok binding.identity_public_key pending.beacon_identity_public_key).elim
    fun _ had => by
      cases id <;> cases availability <;>
        by_cases hsender : pending.server_binding.identity_key_id = binding.identity_key_id <;>
        by_cases hidentity : absBytes pending.server_binding.identity_public_key =
          absBytes binding.identity_public_key <;>
        simp [pqxdh.server_prepare_commit, hsender, array_eq_abs, hidentity, hid, had]

theorem is_all_zero_ok (bytes : Std.Array Std.U8 32#usize) :
    ∃ result, pqxdh.is_all_zero bytes = ok result :=
  ⟨_, is_all_zero_abs bytes⟩

theorem verified_registration_id_ok (registration : pqxdh.VerifiedInitKex) :
    ∃ result, pqxdh.VerifiedInitKex.registration_id registration = ok result :=
  registration_id_ok registration

theorem established_peer_clone_ok (peer : pqxdh.EstablishedPeer) :
    ∃ result, pqxdh.EstablishedPeer.Insts.CoreCloneClone.clone peer = ok result :=
  ⟨peer, rfl⟩

theorem established_peer_eq_ok (peer other : pqxdh.EstablishedPeer) :
    ∃ result, pqxdh.EstablishedPeer.Insts.CoreCmpPartialEqEstablishedPeer.eq peer other = ok result := by
  by_cases hid : peer.key_id = other.key_id <;>
    by_cases hidentity : absBytes peer.identity_public_key = absBytes other.identity_public_key <;>
    simp [pqxdh.EstablishedPeer.Insts.CoreCmpPartialEqEstablishedPeer.eq, hid, array_eq_abs, hidentity]

theorem established_peer_ne_ok (peer other : pqxdh.EstablishedPeer) :
    ∃ result, pqxdh.EstablishedPeer.Insts.CoreCmpPartialEqEstablishedPeer.ne peer other = ok result :=
  (established_peer_eq_ok peer other).elim fun result hresult =>
    ⟨!result, by simp [pqxdh.EstablishedPeer.Insts.CoreCmpPartialEqEstablishedPeer.ne, hresult]⟩

end BeaconcryptCore.PanicFreedom
