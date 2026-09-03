import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.Refinement.PqxdhConcreteSession

/-! Direct semantic counterparts of the raw-byte F* PQXDH lemmas. These statements require no primitive or ideal-protocol representation assumptions beyond their explicit data premises. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.PqxdhSurface

theorem bytes_eq_of_abs_eq {n : Std.Usize} {left right : Std.Array Std.U8 n}
    (h : absBytes left = absBytes right) : left = right :=
  Subtype.ext ((absBytes_inj_iff left right).mp h)

theorem untag_sign_key_of_parse (encoded : Std.Array Std.U8 33#usize) (key : Std.Array Std.U8 32#usize)
    (hparse : Pqxdh.parseSigTag (absBytes encoded) = some (absBytes key)) :
    pqxdh.untag_sign_key encoded = ok (.Some key) :=
  (untag_sign_key_abs encoded).elim
    (fun hex => hex.elim fun decoded hd => hd.1.trans
      (congrArg (fun k => ok (core.option.Option.Some k))
        (bytes_eq_of_abs_eq (Option.some.inj (hd.2.symm.trans hparse)))))
    (fun hn => by cases hn.2.symm.trans hparse)

theorem untag_x25519_key_of_parse (encoded : Std.Array Std.U8 34#usize)
    (role : Std.U8) (key : Std.Array Std.U8 32#usize)
    (hparse : Pqxdh.parseXTag (absByte role) (absBytes encoded) = some (absBytes key)) :
    pqxdh.untag_x25519_key encoded role = ok (.Some key) :=
  (untag_x25519_key_abs encoded role).elim
    (fun hex => hex.elim fun decoded hd => hd.1.trans
      (congrArg (fun k => ok (core.option.Option.Some k))
        (bytes_eq_of_abs_eq (Option.some.inj (hd.2.symm.trans hparse)))))
    (fun hn => by cases hn.2.symm.trans hparse)

theorem untag_mlkem768_key_of_parse (encoded : Std.Array Std.U8 1185#usize)
    (key : Std.Array Std.U8 1184#usize)
    (hparse : Pqxdh.parsePQTag (absBytes encoded) = some (absBytes key)) :
    pqxdh.untag_mlkem768_key encoded = ok (.Some key) :=
  (untag_mlkem768_key_abs encoded).elim
    (fun hex => hex.elim fun decoded hd => hd.1.trans
      (congrArg (fun k => ok (core.option.Option.Some k))
        (bytes_eq_of_abs_eq (Option.some.inj (hd.2.symm.trans hparse)))))
    (fun hn => by cases hn.2.symm.trans hparse)

theorem sign_key_tag_round_trip (key : Std.Array Std.U8 32#usize) :
    ∃ encoded, pqxdh.tag_sign_key key = ok encoded ∧ pqxdh.untag_sign_key encoded = ok (.Some key) :=
  (tag_sign_key_abs key).elim fun encoded h =>
    ⟨encoded, h.1, untag_sign_key_of_parse encoded key (by simp [h.2])⟩

theorem x25519_key_tag_round_trip (role : Std.U8) (key : Std.Array Std.U8 32#usize) :
    ∃ encoded, pqxdh.tag_x25519_key role key = ok encoded ∧
      pqxdh.untag_x25519_key encoded role = ok (.Some key) :=
  (tag_x25519_key_abs role key).elim fun encoded h =>
    ⟨encoded, h.1, untag_x25519_key_of_parse encoded role key (by simp [h.2])⟩

theorem mlkem768_key_tag_round_trip (key : Std.Array Std.U8 1184#usize) :
    ∃ encoded, pqxdh.tag_mlkem768_key key = ok encoded ∧ pqxdh.untag_mlkem768_key encoded = ok (.Some key) :=
  (tag_mlkem768_key_abs key).elim fun encoded h =>
    ⟨encoded, h.1, untag_mlkem768_key_of_parse encoded key (by simp [h.2])⟩

theorem untag_x25519_key_of_parse_none (encoded : Std.Array Std.U8 34#usize) (role : Std.U8)
    (hparse : Pqxdh.parseXTag (absByte role) (absBytes encoded) = none) :
    pqxdh.untag_x25519_key encoded role = ok .None :=
  (untag_x25519_key_abs encoded role).elim
    (fun hex => hex.elim fun _ hd => by cases hd.2.symm.trans hparse) (fun hn => hn.1)

/-- Every role mismatch is rejected, including exchanging the prekey and one-time-key fields. -/
theorem x25519_key_roles_are_enforced (key : Std.Array Std.U8 32#usize) (role other : Std.U8)
    (hne : role ≠ other) :
    ∃ encoded, pqxdh.tag_x25519_key role key = ok encoded ∧ pqxdh.untag_x25519_key encoded other = ok .None :=
  (tag_x25519_key_abs role key).elim fun encoded h =>
    ⟨encoded, h.1, untag_x25519_key_of_parse_none encoded other (by
      simp [h.2, Pqxdh.parseXTag, Pqxdh.tagX, show absByte role ≠ absByte other from fun h => hne (absByte_injective h)])⟩

/-- The five production algorithm and role markers have exact values and are pairwise distinct. -/
theorem key_type_and_role_markers_are_disjoint :
    pqxdh.SIGN_TYPE_ED25519 = 1#u8 ∧ pqxdh.KEM_TYPE_MLKEM768 = 3#u8 ∧
    pqxdh.KEM_TYPE_X25519 = 4#u8 ∧ pqxdh.KEY_ROLE_PREKEY = 128#u8 ∧ pqxdh.KEY_ROLE_ONE_TIME = 129#u8 ∧
    [pqxdh.SIGN_TYPE_ED25519, pqxdh.KEM_TYPE_MLKEM768, pqxdh.KEM_TYPE_X25519,
      pqxdh.KEY_ROLE_PREKEY, pqxdh.KEY_ROLE_ONE_TIME].Nodup := by
  simp [pqxdh.SIGN_TYPE_ED25519, pqxdh.KEM_TYPE_MLKEM768, pqxdh.KEM_TYPE_X25519,
    pqxdh.KEY_ROLE_PREKEY, pqxdh.KEY_ROLE_ONE_TIME]

/-- Every bundle constructed from raw public-key bytes validates to those exact inputs and retains the pinned binding. -/
theorem beacon_start_validates (state : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) :
    ∃ started, pqxdh.beacon_start state inputs coins = ok started ∧
      pqxdh.validate_init_kex started.message = ok (.Ok {
        beacon_identity_public_key := inputs.identity_public_key,
        beacon_prekey_public_key := inputs.prekey_public_key,
        beacon_one_time_public_key := coins.one_time_public_key,
        beacon_pq_public_key := inputs.pq_public_key }) ∧
      started.state.expected_server_binding = state.expected_server_binding ∧
      started.state.beacon_identity_public_key = inputs.identity_public_key :=
  (sign_key_tag_round_trip inputs.identity_public_key).elim fun identity hid =>
  (x25519_key_tag_round_trip pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key).elim fun prekey hpre =>
  (x25519_key_tag_round_trip pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key).elim fun oneTime hot =>
  (mlkem768_key_tag_round_trip inputs.pq_public_key).elim fun pq hpq =>
  ⟨{ state := { expected_server_binding := state.expected_server_binding,
                 beacon_identity_public_key := inputs.identity_public_key },
     message := { identity_key := identity, prekey := prekey, one_time_key := oneTime, pq_key := pq } },
    by simp [pqxdh.beacon_start, hid.1, hpre.1, hot.1, hpq.1],
    by simp [pqxdh.validate_init_kex, hid.2, hpre.2, hot.2, hpq.2], rfl, rfl⟩

/-- Byte-array equality in the extraction is the exact concrete array equality decision. -/
theorem byte_array_eq_exact {n : Std.Usize} (left right : Std.Array Std.U8 n) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 left right =
      ok (decide (left.val = right.val)) := by
  simp only [array_eq_abs, absBytes_inj_iff]

theorem byte_array_eq_of_ne {n : Std.Usize} (left right : Std.Array Std.U8 n)
    (hne : left ≠ right) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 left right = ok false := by
  simp [array_eq_abs, show absBytes left ≠ absBytes right from fun h => hne (bytes_eq_of_abs_eq h)]

/-- A changed response identity is rejected before any root construction. -/
theorem beacon_response_identity_mismatch_is_rejected
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (hne : state.expected_server_binding.identity_public_key ≠ inputs.response_server_identity) :
    pqxdh.beacon_prepare_finish state inputs = ok (.Err .IdentityMismatch) := by
  simp [pqxdh.beacon_prepare_finish, byte_array_eq_of_ne _ _ hne]

/-- The exact candidate or propagated root error, for every raw input with the pinned response key. -/
theorem beacon_successful_finish_preserves_binding_and_ad
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (hidentity : state.expected_server_binding.identity_public_key = inputs.response_server_identity) :
    ∃ rootResult ad,
      pqxdh.build_root_key_input inputs.shared_secrets = ok rootResult ∧
      pqxdh.build_associated_data state.expected_server_binding.identity_public_key
        state.beacon_identity_public_key = ok ad ∧
      pqxdh.beacon_prepare_finish state inputs = ok (match rootResult with
        | .Ok root => .Ok { server_binding := state.expected_server_binding, assigned_key_id := inputs.assigned_key_id, root_key_input := root, associated_data := ad }
        | .Err err => .Err err) :=
  (PanicFreedom.build_root_key_input_ok inputs.shared_secrets).elim fun rootResult hroot =>
  (PanicFreedom.build_associated_data_ok state.expected_server_binding.identity_public_key
      state.beacon_identity_public_key).elim fun ad had =>
  ⟨rootResult, ad, hroot, had, by
    cases rootResult <;> simp [pqxdh.beacon_prepare_finish, array_eq_abs, ← hidentity, hroot, had]⟩

/-- An exact assigned-ID prefix and pinned sender authenticate the unchanged candidate. -/
theorem exact_key_id_binding_authenticates (candidate : pqxdh.BeaconRegistrationCandidate) :
    ∃ binding, pqxdh.BeaconRegistrationCandidate.key_id_binding candidate = ok binding ∧
      pqxdh.authenticate_registration_key_id_binding candidate
        candidate.server_binding.identity_key_id binding.bytes = ok (.Ok { candidate }) :=
  (PanicFreedom.registration_key_id_binding_ok candidate.assigned_key_id).elim fun binding hb =>
    ⟨binding, hb, by simp [pqxdh.authenticate_registration_key_id_binding,
      pqxdh.BeaconRegistrationCandidate.key_id_binding, hb, array_eq_abs]⟩

theorem mismatched_authenticated_server_key_id_is_rejected
    (candidate : pqxdh.BeaconRegistrationCandidate) (sender : Std.U64)
    (binding : Std.Array Std.U8 8#usize)
    (hne : sender ≠ candidate.server_binding.identity_key_id) :
    pqxdh.authenticate_registration_key_id_binding candidate sender binding = ok (.Err .IdentityMismatch) := by
  simp [pqxdh.authenticate_registration_key_id_binding, hne]

theorem mismatched_key_id_binding_is_rejected (candidate : pqxdh.BeaconRegistrationCandidate)
    (authenticatedBinding : Std.Array Std.U8 8#usize) (expected : pqxdh.RegistrationKeyIdBinding)
    (hexpected : pqxdh.BeaconRegistrationCandidate.key_id_binding candidate = ok expected)
    (hne : authenticatedBinding ≠ expected.bytes) :
    pqxdh.authenticate_registration_key_id_binding candidate
      candidate.server_binding.identity_key_id authenticatedBinding = ok (.Err .KeyIdMismatch) := by
  simp [pqxdh.authenticate_registration_key_id_binding, hexpected, byte_array_eq_of_ne _ _ hne]

theorem beacon_commit_preserves_authenticated_ids (authenticated : pqxdh.AuthenticatedBeaconRegistration) :
    pqxdh.beacon_commit authenticated = ok {
      server_binding := authenticated.candidate.server_binding,
      assigned_key_id := authenticated.candidate.assigned_key_id } := rfl

theorem fresh_registration_status_is_accepted :
    pqxdh.validate_registration_status .Fresh = ok (.Ok ()) := rfl

theorem consumed_registration_status_is_rejected :
    pqxdh.validate_registration_status .Consumed = ok (.Err .RegistrationReplay) := rfl

theorem server_rejects_consumed_registration (state : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (binding : pqxdh.ServerBinding)
    (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets) :
    pqxdh.server_accept state registration .Consumed binding coins secrets = ok (.Err .RegistrationReplay) := rfl

/-- Fresh acceptance retains the entire active state and token inputs, or propagates precisely the root-input error. -/
theorem server_fresh_acceptance_shape (state : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (binding : pqxdh.ServerBinding)
    (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets) :
    ∃ rootResult registrationId,
      pqxdh.build_root_key_input secrets = ok rootResult ∧
      pqxdh.VerifiedInitKex.registration_id registration = ok registrationId ∧
      pqxdh.server_accept state registration .Fresh binding coins secrets = ok (match rootResult with
        | .Ok root => .Ok (state, { server_binding := binding, registration_id := registrationId, beacon_identity_public_key := registration.beacon_identity_public_key, ephemeral_public_key := coins.ephemeral_public_key, kem_ciphertext := coins.kem_ciphertext, root_key_input := root })
        | .Err err => .Err err) :=
  (PanicFreedom.build_root_key_input_ok secrets).elim fun rootResult hroot =>
  (PanicFreedom.registration_id_ok registration).elim fun registrationId hrid =>
    ⟨rootResult, registrationId, hroot, hrid, by
      cases rootResult <;> simp [pqxdh.server_accept, pqxdh.validate_registration_status, hroot, hrid]⟩

theorem server_abort_is_state_neutral (candidate : pqxdh.ServerRegistrationCandidate) :
    pqxdh.server_abort_candidate candidate = ok candidate.previous_state := rfl

theorem next_server_key_id_success (state : pqxdh.ServerState)
    (hne : state.last_key_id ≠ core.num.U64.MAX) :
    ∃ next, pqxdh.server_next_key_id state = ok (.Ok next) ∧ next.val = state.last_key_id.val + 1 :=
  (server_next_key_id_refines ⟨[], 0, state.last_key_id.val, [], []⟩ state rfl).2 (by
    intro h
    exact hne (Std.UScalar.eq_of_val_eq (h.trans (by decide))))

/-- Either changed binding field rejects commit preparation, independent of allocation availability. -/
theorem server_binding_mismatch_is_rejected (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (current : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability)
    (hmismatch : pending.server_binding.identity_key_id ≠ current.identity_key_id ∨
      pending.server_binding.identity_public_key ≠ current.identity_public_key) :
    pqxdh.server_prepare_commit state pending current availability = ok (.Err .IdentityMismatch) := by
  rcases hmismatch with hid | hkey
  · simp [pqxdh.server_prepare_commit, hid]
  · simp [pqxdh.server_prepare_commit, byte_array_eq_of_ne _ _ hkey]

theorem occupied_server_key_id_is_rejected (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (current : pqxdh.ServerBinding)
    (hne : state.last_key_id ≠ core.num.U64.MAX) (hbinding : pending.server_binding = current) :
    pqxdh.server_prepare_commit state pending current .Occupied = ok (.Err .KeyIdCollision) :=
  (next_server_key_id_success state hne).elim fun next hn => by
    simp [pqxdh.server_prepare_commit, hbinding, array_eq_abs, hn.1]

/-- Available allocation returns the exact unpublished candidate and the checked mathematical successor. -/
theorem available_server_key_id_candidate_shape (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (current : pqxdh.ServerBinding)
    (hne : state.last_key_id ≠ core.num.U64.MAX) (hbinding : pending.server_binding = current) :
    ∃ next ad,
      pqxdh.server_next_key_id state = ok (.Ok next) ∧ next.val = state.last_key_id.val + 1 ∧
      pqxdh.build_associated_data current.identity_public_key pending.beacon_identity_public_key = ok ad ∧
      pqxdh.server_prepare_commit state pending current .Available = ok (.Ok {
        previous_state := state, next_state := { last_key_id := next }, key_id := next,
        beacon_identity_public_key := pending.beacon_identity_public_key,
        server_identity_public_key := current.identity_public_key,
        server_identity_key_id := current.identity_key_id,
        ephemeral_public_key := pending.ephemeral_public_key, kem_ciphertext := pending.kem_ciphertext,
        associated_data := ad }) :=
  (next_server_key_id_success state hne).elim fun next hn =>
  (PanicFreedom.build_associated_data_ok current.identity_public_key pending.beacon_identity_public_key).elim fun ad had =>
    ⟨next, ad, hn.1, hn.2, had, by simp [pqxdh.server_prepare_commit, hbinding, array_eq_abs, hn.1, had]⟩

theorem chain_size_cast : Std.UScalar.cast .U8 32#usize = 32#u8 :=
  Std.UScalar.eq_of_val_eq (by simp_scalar)

theorem ratchet_initializations_are_complementary :
    pqxdh.beacon_ratchet_initialization = ok { send_offset := 32#u8, receive_offset := 0#u8 } ∧
    pqxdh.server_ratchet_initialization = ok { send_offset := 0#u8, receive_offset := 32#u8 } := by
  simp [pqxdh.beacon_ratchet_initialization, pqxdh.server_ratchet_initialization,
    pqxdh.BEACON_RATCHETS, pqxdh.SERVER_RATCHETS, pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift, chain_size_cast]

theorem candidate_ratchet_initializations_are_complementary
    (beacon : pqxdh.BeaconRegistrationCandidate) (server : pqxdh.ServerRegistrationCandidate) :
    pqxdh.BeaconRegistrationCandidate.ratchet_initialization beacon =
      ok { send_offset := 32#u8, receive_offset := 0#u8 } ∧
    pqxdh.ServerRegistrationCandidate.ratchet_initialization server =
      ok { send_offset := 0#u8, receive_offset := 32#u8 } := by
  simp [pqxdh.BeaconRegistrationCandidate.ratchet_initialization, pqxdh.ServerRegistrationCandidate.ratchet_initialization,
    pqxdh.BEACON_RATCHETS, pqxdh.SERVER_RATCHETS, pqxdh.RATCHET_CHAIN_SIZE,
    ratchet.RATCHET_CHAIN_SIZE, lift, chain_size_cast]

/-- Equality of all five raw shared secrets implies identical construction, including rejection. -/
theorem honest_roles_build_the_same_root (beacon server : pqxdh.PqxdhSharedSecrets)
    (h1 : beacon.dh1 = server.dh1) (h2 : beacon.dh2 = server.dh2)
    (h3 : beacon.dh3 = server.dh3) (h4 : beacon.dh4 = server.dh4)
    (hpq : beacon.kem_shared_secret = server.kem_shared_secret) :
    pqxdh.build_root_key_input beacon = pqxdh.build_root_key_input server :=
  congrArg pqxdh.build_root_key_input (by cases beacon; cases server; simp_all)

theorem honest_roles_build_the_same_associated_data
    (serverKey serverKey' beaconKey beaconKey' : Std.Array Std.U8 32#usize)
    (hserver : serverKey = serverKey') (hbeacon : beaconKey = beaconKey') :
    pqxdh.build_associated_data serverKey beaconKey = pqxdh.build_associated_data serverKey' beaconKey' := by
  simp only [hserver, hbeacon]

/-- Successful preparation derives the response-identity check and preserves every candidate input. -/
theorem beacon_prepare_finish_success_shape (state : pqxdh.BeaconInitSent)
    (inputs : pqxdh.BeaconFinishInputs) (candidate : pqxdh.BeaconRegistrationCandidate)
    (hsuccess : pqxdh.beacon_prepare_finish state inputs = ok (.Ok candidate)) :
    state.expected_server_binding.identity_public_key = inputs.response_server_identity ∧
    candidate.server_binding = state.expected_server_binding ∧
    candidate.assigned_key_id = inputs.assigned_key_id ∧
    pqxdh.build_root_key_input inputs.shared_secrets = ok (.Ok candidate.root_key_input) ∧
    pqxdh.build_associated_data state.expected_server_binding.identity_public_key
      state.beacon_identity_public_key = ok candidate.associated_data :=
  (PanicFreedom.build_root_key_input_ok inputs.shared_secrets).elim fun rootResult hroot =>
  (PanicFreedom.build_associated_data_ok state.expected_server_binding.identity_public_key
      state.beacon_identity_public_key).elim fun ad had => by
    by_cases hi : absBytes state.expected_server_binding.identity_public_key = absBytes inputs.response_server_identity
    · cases rootResult <;> simp_all [pqxdh.beacon_prepare_finish, array_eq_abs, bytes_eq_of_abs_eq hi]
      simp [← hsuccess]
    · simp [pqxdh.beacon_prepare_finish, array_eq_abs, hi] at hsuccess

theorem authenticated_registration_success_shape (candidate : pqxdh.BeaconRegistrationCandidate)
    (sender : Std.U64) (bound : Std.Array Std.U8 8#usize)
    (authenticated : pqxdh.AuthenticatedBeaconRegistration)
    (hsuccess : pqxdh.authenticate_registration_key_id_binding candidate sender bound = ok (.Ok authenticated)) :
    authenticated.candidate = candidate ∧ sender = candidate.server_binding.identity_key_id ∧
    ∃ expected, pqxdh.BeaconRegistrationCandidate.key_id_binding candidate = ok expected ∧ bound = expected.bytes :=
  (PanicFreedom.registration_key_id_binding_ok candidate.assigned_key_id).elim fun expected he => by
    by_cases hs : sender = candidate.server_binding.identity_key_id
    · by_cases hk : absBytes bound = absBytes expected.bytes
      · simp [pqxdh.authenticate_registration_key_id_binding, hs,
          pqxdh.BeaconRegistrationCandidate.key_id_binding, he, array_eq_abs, hk] at hsuccess
        exact ⟨congrArg pqxdh.AuthenticatedBeaconRegistration.candidate hsuccess.symm,
          hs, expected, he, bytes_eq_of_abs_eq hk⟩
      · simp [pqxdh.authenticate_registration_key_id_binding, hs,
          pqxdh.BeaconRegistrationCandidate.key_id_binding, he, array_eq_abs, hk] at hsuccess
    · simp [pqxdh.authenticate_registration_key_id_binding, hs] at hsuccess

theorem server_binding_ext (left right : pqxdh.ServerBinding)
    (hkey : left.identity_public_key = right.identity_public_key)
    (hid : left.identity_key_id = right.identity_key_id) : left = right := by
  cases left; cases right; simp_all

/-- Successful raw response checking and sender authentication derive the accepting binding; binding equality is not a premise. -/
theorem successful_beacon_acceptance_implies_server_binding_agreement
    (state : pqxdh.BeaconInitSent) (server : pqxdh.ServerRegistrationCandidate)
    (secrets : pqxdh.PqxdhSharedSecrets) (candidate : pqxdh.BeaconRegistrationCandidate)
    (bound : Std.Array Std.U8 8#usize) (authenticated : pqxdh.AuthenticatedBeaconRegistration)
    (hprepare : pqxdh.beacon_prepare_finish state {
      response_server_identity := server.server_identity_public_key,
      assigned_key_id := server.key_id, shared_secrets := secrets } = ok (.Ok candidate))
    (hauth : pqxdh.authenticate_registration_key_id_binding candidate server.server_identity_key_id
      bound = ok (.Ok authenticated)) :
    state.expected_server_binding = { identity_public_key := server.server_identity_public_key, identity_key_id := server.server_identity_key_id } ∧
    candidate.server_binding = state.expected_server_binding ∧
    authenticated.candidate = candidate ∧ candidate.assigned_key_id = server.key_id ∧
    pqxdh.beacon_commit authenticated = ok {
      server_binding := { identity_public_key := server.server_identity_public_key, identity_key_id := server.server_identity_key_id },
      assigned_key_id := server.key_id } := by
  have hp := beacon_prepare_finish_success_shape state _ candidate hprepare
  have ha := authenticated_registration_success_shape candidate _ bound authenticated hauth
  have hb : state.expected_server_binding = { identity_public_key := server.server_identity_public_key, identity_key_id := server.server_identity_key_id } :=
    server_binding_ext _ _ hp.1 ((congrArg pqxdh.ServerBinding.identity_key_id hp.2.1).symm.trans ha.2.1.symm)
  exact ⟨hb, hp.2.1, ha.1, hp.2.2.1, by simp [pqxdh.beacon_commit, ha.1, hp.2.1, hp.2.2.1, hb]⟩

/-- The F* honest-secret premise is exactly equality of all five concrete arrays. -/
theorem honest_shared_secrets_iff (beacon server : pqxdh.PqxdhSharedSecrets) :
    (beacon.dh1 = server.dh1 ∧ beacon.dh2 = server.dh2 ∧ beacon.dh3 = server.dh3 ∧
      beacon.dh4 = server.dh4 ∧ beacon.kem_shared_secret = server.kem_shared_secret) ↔ beacon = server := by
  cases beacon; cases server; simp only [pqxdh.PqxdhSharedSecrets.mk.injEq]

/-- The F* nonzero-DH premise is the exact conjunction of four extracted rejection checks returning false. -/
theorem valid_shared_secrets_iff (secrets : pqxdh.PqxdhSharedSecrets) :
    (pqxdh.is_all_zero secrets.dh1 = ok false ∧ pqxdh.is_all_zero secrets.dh2 = ok false ∧
      pqxdh.is_all_zero secrets.dh3 = ok false ∧ pqxdh.is_all_zero secrets.dh4 = ok false) ↔
      Pqxdh.dhNonZero (absDHs secrets) := by
  simp [is_all_zero_abs, Pqxdh.dhNonZero, absDHs]

/-- Complete raw registration execution under only the F* byte-agreement, pinned identity, nonzero-DH, and non-exhaustion premises. All successful phase equations are conclusions. -/
theorem conditional_honest_run_correspondence
    (beaconState : pqxdh.BeaconInitSent) (serverState : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (binding : pqxdh.ServerBinding)
    (coins : pqxdh.ServerCoins) (beaconSecrets serverSecrets : pqxdh.PqxdhSharedSecrets)
    (hcounter : serverState.last_key_id ≠ core.num.U64.MAX)
    (hidentity : registration.beacon_identity_public_key = beaconState.beacon_identity_public_key)
    (hpin : binding = beaconState.expected_server_binding)
    (hvalid : Pqxdh.dhNonZero (absDHs beaconSecrets)) (hshared : beaconSecrets = serverSecrets) :
    ∃ next beaconCandidate pending serverCandidate idPrefix authenticated established peer,
      pqxdh.server_next_key_id serverState = ok (.Ok next) ∧ next.val = serverState.last_key_id.val + 1 ∧
      pqxdh.beacon_prepare_finish beaconState {
        response_server_identity := binding.identity_public_key, assigned_key_id := next, shared_secrets := beaconSecrets } = ok (.Ok beaconCandidate) ∧
      pqxdh.server_accept serverState registration .Fresh binding coins serverSecrets = ok (.Ok (serverState, pending)) ∧
      pqxdh.server_prepare_commit serverState pending binding .Available = ok (.Ok serverCandidate) ∧
      beaconCandidate.server_binding = binding ∧ serverCandidate.server_identity_public_key = binding.identity_public_key ∧
      serverCandidate.server_identity_key_id = binding.identity_key_id ∧
      beaconCandidate.root_key_input = pending.root_key_input ∧ beaconCandidate.associated_data = serverCandidate.associated_data ∧
      beaconCandidate.assigned_key_id = serverCandidate.key_id ∧ serverCandidate.key_id = next ∧
      pqxdh.BeaconRegistrationCandidate.key_id_binding beaconCandidate = ok idPrefix ∧
      pqxdh.ServerRegistrationCandidate.key_id_binding serverCandidate = ok idPrefix ∧
      pqxdh.BeaconRegistrationCandidate.ratchet_initialization beaconCandidate = ok { send_offset := 32#u8, receive_offset := 0#u8 } ∧
      pqxdh.ServerRegistrationCandidate.ratchet_initialization serverCandidate = ok { send_offset := 0#u8, receive_offset := 32#u8 } ∧
      pqxdh.authenticate_registration_key_id_binding beaconCandidate serverCandidate.server_identity_key_id idPrefix.bytes = ok (.Ok authenticated) ∧
      authenticated.candidate = beaconCandidate ∧ pqxdh.beacon_commit authenticated = ok established ∧
      pqxdh.server_commit serverCandidate = ok (serverCandidate.next_state, peer) ∧
      established.server_binding = binding ∧ established.assigned_key_id = peer.key_id ∧
      peer.identity_public_key = beaconState.beacon_identity_public_key ∧ peer.associated_data = beaconCandidate.associated_data ∧
      serverCandidate.previous_state = serverState ∧ serverCandidate.next_state.last_key_id = next := by
  subst serverSecrets
  exact ((build_root_key_input_abs beaconSecrets).1 hvalid).elim fun root hr =>
    (next_server_key_id_success serverState hcounter).elim fun next hn =>
    (PanicFreedom.build_associated_data_ok binding.identity_public_key beaconState.beacon_identity_public_key).elim fun ad had =>
    (PanicFreedom.registration_id_ok registration).elim fun registrationId hregistration =>
    (PanicFreedom.registration_key_id_binding_ok next).elim fun idPrefix hprefix =>
    let beaconCandidate : pqxdh.BeaconRegistrationCandidate := {
      server_binding := binding, assigned_key_id := next, root_key_input := root, associated_data := ad }
    let pending : pqxdh.PendingServerRegistration := {
      server_binding := binding, registration_id := registrationId,
      beacon_identity_public_key := beaconState.beacon_identity_public_key,
      ephemeral_public_key := coins.ephemeral_public_key, kem_ciphertext := coins.kem_ciphertext, root_key_input := root }
    let serverCandidate : pqxdh.ServerRegistrationCandidate := {
      previous_state := serverState, next_state := { last_key_id := next }, key_id := next,
      beacon_identity_public_key := beaconState.beacon_identity_public_key,
      server_identity_public_key := binding.identity_public_key, server_identity_key_id := binding.identity_key_id,
      ephemeral_public_key := coins.ephemeral_public_key, kem_ciphertext := coins.kem_ciphertext, associated_data := ad }
    ⟨next, beaconCandidate, pending, serverCandidate, idPrefix, { candidate := beaconCandidate },
      { server_binding := binding, assigned_key_id := next },
      { key_id := next, identity_public_key := beaconState.beacon_identity_public_key, associated_data := ad }, by
      simp [beaconCandidate, pending, serverCandidate, pqxdh.beacon_prepare_finish, pqxdh.server_accept,
        pqxdh.validate_registration_status, pqxdh.server_prepare_commit, pqxdh.authenticate_registration_key_id_binding,
        pqxdh.BeaconRegistrationCandidate.key_id_binding, pqxdh.ServerRegistrationCandidate.key_id_binding,
        pqxdh.beacon_commit, pqxdh.server_commit, ← hpin, hidentity, hr.1, hn.1, hn.2, had, hregistration, hprefix,
        array_eq_abs, pqxdh.BeaconRegistrationCandidate.ratchet_initialization,
        pqxdh.ServerRegistrationCandidate.ratchet_initialization, pqxdh.BEACON_RATCHETS, pqxdh.SERVER_RATCHETS,
        pqxdh.RATCHET_CHAIN_SIZE, ratchet.RATCHET_CHAIN_SIZE, lift, chain_size_cast]⟩

end BeaconcryptCore.Refinement.PqxdhSurface
