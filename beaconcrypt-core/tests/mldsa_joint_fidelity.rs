// SPDX-License-Identifier: 0BSD

// Reviewed symbolic composition guards, not a Rust-to-ProVerif refinement theorem.
// Existing ML-DSA source mutations check the production builders and adapter guards.
// These checks pin their composition with the shared KEX/record algebra.
const MODEL: &str = include_str!("../proofs/pro-verif/mldsa-joint-session.pvl");
const QUERIES: &str = include_str!("../proofs/pro-verif/mldsa-joint-session.pv");
const MAKEFILE: &str = include_str!("../Makefile");
const WORKFLOW: &str = include_str!("../../.github/workflows/formal-verification.yml");

fn normalized(source: &str) -> String {
	let mut result = String::new();
	let mut chars = source.chars().peekable();
	let mut comments = 0usize;
	while let Some(c) = chars.next() {
		if c == '(' && chars.peek() == Some(&'*') {
			chars.next();
			comments += 1;
		} else if comments > 0 && c == '*' && chars.peek() == Some(&')') {
			chars.next();
			comments -= 1;
		} else if comments == 0 && !c.is_whitespace() {
			result.push(c);
		}
	}
	assert_eq!(comments, 0, "unterminated ProVerif comment");
	result
}

fn ordered(source: &str, parts: &[&str]) -> Result<(), String> {
	let mut tail = source;
	for part in parts {
		let needle = normalized(part);
		let start = tail
			.find(&needle)
			.ok_or_else(|| format!("missing ordered step: {part}"))?;
		tail = &tail[start + needle.len()..];
	}
	Ok(())
}

fn section<'a>(source: &'a str, from: &str, to: &str) -> Result<&'a str, String> {
	let source = source.split_once(&normalized(from)).ok_or(from)?.1;
	Ok(source.split_once(&normalized(to)).ok_or(to)?.0)
}

fn validate(source: &str) -> Result<(), String> {
	let model = normalized(source);
	for obsolete in [
		"beacon_ml",
		"candidate_ml",
		"protected_ml",
		"mldsa_beacon_input",
		"mldsa_signed_init_kex",
		"JointProtectedBeacon",
		"JointInitSigned",
	] {
		if model.contains(obsolete) {
			return Err(format!("deleted Beacon ML credential restored: {obsolete}"));
		}
	}

	ordered(
		&model,
		&[
			"letfun mldsa_joint_server_input(",
			"let dh1 = x25519_server_dh(server_secret, prekey) in",
			"let dh2 = x25519_server_dh(ephemeral_secret, x25519_public_from_ed(beacon_identity)) in",
			"let dh3 = x25519_server_dh(ephemeral_secret, prekey) in",
			"let dh4 = x25519_server_dh(ephemeral_secret, one_time) in",
			"let kem_secret = mlkem_shared_secret(pq, kem_coins) in",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets(dh1, dh2, dh3, dh4, kem_secret)",
			"letfun mldsa_joint_beacon_input(",
			"let kem_secret = mlkem_decapsulate(kem_ciphertext, pq_secret) in",
			"let dh1 = x25519_beacon_dh(prekey_secret, x25519_public_from_ed(server_identity)) in",
			"let dh2 = x25519_beacon_dh(identity_secret, ephemeral) in",
			"let dh3 = x25519_beacon_dh(prekey_secret, ephemeral) in",
			"let dh4 = x25519_beacon_dh(one_time_secret, ephemeral) in",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets(dh1, dh2, dh3, dh4, kem_secret)",
		],
	)?;
	ordered(
		&model,
		&[
			"new replay_lock: channel; new accepted_observation: channel; new rejected_observation: channel; ( out(replay_lock, mldsa_joint_lock_token()) | MldsaJointServer(",
			"mldsa_joint_first_id(), replay_lock, accepted_observation, rejected_observation)",
			"| MldsaJointServer(",
			"mldsa_joint_second_id(), replay_lock, accepted_observation, rejected_observation)",
			"| MldsaJointBeacon(",
			"| MldsaJointOwnedRequest(beacon_ed, owned_pq_secret)",
			"| MldsaJointCopiedKemRequest(beacon_ed, selected_pq)",
			"| MldsaJointCapabilityWitness(server_secret, prekey_secret)",
		],
	)?;
	let server = section(&model, "let MldsaJointServer(", "let MldsaJointBeacon(")?;
	let admission = server
		.split_once("eventJointRequestAdmitted(")
		.ok_or("missing admission event")?
		.0;
	if admission.contains("ifcandidate_init=") {
		return Err("session selection must not gate registration admission".into());
	}
	ordered(
		server,
		&[
			"let candidate_init = incoming in",
			"let candidate_hash = mldsa_init_hash(SERVER_KEY_ID, server_ed, server_ml, candidate_init) in",
			"let tag_mlkem768(candidate_pq) = verify_signature(signed_pq, candidate_ed) in",
			"let tag_x25519_prekey(candidate_prekey) = verify_signature(signed_prekey, candidate_ed) in",
			"let tag_x25519_one_time(candidate_one_time) = verify_signature(signed_one_time, candidate_ed) in",
			"let verified_init = beaconcrypt_core__pqxdh__VerifiedInitKex(candidate_ed, candidate_prekey, candidate_one_time, candidate_pq) in",
			"let registration_id = beaconcrypt_core__pqxdh__registration_id(verified_init) in",
			"let root_input = mldsa_joint_server_input(server_secret, ephemeral_secret, candidate_ed, candidate_prekey, candidate_one_time, candidate_pq, kem_coins) in",
			"let root = pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)) in",
			"in(replay_lock, lock_token: bitstring);",
			"get mldsa_joint_consumed(=registration_id) in (out(replay_lock, mldsa_joint_released_token(assigned, registration_id)) | out(rejected_observation, (assigned, registration_id, lock_token)) | (let mldsa_joint_released_token(previous_slot, =registration_id) = lock_token in if previous_slot = assigned then 0 else event JointReplayRejected())) else insert mldsa_joint_consumed(registration_id); (out(replay_lock, mldsa_joint_released_token(assigned, registration_id)) | out(accepted_observation, (assigned, registration_id)) | event JointRequestAdmitted(candidate_init, server_ml, candidate_hash);",
			"if candidate_init = selected_init then MldsaJointServerPublish(",
			"root, assigned, MLDSA_JOINT_INITIAL, MLDSA_JOINT_SERVER_RECORD) else MldsaJointServerPublish(",
			"root, assigned, MLDSA_JOINT_OWNED_INITIAL, MLDSA_JOINT_OWNED_RECORD)",
		],
	)?;
	ordered(
		server,
		&[
			"if candidate_pq = owned_pq then if candidate_ed = selected_ed then event JointOwnedAccepted()",
		],
	)?;
	let publish = section(
		&model,
		"let MldsaJointServerPublish(",
		"let MldsaJointServer(",
	)?;
	ordered(
		publish,
		&[
			"let ad = mldsa_ad(candidate_init, server_ed, ephemeral, kem_ciphertext, assigned) in",
			"let initial_frame = seal_frame(ratchet_material(server_to_beacon_chain(root)), ad, first_sequence(), SERVER_KEY_ID, registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(assigned)), initial_plaintext)) in",
			"let raw_initial = mldsa_strip(initial_frame) in",
			"let response = mldsa_response_fields(server_ed, ephemeral, kem_ciphertext, raw_initial, assigned) in",
			"let response_hash = mldsa_response_hash(candidate_hash, response) in",
			"let response_signature = mldsa_sign(mldsa_server_input(response_hash), server_ml_secret, mldsa_signing_context()) in",
			"event JointServerCommitted(candidate_init, server_ml, candidate_hash, response, root, ad, assigned, initial_plaintext);",
			"out(mldsa_joint_registration, mldsa_signed_kex_response(response, response_signature));",
			"let record_sequence = next_sequence(first_sequence()) in",
			"let record_material = ratchet_material(ratchet_next(server_to_beacon_chain(root))) in",
			"let record_frame = seal_frame(record_material, ad, record_sequence, SERVER_KEY_ID, record_plaintext) in",
			"event JointRecordSent(candidate_init, server_ml, candidate_hash, root, ad, server_to_beacon(), record_sequence, SERVER_KEY_ID, assigned, record_plaintext); out(mldsa_joint_server_records, record_frame);",
		],
	)?;
	let beacon = section(
		&model,
		"let MldsaJointBeacon(",
		"let MldsaJointOwnedRequest(",
	)?;
	ordered(
		beacon,
		&[
			"let expected_response_hash = mldsa_response_hash(init_hash, response) in",
			"let verified_response_input = mldsa_verify(response_signature, server_ml, mldsa_signing_context()) in",
			"if verified_response_input = mldsa_server_input(expected_response_hash) then",
			"let root_input = mldsa_joint_beacon_input(identity_secret, prekey_secret, one_time_secret, pq_secret, response_ed, ephemeral, kem_ciphertext) in",
			"if response_ed = server_ed then",
			"let root = pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)) in",
			"let ad = mldsa_ad(classical_init, response_ed, ephemeral, kem_ciphertext, assigned) in",
			"let initial_frame = mldsa_restore(raw_initial, SERVER_KEY_ID) in",
			"let initial_payload = open_frame(ratchet_material(server_to_beacon_chain(root)), ad, first_sequence(), SERVER_KEY_ID, initial_frame) in",
			"let expected_binding = beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(assigned)) in",
			"let registration_payload(=expected_binding, initial_plaintext) = initial_payload in",
			"event JointBeaconCompleted(classical_init, server_ml, init_hash, response, root, ad, assigned, initial_plaintext); event JointHonestComplete();",
			"let beacon_frame = seal_frame(ratchet_material(beacon_to_server_chain(root)), ad, first_sequence(), assigned, MLDSA_JOINT_BEACON_RECORD) in",
			"event JointRecordSent(classical_init, server_ml, init_hash, root, ad, beacon_to_server(), first_sequence(), assigned, SERVER_KEY_ID, MLDSA_JOINT_BEACON_RECORD); out(mldsa_joint_beacon_records, beacon_frame);",
			"if parsed_sender = SERVER_KEY_ID then if parsed_sequence = next_sequence(first_sequence()) then",
			"let record_plaintext = open_frame(ratchet_material(ratchet_next(server_to_beacon_chain(root))), ad, next_sequence(first_sequence()), SERVER_KEY_ID, incoming_record) in",
			"event JointRecordReceived(classical_init, server_ml, init_hash, root, ad, server_to_beacon(), next_sequence(first_sequence()), SERVER_KEY_ID, assigned, record_plaintext); if record_plaintext = MLDSA_JOINT_SERVER_RECORD then event JointServerRecordOpened().",
		],
	)?;
	let receive = section(
		&model,
		"let MldsaJointServerReceive(",
		"let MldsaJointServerPublish(",
	)?;
	ordered(
		receive,
		&[
			"if parsed_sender = assigned then if parsed_sequence = first_sequence() then",
			"let plaintext = open_frame(ratchet_material(beacon_to_server_chain(root)), ad, first_sequence(), assigned, incoming_record) in",
			"event JointRecordReceived(request, server_ml, init_hash, root, ad, beacon_to_server(), first_sequence(), assigned, SERVER_KEY_ID, plaintext); if plaintext = MLDSA_JOINT_BEACON_RECORD then event JointBeaconRecordOpened().",
		],
	)?;
	let capability = section(
		&model,
		"let MldsaJointCapabilityWitness(",
		"let MldsaJointSession()",
	)?;
	ordered(
		capability,
		&[
			"let recovered_ed = quantum_recover_ed25519_secret(ed_public(server_secret)) in if recovered_ed = server_secret then",
			"let recovered_dh = quantum_recover_x25519_secret(x25519_public(prekey_secret)) in if recovered_dh = prekey_secret then event JointClassicalRecovered().",
		],
	)?;
	let creation = section(
		&model,
		"let MldsaJointSession() =",
		"new replay_lock: channel;",
	)?;
	ordered(
		creation,
		&[
			"let selected_pq = mlkem_public(pq_secret) in",
			"let selected_init = signed_init_kex(tag_ed25519(beacon_ed), sign(tag_x25519_prekey(x25519_public(prekey_secret)), identity_secret), sign(tag_x25519_one_time(x25519_public(one_time_secret)), identity_secret), sign(tag_mlkem768(selected_pq), identity_secret)) in",
			"event JointSessionCreated(selected_init);",
		],
	)?;
	Ok(())
}

#[test]
fn joint_model_connects_authentication_to_kex_and_record_state() {
	validate(MODEL).unwrap();
	assert_eq!(normalized(QUERIES).matches("query").count(), 16);
	let makefile = normalized(MAKEFILE);
	for wanted in [
		"$(MAKE) check-proverif-mldsa-joint",
		"cargo test --locked -p beaconcrypt-core --test mldsa_joint_fidelity",
		"mldsa_transcript_source_and_model_mutations_are_rejected -- --exact",
		"python3 $(PROVERIF_DIR)/test-mldsa-joint-session-checker.py",
		"python3 $(PROVERIF_DIR)/test-verdict-classes.py MldsaJointClassificationTests",
		"python3 $(PROVERIF_DIR)/check-mldsa-joint-session.py",
	] {
		assert!(
			makefile.contains(&normalized(wanted)),
			"missing maintained gate: {wanted}"
		);
	}
	assert!(WORKFLOW.contains("target: verify-proverif-mldsa-joint"));
}

const JOINT_COMPOSITION_MUTATION_COUNT: usize = 37;

#[test]
fn joint_model_rejects_changes_to_security_relevant_composition() {
	let mut checked = 0;
	for (from, to) in [
		(
			"mldsa_joint_released_token(previous_slot, =registration_id) = lock_token",
			"mldsa_joint_released_token(previous_slot, prior_id) = lock_token",
		),
		(
			"if previous_slot = assigned then 0 else event JointReplayRejected()",
			"event JointReplayRejected()",
		),
		(
			"out(replay_lock, mldsa_joint_released_token(assigned, registration_id))\n      |",
			"out(replay_lock, mldsa_joint_released_token(assigned, registration_id));",
		),
		(
			"mldsa_ad(candidate_init, server_ed, ephemeral, kem_ciphertext, assigned)",
			"mldsa_ad(candidate_init, ephemeral, server_ed, kem_ciphertext, assigned)",
		),
		(
			"mldsa_ad(classical_init, response_ed, ephemeral, kem_ciphertext, assigned)",
			"mldsa_ad(classical_init, response_ed, response_ed, kem_ciphertext, assigned)",
		),
		(
			"candidate_hash, response, root, ad,\n    assigned, initial_plaintext);",
			"candidate_hash, response, root, root,\n    assigned, initial_plaintext);",
		),
		(
			"event JointBeaconCompleted(classical_init, server_ml, init_hash, response, root, ad, assigned, initial_plaintext);",
			"event JointBeaconCompleted(classical_init, server_ml, init_hash, response, root, root, assigned, initial_plaintext);",
		),
		(
			"if candidate_ed = selected_ed then event JointOwnedAccepted()",
			"event JointOwnedAccepted()",
		),
		(
			"if recovered_dh = prekey_secret then event JointClassicalRecovered()",
			"event JointClassicalRecovered()",
		),
		(
			"if record_plaintext = MLDSA_JOINT_SERVER_RECORD then event JointServerRecordOpened()",
			"event JointServerRecordOpened()",
		),
		(
			"if plaintext = MLDSA_JOINT_BEACON_RECORD then event JointBeaconRecordOpened()",
			"event JointBeaconRecordOpened()",
		),
		(
			"x25519_server_dh(server_secret, prekey)",
			"x25519_server_dh(ephemeral_secret, prekey)",
		),
		(
			"PqxdhSharedSecrets(dh1, dh2, dh3, dh4, kem_secret)",
			"PqxdhSharedSecrets(dh1, dh2, dh3, dh4, dh4)",
		),
		(
			"mlkem_decapsulate(kem_ciphertext, pq_secret)",
			"mlkem_decapsulate(kem_ciphertext, identity_secret)",
		),
		(
			"mldsa_init_hash(SERVER_KEY_ID, server_ed, server_ml, candidate_init)",
			"mldsa_init_hash(SERVER_KEY_ID, server_ed, server_ml, selected_init)",
		),
		(
			"let candidate_init = incoming in",
			"let candidate_init = selected_init in",
		),
		(
			"registration_id(verified_init)",
			"registration_id(candidate_init)",
		),
		("in(replay_lock, lock_token: bitstring);", ""),
		(
			"new rejected_observation: channel;\n  (",
			"new rejected_observation: channel;\n  out(replay_lock, mldsa_joint_lock_token());\n  (",
		),
		(
			"let tag_ed25519(candidate_ed) = encoded_identity in",
			"if candidate_init = selected_init then let tag_ed25519(candidate_ed) = encoded_identity in",
		),
		("insert mldsa_joint_consumed(registration_id);", ""),
		(
			"event JointSessionCreated(selected_init);",
			"event JointSessionCreated(server_ml);",
		),
		(
			"MLDSA_JOINT_INITIAL, MLDSA_JOINT_SERVER_RECORD",
			"MLDSA_JOINT_INITIAL, MLDSA_JOINT_INITIAL",
		),
		(
			"MLDSA_JOINT_OWNED_INITIAL, MLDSA_JOINT_OWNED_RECORD",
			"MLDSA_JOINT_INITIAL, MLDSA_JOINT_SERVER_RECORD",
		),
		(
			"mldsa_ad(candidate_init, server_ed, ephemeral, kem_ciphertext, assigned)",
			"mldsa_ad(candidate_init, server_ed, ephemeral, kem_ciphertext, SERVER_KEY_ID)",
		),
		("mldsa_strip(initial_frame)", "initial_frame"),
		(
			"mldsa_response_hash(candidate_hash, response)",
			"mldsa_response_hash(root, response)",
		),
		(
			"mldsa_server_input(response_hash)",
			"mldsa_other_role(response_hash)",
		),
		(
			"mldsa_response_hash(init_hash, response)",
			"mldsa_response_hash(response, response)",
		),
		(
			"server_ml, mldsa_signing_context()) in",
			"untrusted_key, mldsa_signing_context()) in",
		),
		("if response_ed = server_ed then", ""),
		(
			"mldsa_ad(classical_init, response_ed, ephemeral, kem_ciphertext, assigned)",
			"mldsa_ad(classical_init, response_ed, ephemeral, kem_ciphertext, SERVER_KEY_ID)",
		),
		(
			"mldsa_restore(raw_initial, SERVER_KEY_ID)",
			"mldsa_restore(raw_initial, assigned)",
		),
		(
			"let registration_payload(=expected_binding, initial_plaintext)",
			"let registration_payload(other_binding, initial_plaintext)",
		),
		("if parsed_sender = assigned then", ""),
		("if parsed_sequence = first_sequence() then", ""),
		(
			"ratchet_next(server_to_beacon_chain(root))",
			"server_to_beacon_chain(root)",
		),
	] {
		assert!(MODEL.contains(from), "stale mutation: {from}");
		let changed = MODEL.replacen(from, to, 1);
		assert!(
			validate(&changed).is_err(),
			"composition mutation survived: {from}"
		);
		checked += 1;
	}
	assert_eq!(checked, JOINT_COMPOSITION_MUTATION_COUNT);
}
