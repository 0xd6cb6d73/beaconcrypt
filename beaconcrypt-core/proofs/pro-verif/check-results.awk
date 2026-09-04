# SPDX-License-Identifier: 0BSD

function reject(message) {
  print "ProVerif result check failed: " message > "/dev/stderr"
  failed = 1
}

function require_exact(wanted, label, query_index, found) {
  found = 0
  for (query_index = 1; query_index <= query_count; query_index++) {
    if (query[query_index] == wanted) {
      found = 1
    }
  }
  if (!found) {
    reject("missing or substituted " label " query: " wanted)
  }
}

/^RESULT / {
  print
}

/^RESULT Observational equivalence is / {
  equivalence_count++
  if ((scenario == "passive-classical-equivalence" ||
       scenario == "passive-quantum-equivalence") &&
      $0 != "RESULT Observational equivalence is true.") {
    reject(scenario " was not proved: " $0)
  }
}

/^Verification summary:$/ {
  in_summary = 1
  next
}

in_summary && /^Query / {
  query_count++
  query[query_count] = $0

  if ($0 ~ /cannot be proved|is unknown|is inconclusive/) {
    reject($0)
  }

  if ((scenario == "baseline" ||
       scenario == "active-classical" ||
       scenario == "passive-classical" ||
       scenario == "passive-quantum" ||
       scenario == "failed-receive") &&
      $0 !~ / is true\.$/) {
    reject(scenario " query was not true: " $0)
  }

  if ((scenario == "reachability" ||
       scenario == "failed-receive-reachability" ||
       scenario == "failed-receive-compromise-reachability") &&
      $0 !~ / is false\.$/) {
    reject(scenario " witness was not found: " $0)
  }

  if (scenario == "active-quantum" && $0 !~ / is false\.$/) {
    reject("expected active-quantum break was not found: " $0)
  }

  if ((scenario == "passive-reachability" ||
       scenario == "quantum-capabilities") &&
      $0 !~ / is false\.$/) {
    reject(scenario " control witness was not found: " $0)
  }

  if (scenario == "quantum-mlkem-opacity" && $0 !~ / is true\.$/) {
    reject("ML-KEM opacity control did not preserve secrecy: " $0)
  }

  if (scenario == "quantum-mlkem-recovery" && $0 !~ / is false\.$/) {
    reject("ML-KEM recovery control did not expose the canary: " $0)
  }
}

END {
  if (!in_summary) {
    reject("missing verification summary")
  }

  registration_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,origin_1"
  accepted_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,root_input_3,root_3,origin_1"
  message_arguments = "session_4,message_direction,message_sequence_6,sender,receiver,plaintext_2"
  receive_rejected_arguments = "session_3,target_sequence_2,forged_frame,entry_state"
  receive_future_arguments = "session_3,target_sequence_2,sender,receiver,plaintext_8,accepted_frame,target_material_1,forged_frame,entry_state,committed_state_1"
  receive_reachable_future_arguments = "session_3,target_sequence_2,sender,receiver,RECEIVE_TARGET_SECRET[],accepted_frame,target_material_1,forged_frame,entry_state,committed_state_1"
  receive_delayed_arguments = "session_3,delayed_sequence,sender,receiver,plaintext_8,delayed_frame,delayed_material,committed_state_1,final_state"
  receive_reachable_delayed_arguments = "session_3,delayed_sequence,sender,receiver,RECEIVE_SKIPPED_SECRET[],delayed_frame,delayed_material,committed_state_1,final_state"
  receive_maximum_arguments = "session_3,target_sequence_2,sender,receiver,plaintext_8,accepted_frame,target_material_1,entry_state,committed_state_1"
  receive_reachable_maximum_arguments = "session_3,target_sequence_2,sender,receiver,RECEIVE_MAX_GAP_SECRET[],accepted_frame,target_material_1,entry_state,committed_state_1"
  receive_capacity_arguments = "session_3,target_sequence_2,rejected_frame,rejected_state"
  receive_cached_arguments = "session_3,cached_sequence,cached_material,full_state,released_state_1"
  receive_after_release_arguments = "session_3,target_sequence_2,sender,receiver,plaintext_8,accepted_frame,target_material_1,rejected_state,released_state_1,committed_state_1"
  receive_reachable_after_release_arguments = "session_3,target_sequence_2,sender,receiver,RECEIVE_AFTER_RELEASE_SECRET[],accepted_frame,target_material_1,rejected_state,released_state_1,committed_state_1"
  receive_message_arguments = "session_3,message_direction,message_sequence_1,sender,receiver,plaintext_8"
  receive_malicious_commit_arguments = "transcript,plaintext_8"
  weak_aead_arguments = "left_key_1,right_key_1,left_context_1,right_context_1,left_plaintext_1,right_plaintext_1"

  later_root = "root_5"
  later_domain = "symmetric_ratchet_domain"
  later_seq1 = "first_sequence"
  later_seq2 = "next_sequence(" later_seq1 ")"
  later_seq3 = "next_sequence(" later_seq2 ")"
  later_chain1 = "hkdf_first_32(hkdf_sha512_no_salt(" later_root "," later_domain "))"
  later_chain2 = "hkdf_second_32(hkdf_sha512_no_salt(" later_chain1 "," later_domain "))"
  later_chain3 = "hkdf_second_32(hkdf_sha512_no_salt(" later_chain2 "," later_domain "))"
  later_chain4 = "hkdf_second_32(hkdf_sha512_no_salt(" later_chain3 "," later_domain "))"
  later_send_chain = "hkdf_second_32(hkdf_sha512_no_salt(" later_root "," later_domain "))"
  later_material1 = "ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(" later_chain1 "," later_domain ")),hkdf_final_12(hkdf_sha512_no_salt(" later_chain1 "," later_domain ")))"
  later_material2 = "ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(" later_chain2 "," later_domain ")),hkdf_final_12(hkdf_sha512_no_salt(" later_chain2 "," later_domain ")))"
  later_material3 = "ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(" later_chain3 "," later_domain ")),hkdf_final_12(hkdf_sha512_no_salt(" later_chain3 "," later_domain ")))"
  later_cache = "receive_cache_entry(" later_seq2 "," later_material2 ",receive_cache_entry(" later_seq1 "," later_material1 ",receive_cache_empty))"
  later_receive_state = "receive_state(" later_seq3 "," later_chain4 "," later_cache ")"
  later_ratchet = "later_registration_ratchet_state(zero_sequence," later_send_chain "," later_receive_state ")"

  equivalence_scenario = (scenario == "passive-classical-equivalence" ||
                          scenario == "passive-quantum-equivalence")
  if (!equivalence_scenario && equivalence_count != 0) {
    reject("unexpected observational-equivalence result in " scenario)
  }

  if (equivalence_scenario) {
    if (equivalence_count != 1) {
      reject("expected one " scenario " result, saw " equivalence_count)
    }
    if (query_count != 0) {
      reject("expected no reachability queries in " scenario ", saw " query_count)
    }
  } else if (scenario == "aead-commitment" ||
      scenario == "aead-no-commitment") {
    if (query_count != 7) {
      reject("expected 7 " scenario " queries, saw " query_count)
    }
    expected_result = (scenario == "aead-commitment") ? "true" : "false"
    wanted = "Query not event(WeakAeadMultiOpened(" weak_aead_arguments ")) is " expected_result "."
    require_exact(wanted, scenario)
    mutation[1] = "ctx_key_mutation"
    mutation[2] = "ctx_nonce_mutation"
    mutation[3] = "ctx_associated_data_mutation"
    mutation[4] = "ctx_tag_mutation"
    mutation[5] = "ctx_sequence_mutation"
    mutation[6] = "ctx_sender_mutation"
    for (mutation_index = 1; mutation_index <= 6; mutation_index++) {
      wanted = "Query not event(CtxMutationAccepted(" mutation[mutation_index] ")) is true."
      require_exact(wanted, "CTX independent field mutation")
    }
  } else if (scenario == "passive-classical" ||
             scenario == "passive-quantum") {
    if (query_count != 5) {
      reject("expected 5 " scenario " secrecy queries, saw " query_count)
    }

    passive_secret[1] = "INITIAL_SECRET"
    passive_secret[2] = "CACHED_SECRET"
    passive_secret[3] = "ADVANCE_SECRET"
    passive_secret[4] = "FUTURE_SECRET"
    passive_secret[5] = "BEACON_RECORD_SECRET"
    for (secret_index = 1; secret_index <= 5; secret_index++) {
      wanted = "Query not attacker(" passive_secret[secret_index] "[]) is true."
      require_exact(wanted, scenario " secrecy")
    }
  } else if (scenario == "active-quantum") {
    if (query_count != 4) {
      reject("expected 4 active-quantum attack queries, saw " query_count)
    }

    wanted = "Query not attacker(INITIAL_SECRET[]) is false."
    require_exact(wanted, "active-quantum confidentiality break")
    wanted = "Query not event(QuantumInitialSecretRecovered(selected_pq_public_key,server_ephemeral_3,kem_ciphertext_3,initial_frame_3,response_3,root_input_3,root_3,INITIAL_SECRET[])) is false."
    require_exact(wanted, "active-quantum recovery witness")
    active_quantum_arguments = "server_identity_2,beacon_identity_3,init,registration_id_2,root_input_3,root_3,origin_1"
    active_quantum_origin_arguments = "server_identity_2,beacon_identity_3,init,registration_id_2,origin_1"
    wanted = "Query inj-event(ServerAccepted(" active_quantum_arguments ")) ==> inj-event(BeaconInitiated(" active_quantum_origin_arguments ")) is false."
    require_exact(wanted, "active-quantum agreement break")
    wanted = "Query inj-event(ServerBundleAccepted(bundle)) ==> inj-event(BeaconBundleInitiated(bundle)) is false."
    require_exact(wanted, "active-quantum authenticated-bundle agreement break")
  } else if (scenario == "passive-reachability") {
    if (query_count != 6) {
      reject("expected 6 passive reachability queries, saw " query_count)
    }
    wanted = "Query not event(BeaconCommitted(transcript)) is false."
    require_exact(wanted, "passive registration completion")
    passive_delivery[1] = "server_to_beacon,first_sequence,sender,receiver,INITIAL_SECRET[]"
    passive_delivery[2] = "server_to_beacon,next_sequence(first_sequence),sender,receiver,CACHED_SECRET[]"
    passive_delivery[3] = "server_to_beacon,next_sequence(next_sequence(first_sequence)),sender,receiver,ADVANCE_SECRET[]"
    passive_delivery[4] = "server_to_beacon,next_sequence(next_sequence(next_sequence(first_sequence))),sender,receiver,FUTURE_SECRET[]"
    passive_delivery[5] = "beacon_to_server,first_sequence,sender,receiver,BEACON_RECORD_SECRET[]"
    for (delivery_index = 1; delivery_index <= 5; delivery_index++) {
      wanted = "Query not event(MessageReceived(session_3," passive_delivery[delivery_index] ")) is false."
      require_exact(wanted, "passive exact canary delivery")
    }
  } else if (scenario == "quantum-capabilities") {
    if (query_count != 2) {
      reject("expected 2 quantum capability queries, saw " query_count)
    }
    wanted = "Query not attacker(QUANTUM_ED_CAPABILITY_SECRET[]) is false."
    require_exact(wanted, "Ed25519 quantum recovery")
    wanted = "Query not attacker(QUANTUM_X25519_CAPABILITY_SECRET[]) is false."
    require_exact(wanted, "X25519 quantum recovery")
  } else if (scenario == "quantum-mlkem-opacity" ||
             scenario == "quantum-mlkem-recovery") {
    if (query_count != 1) {
      reject("expected 1 " scenario " query, saw " query_count)
    }
    expected_result = (scenario == "quantum-mlkem-opacity") ? "true" : "false"
    wanted = "Query not attacker(QUANTUM_MLKEM_CONTROL_SECRET[]) is " expected_result "."
    require_exact(wanted, scenario)
  } else if (scenario == "mlkem-reencapsulation-strong" ||
             scenario == "mlkem-reencapsulation-weak") {
    if (query_count != 8) {
      reject("expected 8 " scenario " queries, saw " query_count)
    }
    wanted = "Query not event(KemMultiEpochPathReached(KEM_MULTI_EPOCH_PATH_WITNESS[])) is false."
    require_exact(wanted, scenario " multi-epoch path")
    wanted = "Query not event(KemOldKeyCompromised(KEM_OLD_KEY_COMPROMISE_WITNESS[])) is false."
    require_exact(wanted, scenario " old-key compromise")
    wanted = "Query not event(KemCiphertextSubstitutionAttempted(KEM_SUBSTITUTION_ATTEMPT_WITNESS[])) is false."
    require_exact(wanted, scenario " ciphertext-substitution attempt")
    attack_result = (scenario == "mlkem-reencapsulation-strong") ? "true" : "false"
    wanted = "Query not event(KemWeakReencapsulationSucceeded(KEM_WEAK_ATTACK_WITNESS[])) is " attack_result "."
    require_exact(wanted, scenario " re-encapsulation classification")
    wanted = "Query not event(KemAcceptedRootDisclosed(KEM_ROOT_DISCLOSURE_WITNESS[])) is " attack_result "."
    require_exact(wanted, scenario " accepted-root disclosure")
    wanted = "Query not event(KemOrdinaryOneShotCompleted(KEM_ORDINARY_ONE_SHOT_WITNESS[])) is false."
    require_exact(wanted, scenario " ordinary one-shot path")
    wanted = "Query not attacker(KEM_NEW_SESSION_CANARY[]) is " attack_result "."
    require_exact(wanted, scenario " new-session secrecy")
    wanted = "Query inj-event(KemControlBeaconCommitted(transcript)) ==> inj-event(KemControlServerCommitted(transcript)) is " attack_result "."
    require_exact(wanted, scenario " exact public-key/ciphertext agreement")
  } else if (scenario == "hkdf-prefix-conformance") {
    if (query_count != 2) {
      reject("expected 2 HKDF prefix conformance queries, saw " query_count)
    }
    wanted = "Query not event(HkdfInitialLeftEqualsStepKey(HKDF_PREFIX_LEFT_WITNESS[])) is false."
    require_exact(wanted, "initial-left/step-key prefix equality")
    wanted = "Query not event(HkdfInitialRightEqualsStepNext(HKDF_PREFIX_RIGHT_WITNESS[])) is false."
    require_exact(wanted, "initial-right/step-next prefix equality")
  } else if (scenario == "hkdf-endpoint-controls") {
    if (query_count != 8) {
      reject("expected 8 HKDF endpoint-control queries, saw " query_count)
    }
    wanted = "Query not event(HkdfCorrectRootEndpointCommitted(HKDF_CORRECT_ROOT_COMMIT_WITNESS[])) is false."
    require_exact(wanted, "correct root-domain endpoint")
    wanted = "Query not event(HkdfWrongRootOpeningAttempted(HKDF_WRONG_ROOT_COMMIT_WITNESS[])) is false."
    require_exact(wanted, "wrong root-domain attempt")
    wanted = "Query not event(HkdfWrongRootEndpointCommitted(HKDF_WRONG_ROOT_COMMIT_WITNESS[])) is true."
    require_exact(wanted, "wrong root-domain rejection")
    wanted = "Query not event(HkdfCorrectSymmetricEndpointCommitted(HKDF_CORRECT_SYMMETRIC_COMMIT_WITNESS[])) is false."
    require_exact(wanted, "correct symmetric-domain endpoint")
    wanted = "Query not event(HkdfWrongSymmetricOpeningAttempted(HKDF_WRONG_SYMMETRIC_COMMIT_WITNESS[])) is false."
    require_exact(wanted, "wrong symmetric-domain attempt")
    wanted = "Query not event(HkdfWrongSymmetricEndpointCommitted(HKDF_WRONG_SYMMETRIC_COMMIT_WITNESS[])) is true."
    require_exact(wanted, "wrong symmetric-domain rejection")
    wanted = "Query not event(HkdfWrongProjectionOpeningAttempted(HKDF_WRONG_PROJECTION_COMMIT_WITNESS[])) is false."
    require_exact(wanted, "wrong projection attempt")
    wanted = "Query not event(HkdfWrongProjectionEndpointCommitted(HKDF_WRONG_PROJECTION_COMMIT_WITNESS[])) is true."
    require_exact(wanted, "wrong projection rejection")
  } else if (scenario == "hkdf-domain-distinct" ||
             scenario == "hkdf-domain-alias") {
    if (query_count != 2) {
      reject("expected 2 " scenario " queries, saw " query_count)
    }
    wanted = "Query not event(HkdfDomainComparisonAttempted(HKDF_DOMAIN_COMPARISON_WITNESS[])) is false."
    require_exact(wanted, scenario " non-vacuity")
    expected_result = (scenario == "hkdf-domain-distinct") ? "true" : "false"
    wanted = "Query not attacker(HKDF_DOMAIN_ALIAS_CANARY[]) is " expected_result "."
    require_exact(wanted, scenario " cross-domain disclosure")
  } else if (scenario == "public-key-confusion-strong" ||
             scenario == "public-key-confusion-weak") {
    if (query_count != 8) {
      reject("expected 8 " scenario " queries, saw " query_count)
    }
    wanted = "Query not event(PkAlgorithmMlkemLegitimateParsed(PK_ALGORITHM_MLKEM_PARSE_WITNESS[])) is false."
    require_exact(wanted, scenario " legitimate ML-KEM parse")
    wanted = "Query not event(PkAlgorithmX25519LegitimateParsed(PK_ALGORITHM_X25519_PARSE_WITNESS[])) is false."
    require_exact(wanted, scenario " legitimate X25519 parse")
    wanted = "Query not event(PkAlgorithmConfusionAttempted(PK_ALGORITHM_CONFUSION_WITNESS[])) is false."
    require_exact(wanted, scenario " algorithm-confusion attempt")
    acceptance_result = (scenario == "public-key-confusion-strong") ? "true" : "false"
    wanted = "Query not event(PkAlgorithmConfusionAccepted(PK_ALGORITHM_CONFUSION_WITNESS[])) is " acceptance_result "."
    require_exact(wanted, scenario " algorithm-confusion classification")
    wanted = "Query not event(PkRolePrekeyLegitimateParsed(PK_ROLE_PREKEY_PARSE_WITNESS[])) is false."
    require_exact(wanted, scenario " legitimate prekey parse")
    wanted = "Query not event(PkRoleOneTimeLegitimateParsed(PK_ROLE_ONE_TIME_PARSE_WITNESS[])) is false."
    require_exact(wanted, scenario " legitimate one-time parse")
    wanted = "Query not event(PkRoleConfusionAttempted(PK_ROLE_CONFUSION_WITNESS[])) is false."
    require_exact(wanted, scenario " role-confusion attempt")
    wanted = "Query not event(PkRoleConfusionAccepted(PK_ROLE_CONFUSION_WITNESS[])) is " acceptance_result "."
    require_exact(wanted, scenario " role-confusion classification")
  } else if (scenario == "phase2-response-binding") {
    if (query_count != 18) {
      reject("expected 18 Phase-2 response-binding queries, saw " query_count)
    }
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_CORRECT_RESPONSE_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 correct response commit")
    wanted = "Query not event(Phase2ResponseAttempted(PHASE2_WRONG_OUTER_IDENTITY_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 wrong outer-identity attempt")
    wanted = "Query not event(Phase2OuterIdentityGateReached(PHASE2_WRONG_OUTER_IDENTITY_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 wrong outer-identity internal gate")
    wanted = "Query not event(Phase2ResponseAttempted(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 relabeled assigned-ID attempt")
    wanted = "Query not event(Phase2AuthenticatedFrameOpened(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 relabeled assigned-ID authenticated frame")
    wanted = "Query not event(Phase2GenuineAssignedPrefixObserved(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 relabeled assigned-ID original authenticated prefix")
    wanted = "Query not event(Phase2ResponseAttempted(PHASE2_WRONG_INNER_SENDER_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 wrong inner-sender attempt")
    wanted = "Query not event(Phase2InnerSenderGateReached(PHASE2_WRONG_INNER_SENDER_WITNESS[])) is false."
    require_exact(wanted, "Phase-2 wrong inner-sender internal gate")
    wanted = "Query not event(Phase2AcceptedOuterIdentity(binding)) is false."
    require_exact(wanted, "Phase-2 non-vacuous outer-identity binding")
    wanted = "Query not event(Phase2AcceptedAssignedPrefix(binding)) is false."
    require_exact(wanted, "Phase-2 non-vacuous assigned-ID prefix binding")
    wanted = "Query not event(Phase2AcceptedInnerSender(binding)) is false."
    require_exact(wanted, "Phase-2 non-vacuous inner-sender binding")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_WRONG_OUTER_IDENTITY_WITNESS[])) is true."
    require_exact(wanted, "Phase-2 wrong outer-identity rejection")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is true."
    require_exact(wanted, "Phase-2 relabeled assigned-ID rejection")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_WRONG_INNER_SENDER_WITNESS[])) is true."
    require_exact(wanted, "Phase-2 wrong inner-sender rejection")
    wanted = "Query not attacker(PHASE2_ASSIGNED_ID_BINDING_CANARY[]) is true."
    require_exact(wanted, "Phase-2 assigned-ID binding canary secrecy")
    wanted = "Query inj-event(Phase2AcceptedOuterIdentity(binding)) ==> inj-event(Phase2PinnedOuterIdentity(binding)) is true."
    require_exact(wanted, "Phase-2 outer-identity binding correspondence")
    wanted = "Query inj-event(Phase2AcceptedAssignedPrefix(binding)) ==> inj-event(Phase2AuthenticatedAssignedPrefix(binding)) is true."
    require_exact(wanted, "Phase-2 assigned-ID prefix correspondence")
    wanted = "Query inj-event(Phase2AcceptedInnerSender(binding)) ==> inj-event(Phase2PinnedInnerSender(binding)) is true."
    require_exact(wanted, "Phase-2 inner-sender binding correspondence")
  } else if (scenario == "phase2-assigned-id-weak") {
    if (query_count != 13) {
      reject("expected 13 weak Phase-2 assigned-ID queries, saw " query_count)
    }
    wanted = "Query not event(Phase2ResponseAttempted(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 relabeled assigned-ID attempt")
    wanted = "Query not event(Phase2OuterIdentityGateReached(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 retained outer-identity gate")
    wanted = "Query not event(Phase2InnerSenderGateReached(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 retained inner-sender gate")
    wanted = "Query not event(Phase2AuthenticatedFrameOpened(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 genuine frame opening")
    wanted = "Query not event(Phase2GenuineAssignedPrefixObserved(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 original authenticated prefix")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[])) is false."
    require_exact(wanted, "weak Phase-2 relabeled assigned-ID commit")
    wanted = "Query not event(Phase2RelabeledAssignedIdCommitted(PHASE2_RELABELED_ASSIGNED_ID_WITNESS[],queried_authenticated_binding,queried_outer_binding)) is false."
    require_exact(wanted, "weak Phase-2 explicit mismatched commit")
    wanted = "Query not attacker(PHASE2_ASSIGNED_ID_BINDING_CANARY[]) is false."
    require_exact(wanted, "weak Phase-2 observable commit canary")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_WRONG_OUTER_IDENTITY_WITNESS[])) is true."
    require_exact(wanted, "weak Phase-2 retained outer-identity rejection")
    wanted = "Query not event(Phase2ResponseCommitted(PHASE2_WRONG_INNER_SENDER_WITNESS[])) is true."
    require_exact(wanted, "weak Phase-2 retained inner-sender rejection")
    wanted = "Query inj-event(Phase2AcceptedOuterIdentity(binding)) ==> inj-event(Phase2PinnedOuterIdentity(binding)) is true."
    require_exact(wanted, "weak Phase-2 retained outer-identity correspondence")
    wanted = "Query inj-event(Phase2AcceptedAssignedPrefix(binding)) ==> inj-event(Phase2AuthenticatedAssignedPrefix(binding)) is false."
    require_exact(wanted, "weak Phase-2 broken assigned-ID correspondence")
    wanted = "Query inj-event(Phase2AcceptedInnerSender(binding)) ==> inj-event(Phase2PinnedInnerSender(binding)) is true."
    require_exact(wanted, "weak Phase-2 retained inner-sender correspondence")
  } else if (scenario == "later-sequence-registration") {
    if (query_count != 18) {
      reject("expected 18 later-sequence registration queries, saw " query_count)
    }

    later_first_response = "kex_response(server_identity_1,server_ephemeral_3,kem_ciphertext_3,first_frame_1,assigned_key_id_5)"
    later_third_response = "kex_response(server_identity_1,server_ephemeral_3,kem_ciphertext_3,third_frame_1,assigned_key_id_5)"
    later_binding = "beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver))"
    later_opened_payload = "registration_payload(" later_binding ",LATER_REGISTRATION_SEQ3_PAYLOAD[])"
    later_commit_arguments = "LATER_REGISTRATION_FAITHFUL_WITNESS[],session_5,root_5," later_third_response "," later_seq3 ",sender,assigned_key_id_5,opened_payload_2,LATER_REGISTRATION_SEQ3_PAYLOAD[],third_frame_1,material,receive_state_term,committed_ratchet_4"

    later_expected[1] = "Query not event(LaterRegistrationOriginalResponseIssued(LATER_REGISTRATION_ORIGINAL_WITNESS[],session_5,root_5,first_frame_1," later_first_response ")) is false."
    later_expected[2] = "Query not event(LaterRegistrationSubstitutionSelected(LATER_REGISTRATION_SUBSTITUTION_WITNESS[],session_5,root_5," later_first_response "," later_third_response ")) is false."
    later_expected[3] = "Query not event(LaterRegistrationFaithfulAttempted(LATER_REGISTRATION_FAITHFUL_WITNESS[],candidate_1)) is false."
    later_expected[4] = "Query not event(LaterRegistrationGeneralReceiveOpened(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_5," later_seq3 ",sender," later_binding ",LATER_REGISTRATION_SEQ3_PAYLOAD[]," later_opened_payload ",frame)) is false."
    later_expected[5] = "Query not event(LaterRegistrationCommitted(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_5,root_5,kex_response(server_identity_1,server_ephemeral_3,kem_ciphertext_3,frame,receiver)," later_seq3 ",sender,receiver," later_opened_payload ",LATER_REGISTRATION_SEQ3_PAYLOAD[],frame,material,receive_state_term,committed_ratchet_4)) is false."
    later_expected[6] = "Query not event(LaterRegistrationReturned(LATER_REGISTRATION_FAITHFUL_WITNESS[],LATER_REGISTRATION_SEQ3_PAYLOAD[])) is false."
    later_expected[7] = "Query not event(LaterRegistrationPoststatePublished(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_5,root_5,zero_sequence," later_send_chain "," later_seq3 "," later_chain4 "," later_cache "," later_ratchet ")) is false."
    later_expected[8] = "Query not event(LaterRegistrationTargetUnavailable(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_5," later_seq3 "," later_material3 "," later_cache "," later_ratchet ")) is false."
    later_expected[9] = "Query not event(LaterRegistrationFirstOnlyAttempted(LATER_REGISTRATION_FIRST_ONLY_WITNESS[],candidate_1)) is false."
    later_expected[10] = "Query not event(LaterRegistrationFirstOnlyGateReached(LATER_REGISTRATION_FIRST_ONLY_WITNESS[]," later_seq3 ",candidate_1)) is false."
    later_expected[11] = "Query not event(LaterRegistrationFirstOnlyGatePassed(LATER_REGISTRATION_FIRST_ONLY_WITNESS[]," later_seq3 ",candidate_1)) is true."
    later_expected[12] = "Query not event(LaterRegistrationCommitted(LATER_REGISTRATION_FIRST_ONLY_WITNESS[],session_5,root_5,candidate_1,message_sequence_3,sender,receiver,opened_payload_2,plaintext_3,frame,material,receive_state_term,committed_ratchet_4)) is true."
    later_expected[13] = "Query not attacker(LATER_REGISTRATION_FIRST_ONLY_CANARY[]) is true."
    later_expected[14] = "Query inj-event(LaterRegistrationCommitted(" later_commit_arguments ")) ==> inj-event(LaterRegistrationSubstitutionSelected(LATER_REGISTRATION_SUBSTITUTION_WITNESS[],session_5,root_5," later_first_response "," later_third_response ")) is true."
    later_expected[15] = "Query inj-event(LaterRegistrationCommitted(" later_commit_arguments ")) ==> inj-event(LaterRegistrationServerFrameSent(session_5,root_5,original_response_1," later_seq3 ",sender,assigned_key_id_5,LATER_REGISTRATION_SEQ3_PAYLOAD[],third_frame_1,material)) is true."
    later_expected[16] = "Query inj-event(LaterRegistrationServerFrameSent(session_5,root_5," later_first_response "," later_seq3 ",sender,assigned_key_id_5,LATER_REGISTRATION_SEQ3_PAYLOAD[],third_frame_1,material)) ==> inj-event(LaterRegistrationOriginalResponseIssued(LATER_REGISTRATION_ORIGINAL_WITNESS[],session_5,root_5,first_frame_1," later_first_response ")) is true."
    later_expected[17] = "Query inj-event(LaterRegistrationFaithfulAttempted(LATER_REGISTRATION_FAITHFUL_WITNESS[],candidate_1)) ==> inj-event(LaterRegistrationSubstitutionSelected(LATER_REGISTRATION_SUBSTITUTION_WITNESS[],session_5,root_5,original_response_1,candidate_1)) is true."
    later_expected[18] = "Query inj-event(LaterRegistrationFirstOnlyAttempted(LATER_REGISTRATION_FIRST_ONLY_WITNESS[],candidate_1)) ==> inj-event(LaterRegistrationSubstitutionSelected(LATER_REGISTRATION_SUBSTITUTION_WITNESS[],session_5,root_5,original_response_1,candidate_1)) is true."
    for (later_index = 1; later_index <= 18; later_index++) {
      require_exact(later_expected[later_index],
                    "later-sequence registration result")
    }
  } else if (scenario == "post-registration-ratchet") {
    if (query_count != 27) {
      reject("expected 27 post-registration ratchet queries, saw " query_count)
    }
    post_registration_expected[1] = "Query not event(PostRegistrationHandoff(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_6,root_6,response,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[2] = "Query not event(PostRegistrationBranchStarted(POST_REGISTRATION_FAITHFUL[],session_6,root_6,response,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[3] = "Query not event(PostRegistrationAttempted(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[4] = "Query not event(PostRegistrationOpenCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))))) is false."
    post_registration_expected[5] = "Query not event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),first_sequence,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ1_PAYLOAD[]),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[6] = "Query not event(PostRegistrationKdfCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,material_12)) is true."
    post_registration_expected[7] = "Query not event(PostRegistrationAttempted(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[8] = "Query not event(PostRegistrationRejected(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[9] = "Query not event(PostRegistrationKdfCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,material_12)) is true."
    post_registration_expected[10] = "Query not event(PostRegistrationOpenCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,frame,sequence_1,material_12)) is true."
    post_registration_expected[11] = "Query not event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,sender,receiver,ad,frame,sequence_1,plaintext_4,state)) is true."
    post_registration_expected[12] = "Query not event(PostRegistrationReplayAccepted(POST_REGISTRATION_FAITHFUL[],session_6,frame,plaintext_4,state)) is true."
    post_registration_expected[13] = "Query not event(PostRegistrationKdfCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_FUTURE[],session_6,hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)))) is false."
    post_registration_expected[14] = "Query not event(PostRegistrationOpenCalled(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_FUTURE[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,next_sequence(next_sequence(next_sequence(first_sequence))),sender),next_sequence(next_sequence(next_sequence(first_sequence))),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))))) is false."
    post_registration_expected[15] = "Query not event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_FUTURE[],session_6,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),crypto_frame(ciphertext_6,tag_6,commitment_6,next_sequence(next_sequence(next_sequence(first_sequence))),sender),next_sequence(next_sequence(next_sequence(first_sequence))),POST_REGISTRATION_SEQ4_PAYLOAD[],later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(next_sequence(first_sequence))),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[16] = "Query not event(PostRegistrationFinalState(POST_REGISTRATION_FAITHFUL[],session_6,root_6,zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),next_sequence(next_sequence(next_sequence(first_sequence))),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(next_sequence(first_sequence))),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[17] = "Query not event(PostRegistrationTargetUnavailable(POST_REGISTRATION_FAITHFUL[],session_6,next_sequence(next_sequence(next_sequence(first_sequence))),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(next_sequence(first_sequence))),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))))) is false."
    post_registration_expected[18] = "Query not event(PostRegistrationBranchStarted(POST_REGISTRATION_RETAIN_CONSUMED[],session_6,root_6,response,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[19] = "Query not event(PostRegistrationReturned(POST_REGISTRATION_RETAIN_CONSUMED[],POST_REGISTRATION_CACHED[],session_6,sender,receiver,beaconcrypt_associated_data(tag_ed25519(server_identity_1),tag_ed25519(beacon_identity_3),pqxdh_domain,symmetric_ratchet_domain),crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),first_sequence,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ1_PAYLOAD[]),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[20] = "Query not event(PostRegistrationReplayAccepted(POST_REGISTRATION_RETAIN_CONSUMED[],session_6,crypto_frame(ciphertext_6,tag_6,commitment_6,first_sequence,sender),registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ1_PAYLOAD[]),later_registration_ratchet_state(zero_sequence,hkdf_second_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty)))))) is false."
    post_registration_expected[21] = "Query not attacker(POST_REGISTRATION_REPLAY_CANARY[]) is false."
    post_registration_expected[22] = "Query inj-event(PostRegistrationHandoff(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_6,root_6,response,sender,receiver,ad,state)) ==> inj-event(LaterRegistrationCommitted(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_6,root_6,response,next_sequence(next_sequence(first_sequence)),sender,receiver,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ3_PAYLOAD[]),LATER_REGISTRATION_SEQ3_PAYLOAD[],frame,material_12,receive_state(next_sequence(next_sequence(first_sequence)),hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),receive_cache_entry(next_sequence(first_sequence),ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_entry(first_sequence,ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain)),hkdf_final_12(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_6,symmetric_ratchet_domain)),symmetric_ratchet_domain))),receive_cache_empty))),state)) is true."
    post_registration_expected[23] = "Query event(PostRegistrationBranchStarted(witness_6,session_6,root_6,response,sender,receiver,ad,state)) ==> event(PostRegistrationHandoff(LATER_REGISTRATION_FAITHFUL_WITNESS[],session_6,root_6,response,sender,receiver,ad,state)) is true."
    post_registration_expected[24] = "Query inj-event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,sender,receiver,ad,frame,first_sequence,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ1_PAYLOAD[]),state)) ==> inj-event(LaterRegistrationServerFrameSent(session_6,root_6,original,first_sequence,sender,receiver,LATER_REGISTRATION_SEQ1_PAYLOAD[],frame,material_12)) is true."
    post_registration_expected[25] = "Query inj-event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_FUTURE[],session_6,sender,receiver,ad,frame,next_sequence(next_sequence(next_sequence(first_sequence))),POST_REGISTRATION_SEQ4_PAYLOAD[],state)) ==> inj-event(PostRegistrationServerFrameSent(session_6,root_6,original,next_sequence(next_sequence(next_sequence(first_sequence))),sender,receiver,POST_REGISTRATION_SEQ4_PAYLOAD[],frame,material_12)) is true."
    post_registration_expected[26] = "Query inj-event(PostRegistrationServerFrameSent(session_6,root_6,original,next_sequence(next_sequence(next_sequence(first_sequence))),sender,receiver,POST_REGISTRATION_SEQ4_PAYLOAD[],frame,material_12)) ==> inj-event(LaterRegistrationServerFrameSent(session_6,root_6,original,next_sequence(next_sequence(first_sequence)),sender,receiver,LATER_REGISTRATION_SEQ3_PAYLOAD[],third_frame_1,third_material)) is true."
    post_registration_expected[27] = "Query inj-event(PostRegistrationRejected(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_REPLAY[],session_6,frame,state,state)) ==> inj-event(PostRegistrationReturned(POST_REGISTRATION_FAITHFUL[],POST_REGISTRATION_CACHED[],session_6,sender,receiver,ad,frame,first_sequence,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ1_PAYLOAD[]),state)) is true."
    for (post_registration_index = 1; post_registration_index <= 27; post_registration_index++) {
      require_exact(post_registration_expected[post_registration_index],
                    "post-registration ratchet result " post_registration_index)
    }
  } else if (scenario == "baseline" ||
             scenario == "active-classical") {
    if (query_count != 12) {
      reject("expected 12 " scenario " queries, saw " query_count)
    }

    baseline_secret[1] = "INITIAL_SECRET"
    baseline_secret[2] = "CACHED_SECRET"
    baseline_secret[3] = "ADVANCE_SECRET"
    baseline_secret[4] = "FUTURE_SECRET"
    baseline_secret[5] = "BEACON_RECORD_SECRET"
    for (secret_index = 1; secret_index <= 5; secret_index++) {
      wanted = "Query not attacker(" baseline_secret[secret_index] "[]) is true."
      found = 0
      for (query_index = 1; query_index <= query_count; query_index++) {
        if (query[query_index] == wanted) {
          found = 1
        }
      }
      if (!found) {
        reject("missing " scenario " secrecy result: " wanted)
      }
    }

    expected_correspondence[1] = "Query inj-event(ServerAccepted(" accepted_arguments ")) ==> inj-event(BeaconInitiated(" registration_arguments ")) is true."
    expected_correspondence[2] = "Query inj-event(ServerBundleAccepted(bundle)) ==> inj-event(BeaconBundleInitiated(bundle)) is true."
    expected_correspondence[3] = "Query inj-event(ServerAccepted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[4] = "Query inj-event(RegistrationConsumed(" registration_arguments ")) ==> inj-event(BeaconInitiated(" registration_arguments ")) is true."
    expected_correspondence[5] = "Query inj-event(ServerResponseAborted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[6] = "Query inj-event(BeaconCommitted(transcript)) ==> inj-event(ServerCommitted(transcript)) is true."
    expected_correspondence[7] = "Query inj-event(MessageReceived(" message_arguments ")) ==> inj-event(MessageSent(" message_arguments ")) is true."
    for (correspondence_index = 1; correspondence_index <= 7; correspondence_index++) {
      require_exact(expected_correspondence[correspondence_index], scenario " correspondence")
    }
  } else if (scenario == "reachability") {
    if (query_count != 8) {
      reject("expected 8 reachability queries, saw " query_count)
    }

    required[1] = "Query not event(ServerAccepted(" accepted_arguments ")) is false."
    required[2] = "Query not event(ServerBundleAccepted(bundle)) is false."
    required[3] = "Query not event(RegistrationReplayRejected(" registration_arguments ")) is false."
    required[4] = "Query not event(ServerResponseAborted(" accepted_arguments ")) is false."
    required[5] = "Query not event(BeaconCommitted(transcript)) is false."
    required[6] = "Query not event(MessageReceived(" message_arguments ")) is false."
    required[7] = "Query not event(MaliciousRegistrationCommitted(transcript,plaintext_2)) is false."
    required[8] = "Query not attacker(MALICIOUS_TASK_SECRET[]) is false."
    for (required_index = 1; required_index <= 8; required_index++) {
      require_exact(required[required_index], "reachability")
    }
  } else if (scenario == "compromise") {
    if (query_count != 5) {
      reject("expected 5 compromise queries, saw " query_count)
    }

    expected["INITIAL_SECRET"] = "true"
    expected["ADVANCE_SECRET"] = "true"
    expected["CACHED_SECRET"] = "false"
    expected["FUTURE_SECRET"] = "false"
    expected["BEACON_RECORD_SECRET"] = "false"

    for (secret in expected) {
      wanted = "Query not attacker(" secret "[]) is " expected[secret] "."
      found = 0
      for (query_index = 1; query_index <= query_count; query_index++) {
        if (query[query_index] == wanted) {
          found = 1
        }
      }
      if (!found) {
        reject("missing expected compromise result: " wanted)
      }
    }
  } else if (scenario == "failed-receive") {
    if (query_count != 17) {
      reject("expected 17 state-neutral receive queries, saw " query_count)
    }

    receive_secret[1] = "RECEIVE_PAST_SECRET"
    receive_secret[2] = "RECEIVE_SKIPPED_SECRET"
    receive_secret[3] = "RECEIVE_TARGET_SECRET"
    receive_secret[4] = "RECEIVE_MAX_GAP_SECRET"
    receive_secret[5] = "RECEIVE_CACHED_SECRET"
    receive_secret[6] = "RECEIVE_AFTER_RELEASE_SECRET"
    for (secret_index = 1; secret_index <= 6; secret_index++) {
      wanted = "Query not attacker(" receive_secret[secret_index] "[]) is true."
      require_exact(wanted, "state-neutral receive secrecy")
    }

    receive_correspondence[1] = "Query inj-event(ReceiveRejectionRetried(" receive_rejected_arguments ")) ==> inj-event(ReceiveRejectedNeutral(" receive_rejected_arguments ")) is true."
    receive_correspondence[2] = "Query inj-event(ReceiveFutureAccepted(" receive_future_arguments ")) ==> inj-event(ReceiveRejectionRetried(" receive_rejected_arguments ")) is true."
    receive_correspondence[3] = "Query inj-event(ReceiveHonestFutureDelivered(" receive_future_arguments ")) ==> inj-event(ReceiveFutureAccepted(" receive_future_arguments ")) is true."
    receive_correspondence[4] = "Query inj-event(ReceiveFutureAccepted(" receive_future_arguments ")) ==> inj-event(MessageKeyUnavailable(session_3,beacon_role,server_to_beacon,target_sequence_2,target_material_1)) is true."
    receive_correspondence[5] = "Query inj-event(ReceiveReplayRejected(" receive_future_arguments ")) ==> inj-event(ReceiveFutureAccepted(" receive_future_arguments ")) is true."
    receive_correspondence[6] = "Query inj-event(ReceiveDelayedCachedAccepted(" receive_delayed_arguments ")) ==> inj-event(MessageKeyCached(session_3,beacon_role,server_to_beacon,delayed_sequence,delayed_material)) is true."
    receive_correspondence[7] = "Query inj-event(ReceiveDelayedCachedAccepted(" receive_delayed_arguments ")) ==> inj-event(MessageKeyUnavailable(session_3,beacon_role,server_to_beacon,delayed_sequence,delayed_material)) is true."
    receive_correspondence[8] = "Query inj-event(ReceiveMaximumGapAccepted(" receive_maximum_arguments ")) ==> inj-event(MessageKeyUnavailable(session_3,beacon_role,server_to_beacon,target_sequence_2,target_material_1)) is true."
    receive_correspondence[9] = "Query inj-event(ReceiveCachedKeyConsumed(" receive_cached_arguments ")) ==> inj-event(MessageKeyUnavailable(session_3,beacon_role,server_to_beacon,cached_sequence,cached_material)) is true."
    receive_correspondence[10] = "Query inj-event(ReceiveAfterCapacityReleaseAccepted(" receive_after_release_arguments ")) ==> inj-event(MessageKeyUnavailable(session_3,beacon_role,server_to_beacon,target_sequence_2,target_material_1)) is true."
    receive_correspondence[11] = "Query inj-event(MessageReceived(" receive_message_arguments ")) ==> inj-event(MessageSent(" receive_message_arguments ")) is true."
    for (correspondence_index = 1;
         correspondence_index <= 11;
         correspondence_index++) {
      require_exact(receive_correspondence[correspondence_index],
                    "state-neutral receive correspondence")
    }
  } else if (scenario == "failed-receive-reachability") {
    if (query_count != 12) {
      reject("expected 12 state-neutral receive reachability queries, saw " query_count)
    }

    receive_reachable[1] = "Query not event(ReceiveRejectedNeutral(" receive_rejected_arguments ")) is false."
    receive_reachable[2] = "Query not event(ReceiveRejectionRetried(" receive_rejected_arguments ")) is false."
    receive_reachable[3] = "Query not event(ReceiveFutureAccepted(" receive_reachable_future_arguments ")) is false."
    receive_reachable[4] = "Query not event(ReceiveHonestFutureDelivered(" receive_reachable_future_arguments ")) is false."
    receive_reachable[5] = "Query not event(ReceiveReplayRejected(" receive_reachable_future_arguments ")) is false."
    receive_reachable[6] = "Query not event(ReceiveDelayedCachedAccepted(" receive_reachable_delayed_arguments ")) is false."
    receive_reachable[7] = "Query not event(ReceiveMaximumGapAccepted(" receive_reachable_maximum_arguments ")) is false."
    receive_reachable[8] = "Query not event(ReceiveCapacityRejected(" receive_capacity_arguments ")) is false."
    receive_reachable[9] = "Query not event(ReceiveCachedKeyConsumed(" receive_cached_arguments ")) is false."
    receive_reachable[10] = "Query not event(ReceiveAfterCapacityReleaseAccepted(" receive_reachable_after_release_arguments ")) is false."
    receive_reachable[11] = "Query not event(MaliciousRegistrationCommitted(" receive_malicious_commit_arguments ")) is false."
    receive_reachable[12] = "Query not attacker(MALICIOUS_TASK_SECRET[]) is false."
    for (required_index = 1; required_index <= 12; required_index++) {
      require_exact(receive_reachable[required_index],
                    "state-neutral receive reachability")
    }
  } else if (scenario == "failed-receive-compromise") {
    if (query_count != 9) {
      reject("expected 9 state-neutral receive compromise queries, saw " query_count)
    }

    receive_compromise_secret[1] = "Query not attacker(RECEIVE_PAST_SECRET[]) is true."
    receive_compromise_secret[2] = "Query not attacker(RECEIVE_SKIPPED_SECRET[]) is false."
    receive_compromise_secret[3] = "Query not attacker(RECEIVE_TARGET_SECRET[]) is false."
    receive_compromise_secret[4] = "Query not attacker(RECEIVE_MAX_GAP_SECRET[]) is true."
    receive_compromise_secret[5] = "Query not attacker(RECEIVE_CACHED_SECRET[]) is true."
    receive_compromise_secret[6] = "Query not attacker(RECEIVE_AFTER_RELEASE_SECRET[]) is true."
    for (secret_index = 1; secret_index <= 6; secret_index++) {
      require_exact(receive_compromise_secret[secret_index],
                    "state-neutral receive compromise secrecy")
    }

    receive_compromise_query[1] = "Query inj-event(ReceiveFutureAccepted(" receive_future_arguments ")) ==> inj-event(ReceiveStateCompromised(session_3,target_sequence_2,entry_state,entry_state)) is true."
    receive_compromise_query[2] = "Query inj-event(ReceiveHonestFutureDelivered(" receive_future_arguments ")) ==> inj-event(ReceiveStateCompromised(session_3,target_sequence_2,entry_state,entry_state)) is true."
    receive_compromise_query[3] = "Query inj-event(MessageReceived(" receive_message_arguments ")) ==> inj-event(MessageSent(" receive_message_arguments ")) is false."
    for (correspondence_index = 1;
         correspondence_index <= 3;
         correspondence_index++) {
      require_exact(receive_compromise_query[correspondence_index],
                    "state-neutral receive compromise correspondence")
    }
  } else if (scenario == "failed-receive-compromise-reachability") {
    if (query_count != 2) {
      reject("expected 2 state-neutral receive compromise reachability queries, saw " query_count)
    }
    wanted = "Query not event(ReceiveStateCompromised(session_3,target_sequence_2,unchanged_state,unchanged_state)) is false."
    require_exact(wanted, "state-neutral receive compromise reachability")
    wanted = "Query not event(ReceiveHonestFutureDelivered(" receive_reachable_future_arguments ")) is false."
    require_exact(wanted,
                  "state-neutral post-compromise delivery reachability")
  } else {
    reject("unknown scenario: " scenario)
  }

  if (failed) {
    exit 1
  }
  print "ProVerif " scenario " results matched the reviewed expectations."
}
