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
  commit_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,assigned_key_id_3,root_input_3,root_3,associated_data_3,session_4,origin_1"
  message_arguments = "session_4,message_direction,message_sequence_6,sender,receiver,plaintext_2"
  malicious_commit_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,assigned_key_id_3,root_input_3,root_3,associated_data_3,session_4,plaintext_2"
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
  receive_malicious_commit_arguments = "server_identity_1,beacon_identity_2,init,registration_id_2,assigned_key_id_1,root_input_1,root_4,associated_data_9,session_3,plaintext_8"
  weak_aead_arguments = "left_key_1,right_key_1,left_context_1,right_context_1,left_plaintext_1,right_plaintext_1"

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
    if (query_count != 3) {
      reject("expected 3 active-quantum attack queries, saw " query_count)
    }

    wanted = "Query not attacker(INITIAL_SECRET[]) is false."
    require_exact(wanted, "active-quantum confidentiality break")
    wanted = "Query not event(QuantumInitialSecretRecovered(INITIAL_SECRET[])) is false."
    require_exact(wanted, "active-quantum recovery witness")
    active_quantum_arguments = "server_identity_2,beacon_identity_3,init,registration_id_2,root_input_3,root_3,origin_1"
    active_quantum_origin_arguments = "server_identity_2,beacon_identity_3,init,registration_id_2,origin_1"
    wanted = "Query inj-event(ServerAccepted(" active_quantum_arguments ")) ==> inj-event(BeaconInitiated(" active_quantum_origin_arguments ")) is false."
    require_exact(wanted, "active-quantum agreement break")
  } else if (scenario == "passive-reachability") {
    if (query_count != 6) {
      reject("expected 6 passive reachability queries, saw " query_count)
    }
    passive_commit_arguments = "server_identity_2,beacon_identity_2,init,registration_id_2,assigned_key_id_2,root_input_2,root_2,associated_data_2,session_3,origin_1"
    wanted = "Query not event(BeaconCommitted(" passive_commit_arguments ")) is false."
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
  } else if (scenario == "baseline" ||
             scenario == "active-classical") {
    if (query_count != 11) {
      reject("expected 11 " scenario " queries, saw " query_count)
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
    expected_correspondence[2] = "Query inj-event(ServerAccepted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[3] = "Query inj-event(RegistrationConsumed(" registration_arguments ")) ==> inj-event(BeaconInitiated(" registration_arguments ")) is true."
    expected_correspondence[4] = "Query inj-event(ServerResponseAborted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[5] = "Query inj-event(BeaconCommitted(" commit_arguments ")) ==> inj-event(ServerCommitted(" commit_arguments ")) is true."
    expected_correspondence[6] = "Query inj-event(MessageReceived(" message_arguments ")) ==> inj-event(MessageSent(" message_arguments ")) is true."
    for (correspondence_index = 1; correspondence_index <= 6; correspondence_index++) {
      require_exact(expected_correspondence[correspondence_index], scenario " correspondence")
    }
  } else if (scenario == "reachability") {
    if (query_count != 7) {
      reject("expected 7 reachability queries, saw " query_count)
    }

    required[1] = "Query not event(ServerAccepted(" accepted_arguments ")) is false."
    required[2] = "Query not event(RegistrationReplayRejected(" registration_arguments ")) is false."
    required[3] = "Query not event(ServerResponseAborted(" accepted_arguments ")) is false."
    required[4] = "Query not event(BeaconCommitted(" commit_arguments ")) is false."
    required[5] = "Query not event(MessageReceived(" message_arguments ")) is false."
    required[6] = "Query not event(MaliciousRegistrationCommitted(" malicious_commit_arguments ")) is false."
    required[7] = "Query not attacker(MALICIOUS_TASK_SECRET[]) is false."
    for (required_index = 1; required_index <= 7; required_index++) {
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
