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

  if ((scenario == "baseline" || scenario == "failed-receive") &&
      $0 !~ / is true\.$/) {
    reject(scenario " query was not true: " $0)
  }

  if ((scenario == "reachability" ||
       scenario == "failed-receive-reachability" ||
       scenario == "failed-receive-compromise-reachability") &&
      $0 !~ / is false\.$/) {
    reject(scenario " witness was not found: " $0)
  }
}

END {
  if (!in_summary) {
    reject("missing verification summary")
  }

  registration_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,origin_1"
  accepted_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,root_input_3,root_3,origin_1"
  commit_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,assigned_key_id_3,root_input_3,root_3,associated_data_3,session_4,origin_1"
  message_arguments = "session_4,message_direction,message_sequence_6,sender,receiver,plaintext_6"
  malicious_commit_arguments = "server_identity_3,beacon_identity_4,init,registration_id_4,assigned_key_id_3,root_input_3,root_3,associated_data_3,session_4,plaintext_6"
  failed_advanced_arguments = "session_5,target_sequence_2,target_material,forged_frame,ready_state_1,retained_state_2"
  failed_retry_arguments = failed_advanced_arguments ",full_state_2"
  failed_cache_arguments = "session_5,retained_state_2,full_state_2"
  failed_capacity_arguments = "session_5,target_sequence_2,capacity_sequence_1,capacity_frame,retained_state_2,full_state_2"
  failed_accepted_arguments = "session_5,target_sequence_2,sender,receiver,plaintext_5,accepted_frame_1,target_material,forged_frame,ready_state_1,retained_state_2,full_state_2,consumed_state_1"
  failed_reachable_accepted_arguments = "session_5,target_sequence_2,sender,receiver,FAILED_TARGET_SECRET[],accepted_frame_1,target_material,forged_frame,ready_state_1,retained_state_2,full_state_2,consumed_state_1"
  failed_consumed_arguments = "session_5,target_sequence_2,full_state_2,consumed_state_1"
  failed_after_release_arguments = "session_5,target_sequence_2,capacity_sequence_1,capacity_frame,retained_state_2,full_state_2,consumed_state_1,refilled_state_2"
  failed_compromise_arguments = "session_5,target_sequence_2,retained_state_2,full_state_2"
  failed_message_arguments = "session_5,message_direction,message_sequence_1,sender,receiver,plaintext_5"
  failed_malicious_commit_arguments = "server_identity_1,beacon_identity_2,init,registration_id_2,assigned_key_id_1,root_input_1,root_2,associated_data_8,session_5,plaintext_5"

  if (scenario == "baseline") {
    if (query_count != 11) {
      reject("expected 11 baseline queries, saw " query_count)
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
        reject("missing baseline secrecy result: " wanted)
      }
    }

    expected_correspondence[1] = "Query inj-event(ServerAccepted(" accepted_arguments ")) ==> inj-event(BeaconInitiated(" registration_arguments ")) is true."
    expected_correspondence[2] = "Query inj-event(ServerAccepted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[3] = "Query inj-event(RegistrationConsumed(" registration_arguments ")) ==> inj-event(BeaconInitiated(" registration_arguments ")) is true."
    expected_correspondence[4] = "Query inj-event(ServerResponseAborted(" accepted_arguments ")) ==> inj-event(RegistrationConsumed(" registration_arguments ")) is true."
    expected_correspondence[5] = "Query inj-event(BeaconCommitted(" commit_arguments ")) ==> inj-event(ServerCommitted(" commit_arguments ")) is true."
    expected_correspondence[6] = "Query inj-event(MessageReceived(" message_arguments ")) ==> inj-event(MessageSent(" message_arguments ")) is true."
    for (correspondence_index = 1; correspondence_index <= 6; correspondence_index++) {
      require_exact(expected_correspondence[correspondence_index], "baseline correspondence")
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
    if (query_count != 13) {
      reject("expected 13 failed-receive queries, saw " query_count)
    }

    failed_secret[1] = "FAILED_PAST_SECRET"
    failed_secret[2] = "FAILED_SKIPPED_SECRET"
    failed_secret[3] = "FAILED_TARGET_SECRET"
    failed_secret[4] = "FAILED_FUTURE_SECRET"
    for (secret_index = 1; secret_index <= 4; secret_index++) {
      wanted = "Query not attacker(" failed_secret[secret_index] "[]) is true."
      require_exact(wanted, "failed-receive secrecy")
    }

    failed_correspondence[1] = "Query inj-event(FailedReceiveStateAdvanced(" failed_advanced_arguments ")) ==> inj-event(MessageKeyCached(session_5,beacon_role,server_to_beacon,target_sequence_2,target_material)) is true."
    failed_correspondence[2] = "Query inj-event(FailedReceiveRetryRetained(" failed_retry_arguments ")) ==> inj-event(FailedReceiveStateAdvanced(" failed_advanced_arguments ")) is true."
    failed_correspondence[3] = "Query inj-event(FailedReceiveCapacityRejected(" failed_capacity_arguments ")) ==> inj-event(FailedReceiveCacheFilled(" failed_cache_arguments ")) is true."
    failed_correspondence[4] = "Query inj-event(FailedReceiveAccepted(" failed_accepted_arguments ")) ==> inj-event(FailedReceiveRetryRetained(" failed_retry_arguments ")) is true."
    failed_correspondence[5] = "Query inj-event(FailedReceiveAccepted(" failed_accepted_arguments ")) ==> inj-event(FailedReceiveKeyConsumed(" failed_consumed_arguments ")) is true."
    failed_correspondence[6] = "Query inj-event(FailedReceiveReplayRejected(" failed_accepted_arguments ")) ==> inj-event(FailedReceiveAccepted(" failed_accepted_arguments ")) is true."
    failed_correspondence[7] = "Query inj-event(FailedReceiveAfterCapacityReleaseAdmitted(" failed_after_release_arguments ")) ==> inj-event(FailedReceiveCapacityRejected(" failed_capacity_arguments ")) is true."
    failed_correspondence[8] = "Query inj-event(FailedReceiveAfterCapacityReleaseAdmitted(" failed_after_release_arguments ")) ==> inj-event(FailedReceiveKeyConsumed(" failed_consumed_arguments ")) is true."
    failed_correspondence[9] = "Query inj-event(MessageReceived(" failed_message_arguments ")) ==> inj-event(MessageSent(" failed_message_arguments ")) is true."
    for (correspondence_index = 1;
         correspondence_index <= 9;
         correspondence_index++) {
      require_exact(failed_correspondence[correspondence_index],
                    "failed-receive correspondence")
    }
  } else if (scenario == "failed-receive-reachability") {
    if (query_count != 11) {
      reject("expected 11 failed-receive reachability queries, saw " query_count)
    }

    failed_reachable[1] = "Query not event(FailedReceiveStateAdvanced(" failed_advanced_arguments ")) is false."
    failed_reachable[2] = "Query not event(FailedReceiveCacheFilled(" failed_cache_arguments ")) is false."
    failed_reachable[3] = "Query not event(FailedReceiveCapacityRejected(" failed_capacity_arguments ")) is false."
    failed_reachable[4] = "Query not event(FailedReceiveRetryRetained(" failed_retry_arguments ")) is false."
    failed_reachable[5] = "Query not event(FailedReceiveAccepted(" failed_reachable_accepted_arguments ")) is false."
    failed_reachable[6] = "Query not event(FailedReceiveKeyConsumed(" failed_consumed_arguments ")) is false."
    failed_reachable[7] = "Query not event(FailedReceiveHonestDelivery(" failed_reachable_accepted_arguments ")) is false."
    failed_reachable[8] = "Query not event(FailedReceiveReplayRejected(" failed_reachable_accepted_arguments ")) is false."
    failed_reachable[9] = "Query not event(FailedReceiveAfterCapacityReleaseAdmitted(" failed_after_release_arguments ")) is false."
    failed_reachable[10] = "Query not event(MaliciousRegistrationCommitted(" failed_malicious_commit_arguments ")) is false."
    failed_reachable[11] = "Query not attacker(MALICIOUS_TASK_SECRET[]) is false."
    for (required_index = 1; required_index <= 11; required_index++) {
      require_exact(failed_reachable[required_index],
                    "failed-receive reachability")
    }
  } else if (scenario == "failed-receive-compromise") {
    if (query_count != 7) {
      reject("expected 7 failed-receive compromise queries, saw " query_count)
    }

    failed_compromise_secret[1] = "Query not attacker(FAILED_PAST_SECRET[]) is true."
    failed_compromise_secret[2] = "Query not attacker(FAILED_SKIPPED_SECRET[]) is false."
    failed_compromise_secret[3] = "Query not attacker(FAILED_TARGET_SECRET[]) is false."
    failed_compromise_secret[4] = "Query not attacker(FAILED_FUTURE_SECRET[]) is false."
    for (secret_index = 1; secret_index <= 4; secret_index++) {
      require_exact(failed_compromise_secret[secret_index],
                    "failed-receive compromise secrecy")
    }

    failed_compromise_query[1] = "Query inj-event(FailedReceiveAccepted(" failed_accepted_arguments ")) ==> inj-event(FailedReceiveStateCompromised(" failed_compromise_arguments ")) is true."
    failed_compromise_query[2] = "Query inj-event(FailedReceiveHonestDelivery(" failed_accepted_arguments ")) ==> inj-event(FailedReceiveStateCompromised(" failed_compromise_arguments ")) is true."
    failed_compromise_query[3] = "Query inj-event(MessageReceived(" failed_message_arguments ")) ==> inj-event(MessageSent(" failed_message_arguments ")) is false."
    for (correspondence_index = 1;
         correspondence_index <= 3;
         correspondence_index++) {
      require_exact(failed_compromise_query[correspondence_index],
                    "failed-receive compromise correspondence")
    }
  } else if (scenario == "failed-receive-compromise-reachability") {
    if (query_count != 2) {
      reject("expected 2 failed-receive compromise reachability queries, saw " query_count)
    }
    wanted = "Query not event(FailedReceiveStateCompromised(" failed_compromise_arguments ")) is false."
    require_exact(wanted, "failed-receive compromise reachability")
    wanted = "Query not event(FailedReceiveHonestDelivery(" failed_reachable_accepted_arguments ")) is false."
    require_exact(wanted,
                  "failed-receive post-compromise delivery reachability")
  } else {
    reject("unknown scenario: " scenario)
  }

  if (failed) {
    exit 1
  }
  print "ProVerif " scenario " results matched the reviewed expectations."
}
