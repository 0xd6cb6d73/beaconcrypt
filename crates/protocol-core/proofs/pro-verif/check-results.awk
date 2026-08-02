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

  if (scenario == "baseline" && $0 !~ / is true\.$/) {
    reject("baseline query was not true: " $0)
  }

  if (scenario == "reachability" && $0 !~ / is false\.$/) {
    reject("reachability witness was not found: " $0)
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
  } else {
    reject("unknown scenario: " scenario)
  }

  if (failed) {
    exit 1
  }
  print "ProVerif " scenario " results matched the reviewed expectations."
}
