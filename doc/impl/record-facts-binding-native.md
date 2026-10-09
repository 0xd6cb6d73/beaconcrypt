# Caller-known native record witnesses

`PqxdhRecordFactsBindingNative` connects the literal native Server and Beacon send/receive results to the shared random-oracle cache. Its conclusion concerns actual raw bytes or ciphertext returned by the source interpreter. It never inserts recovered plaintext into an attacker request and never substitutes a successful answer for an optional failure.

`native_serverRaw_shared` and `native_beaconRaw_shared` show that a successful receive on a caller-known handle leaves a shared-cache witness for the commitment decoded from the actual raw request. `native_serverSend_shared` and `native_beaconSend_shared` give the corresponding witness for the actual returned ciphertext. These four source wrappers allow every key mode and require no honest-handle selection. Sends use the existing frame-writer/readback contract; receives use the actual decoder result.

`KnownEntryFacts` is an internal per-entry invariant: whenever a published or successfully received transcript entry belongs to a handle that is caller-known in the indicated control state, its exact record has a shared-cache commitment witness. `native_knownEntryFacts_before` derives this invariant for every literal native query and reply, including unrelated commands and rejected calls. It retains the complete native result state.

`published_known_mono`, `accepted_known_mono`, and `knownEntryFacts_mono` transport earlier successful-record evidence across an actual forward control step and shared-cache growth. A previously hidden endpoint cannot become caller-known: its installed slot persists, while a caller-known handle has no installed hidden slot. The proof uses the earlier source-derived known-or-hidden classification. It does not infer that final hidden state was already hidden at the record operation.

`native_knownEntryFacts` places the literal entry invariant at the complete final control and private state. `native_send_shared` supplies the same final caller-known witness for experiment-generated secrecy sends. These transport conclusions use the already proved safe source state and all non-real record modes. Those are operational hypotheses discharged by the initialized global run, rather than new primitive security assumptions.

No operation or oracle call is added by these evidence theorems. Actual sampling, cryptographic services, source counters, cache effects, optional answers, and other private state remain those of the existing interpreter. These witnesses do not declare that ambient work is free and do not replace the source or reduction query bills.

The complete adaptive transcript invariant and its initialized-run instance remain a separate additive join. Only after that join may the internal `LedgerEvidence` obligations in the binding-event module be discharged. This module does not assert a collision probability bound or a final record-layer security theorem.
