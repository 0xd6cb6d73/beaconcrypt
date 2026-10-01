# Private record state in the ordinary random privacy experiment

The 17 statements in `PqxdhServerAuthPublicationPrivateView` establish a complete source-view comparison inside the existing ordinary modified nonce-AEAD random experiment. They preserve all public hash effects and derive the first selected seal's actual independent body, tag and commitment draws. This is an unconditional operational sampling result. It does not condition those draws on a writer succeeding or failing, and it does not yet prove a publication-authentication probability bound.

## Exact state and source interpreter

The mathematical state retains the full `ReceiveState`, the redundant ordinary seal history from `AdaptiveCtxDirectReplay.directWithBase`, and the ordinary primitive's `ModifiedNonceAeadHandlerState`. The `project` function removes every tag-bearing private record copy: the suffix cache, CTX successful records, receive `privateInputs`, redundant ordinary records and primitive successful records. It retains the full public cache and public input history, both nonce-control lists, and the raw-attempt counter. `project_idempotent` checks this projection.

`step` executes the unchanged direct source handler through the unchanged ordinary random primitive. `uniform_step`, `lifted_step` and `public_step` identify its complete source coin and public-hash effects. Public hashing continues to query the actual complete-input public cache; it is not replaced by a constant or a private table. `program_source` identifies the flattened handler with the original full adaptive direct-source experiment, including all three retained states.

`public_project` and `quiet_project` show that source coins and public hashes commute with the private projection. `program_project` lifts that equality through every possible adaptive reply and complete continuation of a source program with selected-seal and raw-query caps zero. `program_congr` compares any two full initial states with the same projection. Neither theorem assumes an independence law for those initial states. The continuation still sees each actual public hash or coin reply and may adapt its subsequent requests to it.

## Actual first-seal sampler

`private_step`, `seal_step` and `seal_base` expose the original private commitment lookup, actual optional ordinary ciphertext and redundant record update. They preserve the full private poststate until observation; no record is reconstructed from a writer's bytes.

`Unused` requires an empty selected suffix table and an empty primitive nonce list. `initial_unused` proves that condition for the literal existing random experiment. `quiet_unused` and `program_unused` retain it through all supported nonsealing, nonreceiving source prefixes. Thus public hash queries, including arbitrary strings that happen to match other inputs, cannot silently initialize this separate suffix table or the selected primitive's nonce control.

`first_seal` derives the exact projected result of the next source seal: sample the ordinary random body of the submitted plaintext length, sample its 16-byte tag, sample the fresh 64-byte commitment, and return that full actual record. Its public poststate changes only the nonce controls. Empty suffix-table use is explicit and comes from the preceding source invariant; it is not inferred from a marginal tag distribution.

`first_seal_suffix` retains the joint actual record and final projected public state through an arbitrary fixed adaptive suffix with no further selected seal or raw operation. This suffix is not supplied the seal reply. Its public cache work and reply-dependent execution remain present in the equality, as do all three original sampler draws. The theorem gives the concrete law needed to move an unobserved tag past a later public computation; it does not assume that an arbitrary ciphertext-reading adversary has this shape.

## Query scope and remaining consumer

Every operational equality retains the original oracle programs and sampler calls. A public hash may still incur its actual uniform digest work. A fresh selected seal still samples plaintext-length random body bytes, 16 tag bytes and 64 commitment bytes. This package does not declare local primitive evaluation, journal processing or deterministic source work free. It adds no new primitive contract, excludes no known-key byte alias and proves no source-key independence.

The actual forced-frame reference must still be joined to this law. That consumer must show that the original source control and ghost-erasure comparison give precisely a suffix which is not supplied the selected record, retain the first-raw cutoff and source-derived budgets under its changed public reply, and associate the actual seal with its ordered writer observations. The separate tag-hit probability, actual unpublished-branch inclusion, ordinary privacy reduction and new observation-specific R1/five-hop transport remain necessary. `PqxdhServerAuthPublicationForcedFrame` and `PqxdhServerAuthPublicationGhost` supply earlier pieces, but their names alone do not establish that join.

This focused package has direct single-file Lean and guarded standard-axiom checks. Central imports, inventory and aggregate validation will be updated with the reviewed consuming cohort.
