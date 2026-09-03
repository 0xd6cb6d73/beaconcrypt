# PQXDH F* surface migration audit

This inventory records every top-level declaration in `beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Pqxdh.Lemmas.fst` against the current Lean extraction. It distinguishes complete correspondence from a proof ingredient and from remaining work; totality alone does not discharge semantic obligations. No files under `BeaconcryptCore/Model/` are changed.

The new `Refinement/RatchetInterpreter.lean` binds one fixed pure request interpreter to the existing ratchet model through the checked extracted 76-byte decoder. `withInterpreter` retains the supplied AEAD operations and their existing correctness law while setting only the KDF fields. `interpreter_request_refines` derives response refinement from the extracted request's input and label invariants; it does not assume a successful decoder equation or a cryptographic response law.

The new `Refinement/PqxdhConcreteSession.lean` executes the actual extracted start/resume phases for both roles with one shared pure 64-byte interpreter. It proves exact initial byte halves, complete zero-state kernel correspondence, opposing directional chain and material equality, and session establishment from authenticated root-input equality under any fixed root derivation. `Refinement/PqxdhSessionLifecycle.lean` now composes complete terminating send and receive drivers into lifetime preservation of the paired session in both directions, for every target and optional callback result.

“Existing” denotes an existing checked semantic result; “New checked” denotes a result added during this migration. The direct raw-byte corollaries in `Refinement/PqxdhSurface.lean` now cover every non-lifecycle protocol statement, without the additional primitive representation premises required by earlier protocol refinements. Source-specific range-update helpers are superseded because the current extraction uses bounded array-building closures.

| F* declaration | Status | Lean correspondence or remaining obligation |
| --- | --- | --- |
| `update_at_range_byte_view` | Superseded helper | The current extraction builds arrays with `from_fn`; `PqxdhRefinement.from_fn_pure`, `index_usize_eq`, and the complete byte-layout theorems replace the old range-update proof obligations. |
| `honest_shared_secrets` | New checked premise equivalence | `PqxdhSurface.honest_shared_secrets_iff` equates the five field equalities with concrete shared-secret record equality. Primitive agreement remains a caller obligation. |
| `key_type_and_role_markers_are_disjoint` | New checked | `PqxdhSurface.key_type_and_role_markers_are_disjoint` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `sign_key_tag_is_exact` | Existing | `PqxdhRefinement.tag_sign_key_abs` proves the complete encoding. |
| `x25519_key_tag_is_exact` | Existing | `PqxdhRefinement.tag_x25519_key_abs` proves the complete encoding for every role byte. |
| `mlkem768_key_tag_is_exact` | Existing | `PqxdhRefinement.tag_mlkem768_key_abs` proves the complete encoding. |
| `sign_key_tag_round_trip` | New checked | `PqxdhSurface.sign_key_tag_round_trip` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `x25519_key_tag_round_trip` | New checked | `PqxdhSurface.x25519_key_tag_round_trip` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `x25519_key_roles_are_enforced` | New checked | `PqxdhSurface.x25519_key_roles_are_enforced` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `mlkem768_key_tag_round_trip` | New checked | `PqxdhSurface.mlkem768_key_tag_round_trip` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `beacon_start_validates` | New checked | `PqxdhSurface.beacon_start_validates` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `beacon_start_preserves_expected_server_binding` | New checked | `PqxdhSurface.beacon_start_validates` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `registration_id_is_exact` | Existing | `PqxdhRefinement.registration_id_abs` proves the complete identity/one-time-key concatenation. |
| `valid_shared_secrets` | New checked premise equivalence | `PqxdhSurface.valid_shared_secrets_iff` identifies the exact four extracted all-zero checks with `Pqxdh.dhNonZero (absDHs secrets)`. |
| `v_ROOT_RANGE_1` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `v_ROOT_RANGE_2` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `v_ROOT_RANGE_3` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `v_ROOT_RANGE_4` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `v_ROOT_RANGE_5` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `root_transcript_bytes` | Superseded helper | The generated `build_root_key_input` closure and `Pqxdh.pqxdhIKM`; complete correspondence is `PqxdhRefinement.build_root_key_input_abs`. |
| `root_transcript_byte_is_exact` | Existing | `PqxdhRefinement.build_root_key_input_abs` covers both the exact nonzero transcript and all-zero-DH rejection. |
| `valid_root_build_uses_exact_bytes` | Existing | `PqxdhRefinement.build_root_key_input_abs` covers both the exact nonzero transcript and all-zero-DH rejection. |
| `root_key_transcript_is_exact` | Existing | `PqxdhRefinement.build_root_key_input_abs` covers both the exact nonzero transcript and all-zero-DH rejection. |
| `all_zero_dh_is_rejected` | Existing | `PqxdhRefinement.build_root_key_input_abs` covers both the exact nonzero transcript and all-zero-DH rejection. |
| `honest_roles_build_the_same_root` | New checked | `PqxdhSurface.honest_roles_build_the_same_root` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `equal_root_inputs_derive_same_fixed_root` | New checked | `PqxdhConcreteSession.authenticated_roots_agree` uses equality under the supplied pure root derivation; general equal-input congruence is `congrArg`. |
| `authenticated_registration_derives_common_fixed_root` | New checked | `PqxdhConcreteSession.authenticated_roots_agree` uses equality under the supplied pure root derivation; general equal-input congruence is `congrArg`. |
| `v_AD_RANGE_1` | Superseded helper | The generated associated-data closure and `Pqxdh.assocData`; complete correspondence is `PqxdhRefinement.build_associated_data_abs`. |
| `v_AD_RANGE_2` | Superseded helper | The generated associated-data closure and `Pqxdh.assocData`; complete correspondence is `PqxdhRefinement.build_associated_data_abs`. |
| `v_AD_RANGE_3` | Superseded helper | The generated associated-data closure and `Pqxdh.assocData`; complete correspondence is `PqxdhRefinement.build_associated_data_abs`. |
| `v_AD_RANGE_4` | Superseded helper | The generated associated-data closure and `Pqxdh.assocData`; complete correspondence is `PqxdhRefinement.build_associated_data_abs`. |
| `associated_data_bytes` | Superseded helper | The generated associated-data closure and `Pqxdh.assocData`; complete correspondence is `PqxdhRefinement.build_associated_data_abs`. |
| `ad_range_to_byte` | Superseded helper | The current extraction builds arrays with `from_fn`; `PqxdhRefinement.from_fn_pure`, `index_usize_eq`, and the complete byte-layout theorems replace the old range-update proof obligations. |
| `ad_range_from_byte` | Superseded helper | The current extraction builds arrays with `from_fn`; `PqxdhRefinement.from_fn_pure`, `index_usize_eq`, and the complete byte-layout theorems replace the old range-update proof obligations. |
| `associated_data_byte_is_exact` | Existing | `PqxdhRefinement.build_associated_data_abs` proves the complete transcript. |
| `associated_data_build_uses_exact_bytes` | Existing | `PqxdhRefinement.build_associated_data_abs` proves the complete transcript. |
| `associated_data_is_exact` | Existing | `PqxdhRefinement.build_associated_data_abs` proves the complete transcript. |
| `honest_roles_build_the_same_associated_data` | New checked | `PqxdhSurface.honest_roles_build_the_same_associated_data` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `beacon_response_identity_mismatch_is_rejected` | New checked | `PqxdhSurface.beacon_response_identity_mismatch_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `beacon_successful_finish_preserves_binding_and_ad` | New checked | `PqxdhSurface.beacon_successful_finish_preserves_binding_and_ad` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `ratchet_initializations_are_complementary` | New checked | `PqxdhSurface.ratchet_initializations_are_complementary` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `initial_ratchet_chains_use_exact_root_and_directions` | New checked | `initializeBeacon_eq`, `initializeServer_eq`, and `initial_kernels_refine` in `PqxdhConcreteSession` prove exact request fields and complementary byte halves for every pure initial interpreter. |
| `concrete_session` | New relation | `PqxdhConcreteSession.ConcreteSession` combines both `KernelRefines` relations with send-origin derivational reachability. Receive-origin and cache-material reachability are already included in `KernelRefines`. |
| `concrete_initial_kernels_are_complementary` | New checked | `PqxdhConcreteSession.initialize_establishes_concrete_session` proves both initialization executions, initial reachability, cross-role chain equality, and material equality at every position. |
| `concrete_initial_kernels_are_reachable` | New checked | `PqxdhConcreteSession.initialize_establishes_concrete_session` proves both initialization executions, initial reachability, cross-role chain equality, and material equality at every position. |
| `concrete_directional_materials_agree` | New checked | `PqxdhConcreteSession.initialize_establishes_concrete_session` proves both initialization executions, initial reachability, cross-role chain equality, and material equality at every position. |
| `authenticated_registrations_establish_concrete_session` | New checked | `PqxdhConcreteSession.authenticated_registrations_establish_concrete_session` connects authenticated root agreement to candidate-bound beacon initialization, server initialization, and fixed-interpreter material streams. |
| `beacon_seal_server_open_preserves_concrete_session` | New checked | `PqxdhConcreteSession.beacon_seal_server_open_preserves_concrete_session` in `PqxdhSessionLifecycle.lean` proves exact complete `sealNext` and `receiveNext` executions and the resulting paired invariant for every target and optional callback outcome. No trace, helper-success, response-refinement, or callback-correctness premise is supplied by the caller. |
| `server_seal_beacon_open_preserves_concrete_session` | New checked | `PqxdhConcreteSession.server_seal_beacon_open_preserves_concrete_session` in `PqxdhSessionLifecycle.lean` proves exact complete `sealNext` and `receiveNext` executions and the resulting paired invariant for every target and optional callback outcome. No trace, helper-success, response-refinement, or callback-correctness premise is supplied by the caller. |
| `candidate_ratchet_initializations_are_complementary` | New checked | `PqxdhSurface.candidate_ratchet_initializations_are_complementary` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `registration_key_id_binding_is_exact` | Existing | `PqxdhRefinement.registration_key_id_binding_abs` proves exact `Pqxdh.LE64`; its proof handles every shift and byte conversion. |
| `registration_key_id_binding_has_le64_values` | Existing | `PqxdhRefinement.registration_key_id_binding_abs` proves exact `Pqxdh.LE64`; its proof handles every shift and byte conversion. |
| `exact_key_id_binding_authenticates` | New checked | `PqxdhSurface.exact_key_id_binding_authenticates` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `mismatched_authenticated_server_key_id_is_rejected` | New checked | `PqxdhSurface.mismatched_authenticated_server_key_id_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `mismatched_key_id_binding_is_rejected` | New checked | `PqxdhSurface.mismatched_key_id_binding_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `beacon_commit_preserves_authenticated_ids` | New checked | `PqxdhSurface.beacon_commit_preserves_authenticated_ids` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `fresh_registration_status_is_accepted` | New checked | `PqxdhSurface.fresh_registration_status_is_accepted` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `consumed_registration_status_is_rejected` | New checked | `PqxdhSurface.consumed_registration_status_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `server_rejects_consumed_registration` | New checked | `PqxdhSurface.server_rejects_consumed_registration` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `server_fresh_acceptance_shape` | New checked | `PqxdhSurface.server_fresh_acceptance_shape` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `next_server_key_id_is_checked` | Existing | `PqxdhRefinement.server_next_key_id_refines` permits the ideal counter to be instantiated with the concrete counter; `server_next_key_id_ok` additionally packages totality. |
| `server_binding_mismatch_is_rejected` | New checked | `PqxdhSurface.server_binding_mismatch_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `occupied_server_key_id_is_rejected` | New checked | `PqxdhSurface.occupied_server_key_id_is_rejected` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `available_server_key_id_candidate_shape` | New checked | `PqxdhSurface.available_server_key_id_candidate_shape` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `server_commit_shape` | Existing | `PqxdhRefinement.server_commit_refines` is unconditional on the candidate. |
| `server_abort_is_state_neutral` | New checked | `PqxdhSurface.server_abort_is_state_neutral` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `successful_beacon_acceptance_implies_server_binding_agreement` | New checked | `PqxdhSurface.successful_beacon_acceptance_implies_server_binding_agreement` is a direct extracted-code counterpart with only explicit raw-data premises. |
| `conditional_honest_run_correspondence` | New checked | `PqxdhSurface.conditional_honest_run_correspondence` constructs every successful extracted phase, common root/AD/ID, both binding encodings, complementary directions, authenticated typestate, and both committed states. Its byte equality and nonzero premises are exactly characterized by `honest_shared_secrets_iff` and `valid_shared_secrets_iff`; server nonzero follows from shared-byte equality. |

Validation: `lake build BeaconcryptCore.Refinement.RatchetInterpreter BeaconcryptCore.Refinement.PqxdhConcreteSession BeaconcryptCore.Refinement.PqxdhSurface BeaconcryptCore.Refinement.PqxdhSessionLifecycle`. The new proof units contain no `sorry`, admitted lemma, or additional axiom. Aggregate locked verification and mutation-suite results are recorded by the integration milestone.
