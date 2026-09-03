# Ratchet F* behavioral coverage ledger

This ledger inventories every lemma declaration in `beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Ratchet.Lemmas.fst`. Its `.fsti` deliberately exports no declarations: the implementation is private and is friended by the PQXDH proof. The inventory therefore includes proof-internal array, arithmetic, and logical lemmas as well as protocol guarantees.

The panic-freedom boundary is complete independently of this behavioral ledger: all 269 extracted non-helper `RustM` operations have checked unconditional normal-return contracts. Normal return includes explicit protocol rejection. Those contracts alone do not establish the semantic claims listed here.

`Matched` identifies checked Lean evidence for the same behavioral clause, sometimes through a stronger theorem or a renamed first-order effect API. A match is not a mechanical translation of the F* statement: Lean's `KernelRefines` expresses canonical chains and a bidirectional correspondence with the ideal skipped store, whereas the historical F* `valid_state` and `reachable` predicates package those clauses differently. `In progress` identifies an assigned proof. `Unmatched` is an open statement-level audit item; it may be a corollary of a checked capstone or a proof-internal fact unnecessary in the new proof, and must not be counted as covered until that judgment is recorded.

The ideal files under `BeaconcryptCore/Model/` are unchanged. The historical callback-based F* functions are represented by the extracted first-order Lean request/response phases; semantic equivalence must include the driver composition and external response laws. Restored chains and keys require trusted canonical persistence provenance in both proof surfaces.

The most important unmatched behavioral groups are constructor reachability; tagged material access; successful consumption and replay; rejection retry equivalence and capacity preservation; and the exact 49-skipped-key corollary for a receive gap of 50. The newer Lean planner additionally proves admission of 50 retained skipped keys by deriving the target outside the cache. Restoration and receive-driver composition are active work.

Evidence entries abbreviate `BeaconcryptCore.Refinement.<module>` and the theorem namespace is determined by that module. This is a conservative audit draft, not a claim that F* replacement is complete.

| F* declaration | Source line | Status | Lean evidence or remaining obligation |
| --- | ---: | --- | --- |
| `ratchet_kdf_output_split_is_exact` | 18 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `symmetric_ratchet_kdf_request_is_exact` | 34 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `ratchet_step_uses_exact_chain_and_partition` | 43 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `concrete_ratchet_step_preserves_executor` | 64 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `ratchet_chain_bytes_extensionality` | 70 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `concrete_ratchet_chain_extensionality` | 77 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `u64_value_extensionality` | 87 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `u8_value_extensionality` | 96 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `positive_at_most_one_is_one` | 105 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `u64_below_max_is_not_max` | 110 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `u64_successor_value` | 115 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `u64_value_is_bounded` | 120 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `receive_key_at_matches_cache_slot` | 170 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `lookup_receive_key_from_sound` | 180 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `lookup_receive_key_from_none_excludes_range` | 202 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `lookup_receive_key_sound` | 226 | Matched | `RatchetControl.lookup_receive_key_sound`. |
| `lookup_receive_key_none_is_absent` | 237 | Matched | `RatchetRefinement.lookup_receive_key_of_not_mem and RatchetControl.lookup_receive_key_complete`. |
| `lookup_receive_key_is_complete` | 247 | Matched | `RatchetControl.lookup_receive_key_complete`. |
| `lookup_receive_key_returns_unique_slot` | 256 | Matched | `RatchetStructural.ValidControl.slot_unique combined with RatchetControl.lookup_receive_key_sound`. |
| `from_counters_is_valid` | 273 | Matched | `RatchetStructural.control.from_counters_valid`. |
| `start_restore_is_valid` | 277 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `advance_send_is_monotonic` | 284 | Matched | `RatchetControl.advance_send_ok`. |
| `advance_send_exhaustion_is_neutral` | 296 | Matched | `RatchetControl.advance_send_max`. |
| `advance_send_preserves_receive_state` | 305 | Matched | `RatchetControl.advance_send_ok`. |
| `advance_send_key_matches_sequence` | 313 | Matched | `RatchetControl.advance_send_ok`. |
| `finish_send_consumes_available` | 324 | Matched | `RatchetControl.finish_send_available`. |
| `finish_send_rejects_reuse` | 334 | Matched | `RatchetControl.finish_send_unavailable`. |
| `finish_send_is_one_use` | 343 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `plan_old_receive_is_zero_cost` | 351 | Matched | `RatchetControl.plan_receive_until_replay`. |
| `plan_future_receive_is_bounded` | 362 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `plan_receive_derivations_are_bounded` | 380 | Matched | `RatchetControl.plan_receive_until_bound`. |
| `plan_receive_shape` | 398 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `plan_receive_rejects_large_gap` | 426 | Matched | `RatchetControl.plan_receive_until_reject_of_gap_gt`. |
| `plan_receive_rejects_capacity_overflow` | 436 | Matched | `RatchetControl.plan_receive_until_reject_of_cache_full`. |
| `advance_receive_success_shape` | 450 | Matched | `RatchetControl.advance_receive_step`. |
| `advance_receive_exhaustion_is_neutral` | 469 | Matched | `RatchetControl.advance_receive_max`. |
| `advance_receive_full_cache_is_neutral` | 478 | Matched | `RatchetControl.advance_receive_full`. |
| `advance_receive_preserves_validity` | 489 | Matched | `RatchetStructural.ValidControl.advance_receive`. |
| `finish_receive_missing_is_neutral` | 495 | Matched | `RatchetControl.finish_receive_missing_state_neutral`. |
| `finish_receive_failure_retains_key` | 508 | Matched | `RatchetControl.finish_receive_auth_fail_state_neutral`. |
| `finish_receive_success_shape` | 524 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_preserves_validity` | 540 | Matched | `RatchetStructural.ValidControl.finish_receive`. |
| `finish_receive_consumes_target` | 551 | Matched | `RatchetControl.lookup_receive_key_consumed_absent`. |
| `finish_receive_preserves_other_key` | 562 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_replay_is_rejected` | 575 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_wrapper_matches_detailed` | 588 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_missing_result_is_neutral` | 601 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_retained_result_is_neutral` | 614 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_missing_is_neutral` | 627 | Matched | `RatchetControl.finish_receive_with_removal_out_of_range and finish_receive_with_removal_mismatch`. |
| `finish_receive_with_removal_failure_retains_key` | 641 | Matched | `RatchetControl.finish_receive_with_removal_auth_fail`. |
| `finish_receive_with_removal_success_shape` | 658 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_preserves_validity` | 680 | Matched | `RatchetStructural.ValidControl.finish_receive_with_removal`. |
| `finish_receive_with_removal_consumes_target` | 693 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_preserves_other_key` | 706 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_preserves_other_key_exactly_once` | 721 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `cached_receive_failure_retry_consumes_once` | 743 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `successful_receive_releases_capacity_for_next_future` | 771 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `restore_receive_key_preserves_validity` | 793 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `restore_receive_key_wrapper_matches_slot` | 803 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `restore_receive_key_with_slot_success_shape` | 817 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `restore_receive_key_with_slot_preserves_validity` | 831 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `finish_restore_is_valid` | 842 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `refined_slot_value_is_index` | 857 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `none_material_list_index` | 898 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `empty_material_slot_is_none` | 913 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `empty_material_slots_are_none` | 934 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `chain_after_successor` | 1030 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `chain_after_compose` | 1042 | Matched | `RatchetRefinement.Ratchet.chainAt_chainAt`. |
| `material_at_shift` | 1061 | Matched | `RatchetRefinement.Ratchet.msgKeyAt_chainAt`. |
| `material_at_successor` | 1080 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `empty_material_slots_are_derived` | 1092 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `packed_prefix_unchanged_refl` | 1145 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `packed_prefix_unchanged_transitive` | 1162 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `cached_materials_after_append_are_derived` | 1196 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_from_counters_is_valid` | 1342 | Matched | `RatchetStructural.refined.from_counters_valid`. |
| `refined_new_is_valid` | 1354 | Matched | `RatchetStructural.refined.new_valid`. |
| `refined_from_counters_is_reachable` | 1366 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_new_is_reachable` | 1396 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `concrete_kernel_new_is_reachable` | 1415 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_send_rejection_is_neutral` | 1433 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_send_success_uses_step` | 1443 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_send_preserves_validity` | 1471 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_send_preserves_reachability` | 1483 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_seal_next_uses_exact_step_material` | 1517 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_seal_next_preserves_validity` | 1541 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_seal_next_preserves_reachability` | 1556 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `concrete_seal_next_preserves_reachability` | 1578 | Matched | `RatchetRoleReachability.sealNext_preserves_reachability; actual first-order send driver with arbitrary optional callback`. |
| `refined_advance_receive_rejection_is_step_independent` | 1596 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_success_uses_step` | 1609 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_preserves_validity` | 1638 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_success_matches` | 1648 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_preserves_reachability` | 1667 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_slots_are_empty_for_valid` | 1716 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_with_space_succeeds` | 1748 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_execute_receive_steps_is_exact` | 1781 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_execute_receive_steps_preserves_reachability` | 1849 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_preserves_reachability` | 1881 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_accepted_computes` | 1919 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_executes_plan` | 1942 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_rejection_is_neutral` | 2062 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_is_ordered` | 2078 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_advance_receive_until_old_is_neutral` | 2098 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_entry_is_associated` | 2110 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_entry_mismatched_tag_is_rejected` | 2125 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_key_mismatched_tag_is_rejected` | 2143 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_key_is_associated` | 2160 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_receive_key_is_derived` | 2208 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_finish_receive_neutral_outcomes_preserve_full_state` | 2238 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_finish_receive_mismatched_target_is_neutral` | 2252 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_finish_receive_mismatched_last_is_neutral` | 2271 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `material_slots_after_swap_remove_is_exact` | 2325 | Matched | `RatchetCachedPublication.publish_cached_receive_exact for arbitrary chain and material types`. |
| `cached_materials_after_swap_remove_are_derived` | 2384 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `generated_material_swap_remove_matches_view` | 2445 | Matched | `RatchetCachedPublication.publish_cached_receive_exact for arbitrary chain and material types`. |
| `refined_finish_receive_success_computes_swap` | 2477 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `finish_receive_with_removal_preserves_other_physical_slot` | 2522 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `material_slots_after_swap_remove_matches` | 2550 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_finish_receive_success_is_exact_swap_removal` | 2606 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_finish_receive_preserves_validity` | 2710 | Matched | `RatchetStructural.ValidRefined.cached_publication plus exact entry preservation on rejection; the historical monolithic helper is replaced by prepare/finish phases`. |
| `refined_finish_receive_preserves_reachability` | 2736 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `receive_control_extension_refl` | 2814 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `receive_control_extension_advance` | 2833 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `staged_receive_extension_outside` | 2906 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `staged_receive_extension_boundary_is_empty` | 2924 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `staged_receive_extension_boundary_at_index` | 2941 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `empty_staged_receive_extension` | 2959 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `staged_receive_extension_append` | 2990 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `ratchet_step_extensionality` | 3047 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `lookup_receive_key_absent_is_none` | 3085 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `receive_control_prefix_matches_for_equal_prefix` | 3099 | Matched | `RatchetReceiveLoopExact.receive_control_prefix_matches_true`. |
| `future_commit_preserves_entry_cache_prefix` | 3132 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `pending_receive_slots_last_computes` | 3241 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `pending_receive_slots_next_computes` | 3266 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `pending_receive_slots_are_valid_for_trace` | 3299 | Matched | `RatchetReceiveLoopExact.pending_receive_slots_are_valid_true`. |
| `pending_receive_is_valid_computes` | 3391 | Matched | `RatchetReceiveLoopExact.pending_receive_is_valid_true`. |
| `prepared_future_trace_passes_validator` | 3433 | Matched | `RatchetFutureFinalization.FuturePendingRefines.valid`. |
| `prepare_future_receive_steps_last_computes` | 3519 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_future_receive_steps_next_computes` | 3574 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `exists3_intro` | 3618 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_future_receive_steps_is_total_and_exact` | 3638 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_receive_future_computes` | 3821 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_receive_future_result_shape` | 3852 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `exact_future_helper_result_is_published_by_prepare` | 3882 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `admitted_future_plan_prepares_exact_trace` | 3941 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `publish_future_receive_slots_is_exact` | 4033 | Matched | `RatchetReceiveLoopExact.publish_future_receive_slots_exact`. |
| `material_slots_match_after_future_move` | 4120 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `publish_future_receive_computes` | 4197 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `cache_has_preserved_by_exact_prefix` | 4216 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepared_future_publication_is_exact` | 4310 | Matched | `RatchetFuturePublication.FuturePendingRefines.publication`. |
| `prepare_cached_receive_establishes_valid_cached` | 4476 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `valid_cached_publication_matches_refined_finish` | 4587 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `valid_cached_target_is_preparable` | 4603 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `valid_cached_target_prepares_valid_cached` | 4652 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `future_target_is_absent_from_entry` | 4712 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `staged_receive_extension_excludes_target` | 4722 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_receive_cached_result_shape` | 4784 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_receive_cached_computes` | 4804 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `admitted_cached_target_prepares_valid_cached` | 4826 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `rejected_admission_is_entry_neutral` | 4911 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `prepare_receive_future_establishes_valid_pending` | 4932 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `admitted_future_plan_prepares_valid_pending` | 5003 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `pending_target_material_is_canonical` | 5058 | Matched | `RatchetFuturePublication.FutureOpenRefines.material_exact`. |
| `refined_open_and_finish_rejection_is_neutral` | 5075 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_cached_success_publishes_removal` | 5115 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_future_success_publishes_pending` | 5151 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `cached_publication_establishes_successful_receive` | 5181 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `future_publication_establishes_successful_receive` | 5214 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_and_finish_preserves_validity` | 5241 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_and_finish_success_result` | 5288 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `option_payload_property_is_pointwise` | 5391 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_and_finish_is_state_neutral_or_successful` | 5438 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `successful_receive_consumes_target` | 5474 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `missing_old_target_is_neutral` | 5496 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `successful_open_replay_is_neutral` | 5518 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_success_replay_is_neutral` | 5550 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `rejected_open_attempts_preserve_entry` | 5603 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `retry_after_rejected_open_attempts_equals_direct` | 5631 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `refined_open_rejection_preserves_cache_capacity` | 5666 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `fresh_maximum_gap_success_publishes_exactly_49` | 5686 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `valid_cached_publication_preserves_reachability` | 5764 | Matched | `RatchetCachedPublication.CachedOpenRefines.finish_success_refines`. |
| `valid_pending_publication_preserves_reachability` | 5789 | Matched | `RatchetFuturePublication.FutureOpenRefines.finish_success_refines`. |
| `refined_open_and_finish_preserves_reachability` | 5856 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |
| `concrete_open_and_finish_preserves_reachability` | 5914 | Matched | `RatchetReceiveReachability.receiveNext_preserves_reachability; constructive unbounded first-order driver for every canonical entry and optional callback`. |
| `start_refined_restore_is_valid` | 5935 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `start_refined_restore_is_reachable` | 5948 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `refined_restore_receive_key_is_atomic` | 5978 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `refined_restore_receive_key_preserves_reachability` | 6011 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `finish_refined_restore_is_valid` | 6053 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `finish_refined_restore_preserves_reachability` | 6067 | In progress | Conditional material restoration in `RatchetMaterialRestore`; existing control restoration bounds do not alone establish canonical material provenance. |
| `replace_ratchet_for_other_peer_is_neutral` | 6086 | Matched | `RatchetControlRestore.replace_ratchet_for_peer_other`. |
| `replace_ratchet_for_selected_peer` | 6093 | Matched | `RatchetControlRestore.replace_ratchet_for_peer_match`. |
| `advance_send_for_other_peer_is_neutral` | 6104 | Matched | `RatchetControlRestore.advance_send_for_peer_other`. |
| `advance_send_for_selected_peer_matches` | 6114 | Unmatched | Compare the full statement with checked effect, control, and trace capstones; record a checked corollary or explain replacement of this internal fact. |

The inventory contains 192 declarations: 47 matched, 12 in progress, and 133 unmatched in this draft.
