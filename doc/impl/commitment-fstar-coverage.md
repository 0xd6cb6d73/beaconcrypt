# Commitment F* surface migration audit

This inventory covers every top-level declaration in `beaconcrypt-core/proofs/fstar/Beaconcrypt_core.Commitment.Lemmas.fst`. The production transcript and integer encodings are already refined to their complete byte layouts. `Refinement/CommitmentSurface.lean` now proves direct concrete-input injectivity, complete u64 decoding, and the raw collision witness theorem. The immutable ideal PQXDH model is unchanged.

`productionInput_spec` connects the pure production-input view to the exact extracted builder result for every raw field tuple. `production_commitment_input_is_injective` derives all six raw field equalities using existing ideal preimage injectivity, discharging every length and integer-range premise from the concrete array and u64 types. The collision theorem returns those actual two extracted transcript byte arrays as an explicit witness. It assumes two accepted explanations of one ciphertext and hash output and that their key, nonce, associated data, sequence, sender, or plaintext differ. It uses only the deterministic supplied AEAD-open function; it assumes neither hash injectivity nor AEAD security. Its statement permits different tags as well, and specializes directly to the F* common-tag statement.

| F* declaration | Status | Lean correspondence |
| --- | --- | --- |
| `encode_u64_le_is_exact` | Existing checked | `PqxdhRefinement.commitment_encode_u64_le_abs` proves the complete eight-byte LE64 encoding. |
| `encode_u64_le_has_le64_values` | Existing checked | `PqxdhRefinement.commitment_encode_u64_le_abs` proves the complete eight-byte LE64 encoding. |
| `update_at_range_byte_view` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_KEY_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_NONCE_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_AD_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_TAG_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_SEQUENCE_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `v_SENDER_ID_RANGE` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `commitment_transcript_bytes` | Existing checked | `PqxdhRefinement.build_commitment_transcript_abs` proves every transcript byte in key, nonce, associated-data, tag, sequence, and sender order; `commitment_encode_u64_le_abs` supplies both numeric fields. |
| `production_commitment_transcript_uses_exact_bytes` | Existing checked | `PqxdhRefinement.build_commitment_transcript_abs` proves every transcript byte in key, nonce, associated-data, tag, sequence, and sender order; `commitment_encode_u64_le_abs` supplies both numeric fields. |
| `commitment_transcript_byte_is_exact` | Existing checked | `PqxdhRefinement.build_commitment_transcript_abs` proves every transcript byte in key, nonce, associated-data, tag, sequence, and sender order; `commitment_encode_u64_le_abs` supplies both numeric fields. |
| `commitment_transcript_is_exact` | Existing checked | `PqxdhRefinement.build_commitment_transcript_abs` proves every transcript byte in key, nonce, associated-data, tag, sequence, and sender order; `commitment_encode_u64_le_abs` supplies both numeric fields. |
| `commitment_transcript_integer_fields_are_le64` | Existing checked | `PqxdhRefinement.build_commitment_transcript_abs` proves every transcript byte in key, nonce, associated-data, tag, sequence, and sender order; `commitment_encode_u64_le_abs` supplies both numeric fields. |
| `decode_u64_le` | New checked | `CommitmentSurface.decode_u64_le`. |
| `decode_encode_u64_le` | New checked | `CommitmentSurface.decode_encode_u64_le`. |
| `encode_u64_le_is_injective` | New checked | `CommitmentSurface.encode_u64_le_is_injective`. |
| `equal_embedded_segment` | Superseded helper | The current extraction uses bounded array-building closures. `PqxdhRefinement.build_commitment_transcript_abs` proves the complete output, and immutable `Pqxdh.ctxPreimage_inj` uses exact fixed-length list segments. |
| `production_commitment_input` | New checked | `CommitmentSurface.productionInput and productionInput_spec`. |
| `production_commitment_input_is_injective` | New checked | `CommitmentSurface.production_commitment_input_is_injective`. |
| `ctx_opening_accepted` | New checked | `CommitmentSurface.OpeningAccepted`. |
| `ctx_explanations_are_distinct` | New checked | `CommitmentSurface.ExplanationsDistinct`. |
| `t_HashCollisionWitness` | New checked | `CommitmentSurface.HashCollisionWitness`. |
| `valid_hash_collision_witness` | New checked | `CommitmentSurface.ValidHashCollisionWitness`. |
| `ctx_distinct_openings_imply_hash_collision` | New checked | `CommitmentSurface.ctx_distinct_openings_imply_hash_collision`. |

Validation: `lake build BeaconcryptCore.Refinement.CommitmentSurface`. The new module has no admitted proof or extra axiom. Aggregate locked verification and mutation results are recorded with the integration milestone.
