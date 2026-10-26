# Source position for every reached opening

This HB-91 follow-on identifies the material used by every reached opening before the optional reply exists. It strengthens the earlier successful-result provenance boundary: a failed commitment or AEAD opening is routed through the same original directional position and retains its full primitive poststate. `RawCtxPositionedOpening.lean` contains sixteen checked statements. No production Rust, cryptographic algorithm or maintained symbolic process changes here.

## Actual source prefix

The source kernel/material relation already records the current chain, counter, cache contents and original directional chain. For an arbitrary decoded `u64` target, `receive_prefix` follows the actual source admission branches. Zero, replay and capacity rejection terminate at the original rejection. Cached admission reads the actual stored slot. Future admission executes the complete fixed-response KDF prefix, including skipped positions, before the selected opening. The terminal opening material is exactly the original `msgKeyAt(origin, target - 1)`. Its original sequence and immutable context follow from the source begin/resume scope theorem. No opening reply, decryption correctness, key uniqueness, uniform root or independent material premise is used.

The generic KDF interpreter is a fixed function returning each actual typed source response. The concrete source instantiation uses the existing complete 76-byte functional HKDF-SHA-512 response and its original chain/material correlations. This is not an arbitrary fresh-output ROM interpreter or a proof that new hybrid replies are independent of primitive state. The private log records exactly the actual KDF requests/responses; erasure removes only that log.

## Checked statements

| Statement | Established boundary |
| --- | --- |
| `prefix_scope` | Each actual fixed-response prefix preserves the original target and context. |
| `receive_prefix` | Every real source branch rejects or reaches the exact original material position before opening. |
| `receive_positioned_congr` | Equal handlers on those actual opening arguments preserve the full logged computation, including failure. |
| `bare_receive_positioned_congr` | Erasing only the request log preserves that complete equality. |
| `arguments_positioned` | Actual source getters pass the exact material, sequence and immutable context. |
| `adapter_positioned_congr` | The owner adapter retains missing-material rejection and actual optional-result construction. |
| `primitive_bare` | A fixed functional KDF implementation has the exact bare receive representation. |
| `owner_receive_positioned_congr` | Scoped replacement preserves source receive and finish before either optional reply is observed. |
| `raw_positioned_congr` | Replacement retains original raw/frame/AD and every parser, sender or shape rejection. |
| `rawGame_positioned_congr` | The entire returned owner and primitive state are equal. |
| `source_kdf` | The concrete source derives its fixed-response equation from the existing handler. |
| `source_raw_positioned_congr` | An actual source callback can be replaced at its proved position under a stated local computation equality. |
| `atPosition_eq` | Reconstructing the selected material changes none of the actual opening input. |
| `source_raw_positioned` | The concrete position-routed callback is equal to the original source raw computation, with no assumed opening equality or success premise. |
| `atPosition_bytes` | The selected source material is the same byte-model ratchet material at that index. |
| `source_positioned_query_bounds` | Every selective underlying uniform-query cap is exactly preserved. |

The earlier congruence hypotheses are explicit local computation equations, intended to be discharged by actual component interfaces. They are not new cryptographic contracts. The final `source_raw_positioned` theorem discharges that equality internally for `positionedNative`: this wrapper replaces only the private material field with its reconstruction from the same fixed original chain and actual sequence, then calls the unchanged native opening handler. Original raw bytes, frame, associated data, selected sequence, optional plaintext and complete shared auxiliary/CTX state remain. Both `None` and `Some` branches are included. No new key table or public material endpoint is introduced.

## Work, privacy and remaining composition

The wrapper can recompute a position from its origin and therefore add pure chain/KDF/list work proportional to the index. Unchanged underlying oracle requests do not make this work free, prove a tight runtime bound or establish equality of native parser traversal, timing, allocation or constant-time behavior. The existing source callback budgets remain their original budgets; any efficient computational simulator must separately account for or implement its position lookup. The exact finite native index does not permit sending past counter exhaustion.

The original chain and any private KDF/history instrumentation are excluded from public replies, compromise reveals, snapshots and persistence. Actual optional API plaintext is preserved, and its disclosure to a network adversary remains a separate policy. Different owners, origins or positions may use equal key/nonce bytes; no injectivity is inferred.

The theorem requires the current owner's ordinary source kernel/material relation. Existing initialization and source preservation theorems can supply that relation along uninterrupted execution. A restored or copied owner, arbitrary fresh-output hybrid, global registration handoff, compromise schedule or evolving-key game must establish the corresponding relation itself. This checkpoint does not yet prove persistent ProVerif trace inclusion, remove the source kernel from all non-consumed branches, establish a computational collision bound or finish the global symbolic bridge. Native primitive/codec/compiler/library/storage and resource contracts retain their existing explicit scope.

## Focused validation

The final candidate passed the locked full Lean build (3,222 jobs), all sixteen persistent guarded dependency reports, the root import check, and the inventory check (172 Lean files and 321 unique entries). All sixteen source-fidelity tests passed in 12.96 seconds; formatting, forbidden-proof scans and whitespace checks passed. An initial full-build invocation from the Cargo workspace root could not select the Lean toolchain; rerunning from the existing Lean project directory resolved it without changing the toolchain or any proof.

Rust, ProVerif inputs and the existing runtime validation units are unchanged. The published `df11bc5c222684ceedb687f30afa22a83dfe3781` Rust 1.96 workspace Clippy result (19.80 seconds with the documented existing warnings) remains applicable to those exact inputs. No new mutation run was required for this proof-only addition under the user’s testing instruction. A fresh private fetch and direct remote query both returned `8330cdef4f4659931b6764a026cd90c4caf833a4` for `vcvio`, which remains an ancestor. The completed finite symbolic results and unclassified persistent-model diagnostics retain their separate recorded scopes; this checkpoint supplies no new ProVerif classification or global security result.

## Combined computational topic validation

The integration topic semantically ports these sixteen statements from `947685a68a2b87a90c40ba18414a225e2244410a`, the nine consumed-guard statements from `bbf6185dde503c39940a0d18a687ada523398751`, and the 33 correlated Extract-family statements from `01e53a4ef993066a5281ee27d5b21ade84bcd331`. All four proof modules are unchanged from their reviewed incoming blobs. Current shared documentation, imports, named dependency gates and inventory are reconciled without replacing the newer ProVerif integration or separately replaying ancestors already present.

All 58 persistent dependency guards pass direct checking without diagnostics, and the full combined Lean library passes 3,294 jobs. Policy, root-import, reviewed-inventory and whitespace gates pass with 244 handwritten Lean modules and 408 reviewed artifacts; all prior 404 artifact paths and their order are retained. HB-91 now records 407 guarded operational statements; HB-94 retains its independently sampled key-family scope and 59 statements. The new Extract term remains the explicitly displayed secret-suffix family game and is not inferred from ordinary secret-key HMAC PRF security. It makes no protocol authentication conclusion a primitive assumption.

These four proof additions do not change Rust, ProVerif or transcript fixtures. Formatting and all sixteen fidelity tests remain inherited from the fresh run recorded at `7531be71db54a82d758c03622d9045126c5114aa` (11.88 seconds); no rerun is claimed here. No Rust mutation run is required under the current proof-only testing instruction. These are focused combined-topic results. Persistent symbolic trace inclusion, correlated root Expand and source evolving-key/reveal/global composition retain their separately documented obligations, and the final complete matrix on an eventual validated source/global integration remains required.
