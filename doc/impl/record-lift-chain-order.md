# Ordered hidden-chain callbacks and executed depth

`PqxdhRecordLiftChainOrder` defines a finite replacement order for private hidden-chain coordinates and proves 27 operational results. A coordinate names a slot, direction and source position; none of those fields is recovered from a key's bytes. The module changes no public HKDF evaluation and makes no cryptographic security claim. It prepares the actual callback endpoints and finite range required by the subsequent global simulations.

## Exact finite order

For `n` hidden slots and depth cap `P`, the finite cell type is `Fin P × (Fin n × Bool)`. The `ordering` equivalence places depth first, then slot and direction, with exactly `P * (n * 2)` indices. A direction's coordinate is its production start plus that depth: Server-to-Beacon starts at position 1, after registration sequence 1, while Beacon-to-Server starts at position 0. These are already-derived source positions: the first ordinary Server-to-Beacon callback derives sequence 2.

`coordinate_cellOf`, `coordinate_bounded` and `cellOf_coordinate` show that this representation enumerates exactly the coordinates at or above their directional starts with depth below `P`. `at_index`, `at_bounded`, `index_at` and `index_injective` prove the exact inverse mapping and uniqueness of the logical index. They assert no cryptographic injectivity, distinct keys or independent sessions. Zero slots or zero depth are allowed and give an empty finite family.

The Boolean `selected P cut` marks exactly the in-range coordinates whose index is below `cut`. `selected_zero` makes the first interpreter wholly real. `selected_last` makes every in-range coordinate ideal at the final cut; coordinates outside the justified range stay real. `selected_bounded` exposes the exact index comparison. `selected_unchanged` and `selected_step` prove that one adjacent increment changes precisely the chosen coordinate from real to ideal.

`index_value`, `index_advance` and `index_advance_lt` give the arithmetic order: advancing one source derivation moves by exactly `n * 2` indices and therefore occurs later. `selected_predecessor` proves that a noninitial chosen coordinate's predecessor is already selected. Its strict lower-bound premise excludes the total interpretation's below-start fallback and truncated natural subtraction; this premise is operational, not a byte-distinctness assumption.

## Complete callback endpoints

`lookup_agrees` compares literal `ChainOracle.lookup` computations when their modes agree at the requested coordinate. It retains the complete output, private table, native/effect counters, uniform counter and shared hash cache. `lookup_adjacent` applies this equation to the actual finite order away from the chosen coordinate. It is an equality of the full stateful callback, not just an output marginal. Applying any identical continuation to it therefore retains the same evaluated computation.

`lookup_initial` identifies the first ordered interpreter with the already reviewed all-real callback. That callback is connected to the actual instrumented World KDF by `ChainOracle.lookup_source`. `lookup_terminal` identifies the final ordered callback with the persistent all-ideal callback at an available request covered by the executed post-call cap. It does not assume that every possible natural-number coordinate was sampled or is reachable.

`lookup_repeated` proves that a populated coordinate returns its earlier complete 76-byte answer in either mode under the existing mixed-table validity invariant. A real repeat still evaluates the deterministic source function and increments its native KDF ledger; an ideal hit increments that source ledger without drawing fresh bytes. The equality needed to reuse a selected challenge answer is thus explicit, while repeated source costs remain charged. This result alone does not construct a cryptographic reduction or its full query bill.

## Executed depth bound

`DepthBound table calls` says that each populated coordinate has a valid direction-relative start and depth strictly below the actual executed native KDF count. `depth_empty` establishes it at the empty table and zero calls. `bounded_mono` and `depth_mono` allow the count to grow due to work elsewhere without changing the table.

`available_bounded` derives the next request's depth from the existing interpretation domain. An initial coordinate has depth zero. A later coordinate has its actual predecessor stored in the same table, so the predecessor's strict bound places the request below `calls + 1`. `depth_record` then preserves the bound when the request's complete response is recorded. No finite-support assumption, independent seed family, success premise or ghost query counter is required.

`lookup_depth` discharges this update for the concrete mixed real/ideal callback and its actual poststate native counter. The real case, ideal hit and ideal miss are all included. Every call increments `native.kdf` exactly once, including repeats. The ideal miss additionally draws its complete 76 bytes, as accounted by `ChainOracle.lookup_primitive`; this module does not hide those draws in the logical source count. Previously failed receives can retain their table entries and their already incurred native costs.

## Remaining global obligations

The dynamic World compiler must establish this depth invariant across actual routing and source operations, transport the total `S + 51 * R` ordinary-record callback cap, and show that each queried coordinate lies in the final finite range. Its initial seeds are still the actual lazy partial seed cache; a mathematical totalization is not an independently sampled global family. The local callback bound here supplies the concrete update for that derivation, rather than making global reachability a security premise.

The ordered family contains `P * (n * 2)` candidate coordinates. That is a finite index count, not a claim that the execution makes that many callbacks and not a proved loss bound. The actual global games, selected secret-input and key-free observers, alias/refusal bounds, Extract/HMAC reductions, CTX reductions and whole-program query accounting remain separate joins. Only after their adjacent simulations are proved can the global finite-hybrid inequality be applied. No persistence, saved-state restoration or primitive implementation proof is part of this module.
