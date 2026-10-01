# Server authentication in the complete R1 source experiment

`PqxdhServerAuthentication` closes the ordinary CTX entry probabilities in the original R1 server-authentication experiment. `authentication_bound` gives the explicit final inequality for that experiment. `source_order_authentication` gives the same inequality for `PqxdhServerAuthNative.sourceOrdered`, using the checked constructor interchange over the complete evaluated continuation. Both statements use the approved restricted Extract and shared CTX/BLAKE2b random-oracle experiment; production generator order does not remove these idealizations. The proof does not assume an honest selected registration, an accepted target, a fresh opening, a source origin, or a secure intermediate protocol game.

This is the approved R1 scope: one fresh target Beacon pinned to one fresh Server identity, arbitrary attacker-supplied registration candidates and raw initial responses, separate Server accept/build calls, public HMAC and shared commitment-hash queries, arbitrary adaptive scheduling and stopping, and reveals of installed Server kernels. The revealed kernels include the advanced sending chain after registration. Revealing the original sending chain is a different experiment whose explicit negative control wins. The original experiment does not reveal the Server identity seed or any Beacon secret, and does not claim KCI resistance or post-registration record secrecy.

## Exact event

The original `Win` is the union of three failures at the Beacon's first actual acceptance. W1 means no earlier Server session derived the same actual 192-byte root input. W2 means a partner exists but no earlier seal of any partner has the accepted assigned ID, application suffix and associated data. W3 means two distinct earlier Server attempts share the accepting Beacon’s root input. The acceptance observation is private transient proof instrumentation. A partner is defined by the same concrete root input, not equality of public key encodings, symbolic constructors or administrative session labels.

The source runs actual preparation, consumed-registration admission, optional root and pending-token handling, the complete inner and outer writer paths, initial raw receive, sequence-one and eight-byte binding checks, and publication or terminal abort. All original private/public fields, logs, caches and optional replies remain present in the reduction. A successful inner seal followed by a failed outer writer remains in the source seal history. The theorem therefore uses seal origin, not an unstated guarantee that every originating response was successfully returned to a caller.

## Bound and constructed reductions

Let `A` be the original adaptive adversary. Its four source bounds are `Q` accept attempts, `qH` public zero-salt 192-byte HMAC requests, `qHash` public BLAKE2b requests and `qCoin` uniform queries, each on every reply path and public input. Rejected accepts are included in `Q`. Let `G`, `E` and `D` be the existing complete KEM keygen, encapsulation and decapsulation uniform costs, including their underlying base-query costs. Define

```text
U = 256 + qCoin + 160 Q + 64(qHash + qH) + G + Q E + D
H = U + 76.

Pr[Win(A)] ≤ AdvGapDH(extractor(scanClient(A)))
             + choose(Q, 2) · 64 / 2^256
             + Σ j∈Fin(Q+1) [ScheduleLoss(A,j) + CtxLoss(A,j,H)].
```

`ScheduleLoss` is the existing `entryScheduleLoss` of the same original adversary and coordinate: the root Expand HMAC PRF reduction, Extract on the resulting uniform 32-byte root, the initial Expand HMAC PRF reduction, Extract on the uniform first 32-byte chain, and the two-block step Expand HMAC PRF reduction. Their exact games and constructed reductions are defined in `PqxdhServerAuthKeySchedule` and instantiated by `PqxdhServerAuthEntryFactor`. The first/second/final projections and the opposite initial chain are retained jointly. Repeated views of one expansion are not resampled independently.

For each entry, `CtxLoss` is the finite real value of the transparent `PqxdhServerAuthCtxObserverEvent.ctxLossENN`:

```text
AdvIND$(validation(A,j,H)) + H / 2^128
+ 2 · AdvINT-CTXT(integrity(A,j,0)) + 1 / 2^512.
```

`validation` is the existing ordinary modified nonce-AEAD validation reduction applied to the complete source client's ordinary observer. `integrity` is the indexed ordinary modified nonce-AEAD integrity reduction at index zero applied to that same observer. Its fallback is an arbitrary ordinary forgery value, and is an explicit theorem parameter. The selected-key client itself has no selected-key argument and submits the actual raw target bytes; its receive continuation obtains the challenger's actual optional plaintext.

The factor `Q+1` is the size of the explicit family, consisting of `Q` attempted Server coordinates and the Beacon coordinate. It is not concealed in a primitive assumption or omitted as free target selection. Each term is a separately constructed reduction. The complete source reservation proves at most one selected seal and one selected raw attempt in each term. The index sum inside the ordinary integrity endpoint therefore has one term; its coefficient two is the existing CTX reduction's coefficient, with no additional raw-attempt multiplier. The Gap-DH reduction has coefficient one. The scalar-spread theorem bounds the original distinct-Server collision event, including W3.

## Why the entry probability is discharged

The original event partition, Gap-DH extraction, scalar-collision bound and five adjacent key-schedule comparisons are already proved in the same experiment. The final theorem substitutes the actual ordinary-entry authentication bound for each remaining uniform-entry probability. `PqxdhServerAuthCtxResources.client_hash` derives `H` from the original source budgets, so no arbitrary component-client resource premise remains in the inequality.

The entry compiler forwards the real context sampling and joint residual76, retains every source callback, and shares the actual commitment cache with all known-key and public operations. Literal source token consumption proves the reached one-use seal reservation and discharges the local compiler condition. Normal stopped outputs are supported by the original complete source run. Actual acceptance histories and source designation then identify the selected omitted input with the Beacon input, ruling out the ordinary-root table case. Thus a true original entry decision implies an ordinary observer win in the same fully sampled experiment, with coefficient one. Neither simulator honesty nor selected-input existence is assumed.

## Complete reduction resources

`reduction_bills` derives the transparent `ReductionBills` record from the same four original adversary caps and the same KEM/base bounds. `source_order_authentication_with_resources` states the production-order inequality and that record together. No component-client budget, hidden ambient program or plaintext-length promise is left as an additional hypothesis.

The Gap-DH extractor makes zero signing queries, at most `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1) + qH` decision queries and at most `bodyCoinBudget + 64*(qH+Q+1)` local uniform queries. Its full challenger, including both 32-byte challenge draws, has uniform bound `U`. Every deterministic primitive, source and adversary operation remains in the executable reduction; a query bound does not assert zero runtime for those operations.

For each of the `Q+1` coordinates, the three HMAC reductions have challenge-query caps `1`, `1`, `2` and local uniform caps `U`, `U`, `32+U`. The five component endpoints' complete real/random uniform bounds are, in the schedule-loss order above:

| Component | Real game | Random game |
| --- | --- | --- |
| Root Expand PRF | `64+U` | `64+U` |
| Extract of uniform root | `32+U` | `96+U` |
| Initial Expand PRF | `64+U` | `64+U` |
| Extract of uniform first chain | `64+U` | `128+U` |
| Step Expand PRF | `96+U` | `160+U` |

The real and uniform entry experiments have uniform bounds `U+64` and `U+108`. The actual ordinary CTX source client has total interface bound `H=U+76`, and the full source game adds its 32-byte selected-key draw for `U+108`. The observed ordinary receive program has uniform and shared-hash caps `H`, selected seals at most one and raw attempts at most one, including every failed or refused attempt.

Put `B = H + 64*(H+2)`. This pays for source randomness and all simulated commitment-digest generation, including the public hash requests, selected seal and selected raw attempt. The exact validation reduction has at most `B` uniform queries and two primitive encryption requests: one source seal and one candidate-key validation probe. The exact integrity reduction has at most `B` uniform queries and one primitive seal, followed by the ordinary endpoint's one final forgery verification. Neither has a primitive opening oracle. Their complete real challengers each have uniform bound `32+B`.

The random validation challenger additionally pays for ciphertext body bytes. `PqxdhServerAuthCtxByteBounds.client_plaintext` derives a weighted body-byte bound of `Aeneas.Std.Usize.max` from the production builder's checked `8 + payload.length` overflow gate and the proved one-selected-seal bound. It covers all syntactic replies and optional failures; it is not conditioned on success or supplied by the adversary. The random challenger therefore has uniform bound `B + Aeneas.Std.Usize.max + 32`, where the final32 pays for two 16-byte tags and the validation probe has empty body. This is a conservative machine-width bound, not a tight application workload estimate. Public or known-key local encryption stays real and does not submit body bytes to the selected primitive challenger.

## Permanent contracts and limitations

The bound uses the approved twist-inclusive, joint-use Gap-DH endpoint `PqxdhJointGapDh.game`, the X25519 class and scalar-spread laws, and the fixed-source HKDF functional contract `SourceFullCorrect`. The experiment explicitly models zero-salt Extract on 192-byte PQXDH inputs as a programmable classical random oracle. Other HMAC and public HKDF evaluations remain real. The CTX component uses the existing shared programmable BLAKE2b-512 random oracle. Neither random-oracle idealization follows from collision resistance or ordinary uniform-key HMAC PRF security. Primitive advantages are left as advantages of the constructed ordinary games; no primitive implementation or internal algorithm is proved.

The existing abstract-codec `ReadWritable` premise is used only in the accepted matching-frame receipt argument. It does not claim canonical wire encodings or prove a serialization library. Extracted-core refinement, reviewed adapter transcriptions, primitive correctness, compiler/runtime and ownership contracts remain the documented source boundary. Snapshot, persistence and restoration behavior remain excluded.

This result establishes the stated R1 authentication event. It does not by itself establish the full replicated computational/symbolic experiment, adaptive identity/session creation and compromise, post-registration multi-session secrecy, or a trace compiler for every ProVerif correspondence. It does not claim later assigned-ID equality or exact raw X25519-encoding origin. Those larger composition obligations remain separate from this closed authentication inequality.

## Validation

All four public statements have exact guarded standard-only axiom reports. Direct module checks and independent semantic review cover the original event, constructed reductions, complete query and byte accounting, source order and explicit contracts. Aggregate Make and source checks are run on the enclosing integration; this module checkpoint alone does not claim that final matrix has passed.
