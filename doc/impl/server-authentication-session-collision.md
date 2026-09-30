# Server-authentication session collision (B7)

`PqxdhServerAuthCollision.collB_probability` bounds the original `PqxdhServerAuthExperiment.CollB` event by `choose(Q, 2) * 64 / 2^256`. The event is that two distinct Server attempt indices have root requests with the same 192-byte input as the target Beacon. The adversary may interleave all existing accept, build, finish, public HMAC, public BLAKE2b, state-reveal and coin requests and may stop adaptively. `Q` bounds every accept request, including malformed input, freshness rejection, failed encapsulation, failed root construction, unbuilt pending tokens and requests made after the Beacon's finish.

The only additional primitive premise used here is the already approved `X25519ScalarSpread setup.source.crypto`: for a fixed peer encoding and fixed nonzero output, at most 64 raw 32-byte scalars produce that output. This proof consumes that contract; it does not prove X25519 internals. It does not require the X25519 class law, nonzero-honest-DH, signature security, KEM correctness or security, a codec read-back law, honest adversarial input or an input-independence premise. The functional contracts in the existing `Setup`, `Codec` and `Checks` remain those of the experiment.

## The actual sampler

`spread_probability` converts the finite counting contract to the probability of the actual uniform 32-byte ephemeral draw. `verified_third_probability` then consumes the literal `collectVerified` program under the experiment's concrete Server callbacks. The prekey supplying DH3 is fixed in the verified Phase 1 input before the scalar draw. Freshness and reservation checks and the two point checks retain their original positions before generation. KEM validation and encapsulation, conversion, and the four DH operations retain their original positions afterward. A failed later operation remains a failed continuation; the proof never samples a scalar conditioned on eventual success.

`prefix_third_probability` includes arbitrary raw decoding and signature verification before this same program. `prefix_thirds_probability` gives the union bound against an arbitrary previously fixed list of nonzero outputs. That list may depend on the entire prior adaptive history. No generator interchange or marginal keypair equality is used.

## The source event and history

`thirds` projects the original chronological touch history to pairs of allocated attempt index and nonzero known DH3. Beacon and public-query touches add no entry. `thirds_nonzero`, `input_third_nonzero`, `thirds_input` and `thirds_mem_input` show exactly which source requests contribute. A reached locally valid root request contributes even if the root endpoint subsequently returns `none`.

`root_input_third` reads the actual DH3 bytes at offset 96 of the exact 192-byte root input. Equal root inputs therefore have equal DH3 values. This is a byte projection, not public-key or KDF-output injectivity. `collB_thirds` obtains both contributing requests from the experiment's existing proved `GameInv.sessionOrigin` invariant, keeping their distinct attempt indices. The final theorem discharges that invariant with `gameState_reachable`; there is no authentication or selected-session premise.

`accept_split` and `evaluate_accept` preserve the complete original accept computation, both source and Extract-family state, and the complete continuation after the prefix returns. `acceptTail_thirds` retains optional root replies and pending-token publication. The small state and evaluation helper equations are monadic equalities, and `evaluate_support` transports supported executions back to the unchanged source program. The shared cache and ordered family history are retained. Public HMAC evaluations outside the approved zero-salt 192-byte Extract slice stay real.

## Adaptive accounting

`collision_append` identifies the only way one new attempt can create a distinct-index collision: its actual nonzero DH3 matches an earlier retained coordinate. `accept_collision_probability` applies the actual prefix union bound to that complete accept continuation. The old history can be arbitrary and correlated; it is fixed at the start of this call. The existing collision-free condition is used only for this per-step induction, and the final theorem starts from the source's empty history.

`finish_thirds` and `handler_quiet` prove that every other actual oracle class preserves the Server-coordinate projection. `accept_thirds_length`, `fused_quiet` and `fused_thirds_length` retain this fact under the same interpreted adaptive handler and show that an accept adds at most one entry. `fused_collision_probability` combines the exact per-class facts.

With `n` prior entries and `q` remaining accepts, `allowance n q` counts the remaining earlier/later pairs. `allowance_eq` identifies it as `q*n + choose(q,2)`. `run_collision_probability` uses the actual adaptive syntax and its accept bound to add each per-call hazard once; early stopping and rejection only reduce the count. `body_collision_probability` retains the original Phase 1 sampling order and begins at the actual empty ghost, and `gameState_collision_probability` also retains the original joint challenge draw. `scalar_card` identifies the raw scalar space as exactly `2^256`.

No reduction, oracle call or target guess is added by this statistical event inclusion. There is no extra raw-record or session-selection factor: the pair count already covers all distinct Server attempt pairs. The only budget premise is the adversary's accept cap `Q`. This does not declare the other oracle work free; it leaves that work unchanged and does not replace the separate complete resource ledger for the Gap-DH, KDF and CTX reductions.

## Scope and validation

The theorem also holds when the experiment's negative-control flag reveals the Server identity seed. This is a statement only about collision of freshly generated ephemeral contributions, not about authentication after such a reveal. It makes no secrecy or nonexposure claim about arbitrary supplied state or callbacks.

This closes B7 within the approved restricted-Extract experiment. It does not close B8b's adaptive selected-entry factorization, B9b's CTX consumer, the final Server-authentication bound, or equality with an extracted native adapter. It changes no Rust, wire format, persistence, serialization or primitive-implementation scope.

The module has 36 guarded dependency checks. Its probability statements use the repository's existing discrete VCVio probability adapter, with deprecation notices scoped to those statements; no proof or inventory gate is disabled. Direct Lean 4.34 checks and forbidden-premise scans are performed for this checkpoint. Parent integration owns root imports, global inventory wiring and the consolidated verification run. Mutation testing is unnecessary because Rust did not change.
