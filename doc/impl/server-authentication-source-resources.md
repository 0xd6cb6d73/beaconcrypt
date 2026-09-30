# Complete source resources for the Server-authentication reduction

The four modules `PqxdhServerAuthSourceCosts`, `PqxdhServerAuthPendingBudget`, `PqxdhServerAuthTailCosts` and `PqxdhServerAuthBodyCosts` discharge the direct source-uniform premise left explicit by B6. Their 61 guarded statements concern the existing `PqxdhServerAuthExperiment.body` and the same `scanClient` and ordinary Gap-DH extractor used by `badB_le_gapDh`. They add no cryptographic-security premise, change no adversary capability and do not establish the remaining selected-entry authentication reductions.

The production operations remain `Server::get_shared_secret`, `Server::build_registration_response`, `Beacon::get_registration_bundle` and `Beacon::finish_registration` in `beaconcrypt/src/server.rs` and `beaconcrypt/src/beacon.rs`. The existing experiment executes their reviewed preparation, extracted acceptance, registration builder and first-receive adapters. These resource proofs consume those exact programs, including optional results, complete native state, pending tokens, shared commitment cache, public replies and private analysis logs. They neither resample rejected operations nor condition costs on success.

Let `Q` bound every adversary accept attempt, `qHash` every public BLAKE2b request and `qCoin` every direct adversary uniform-oracle request. These are syntactic adaptive-program bounds for every reply, not counts of successful operations. The existing authentication budget does not bound adversary coins, so `IsAuthCoin` and the separate `qCoin` premise are explicit. Let `qH` be the existing public HMAC table-domain request cap used by B6. Public HMAC outside that domain and public HKDF evaluations remain the actual functions.

For a KEM operation, its declared direct-uniform cap is `uGen`, `uEnc` or `uDec`, and its original base-interface cap is `bGen`, `bEnc` or `bDec`. Let `r` bound the uniform queries of each actual fixed base interpreter callback. `KemBound` states these resource contracts on the unchanged keygen, encapsulation and optional decapsulation programs. Encapsulation bounds quantify over every supplied public key; decapsulation bounds quantify over every secret/ciphertext pair. They do not assume valid, honest or independent selected keys. Define `G = uGen + r*bGen`, `E = uEnc + r*bEnc` and `D = uDec + r*bDec`. No primitive implementation or internal primitive security is proved.

The closed direct-uniform source bound is:

```text
u = 64 + G + qCoin + (32 + E + 64)*Q + 64*qHash + D + 64
  = 128 + qCoin + 96*Q + 64*qHash
    + uGen + Q*uEnc + uDec
    + r*(bGen + Q*bEnc + bDec).
```

`body_coins` proves this bound for the literal original body, including its optional negative-control input. The bound counts uniform-oracle calls; the explicit 32/64 source samplers are byte-valued calls. It is not a compiled-runtime, input-length or allocation bound. Real deterministic cryptographic and codec work stays in the execution and is not claimed to have zero runtime.

## Exact prefixes and primitive interpretation

`ambient_uniform` proves that interpreting an original primitive program with direct cap `u` and base cap `b` costs at most `u + r*b`, through every actual answer and complete continuation. `keygen_uniform`, `encaps_uniform` and `decaps_uniform` instantiate that fact at the exact source primitive interfaces.

`verify_callbacks`, `collect_callbacks` and `server_callbacks` retain source order and all rejection paths. One Server prefix has at most one ephemeral generation, one encapsulation, three signature verifications and 17 other callbacks. The prefix's actual uniform cost is `32 + E`, proved by `generate_uniform`, `server_step_uniform`, `server_bill` and `server_prefix_uniform`. The callback bounds count attempted verifications even when the first or a later verification rejects. Each of the `Q` accept attempts executes at most one such prefix, so no accepted-only interpretation is used.

`beacon_collect_decaps`, `beacon_prepare_decaps` and `beacon_callbacks` retain the complete metadata/preparation path and give at most one decapsulation, with a conservative 12-callback allowance for the other class. `beacon_step_uniform` and `beacon_prefix_uniform` give the full cost `D`. Public conversion, required point checks, all DH work and optional rejection remain in the same continuation.

`phase1_signing_uniform`, `phase1_writing_uniform`, `phase1_after_uniform` and `phase1_uniform` follow the actual source Phase 1 program. The body has already sampled its Beacon identity seed, one-time scalar and KEM pair. The original three Beacon signature calls, optional writer and complete publication execute deterministically from those inputs, adding no uniform request. These are locally computed Beacon signatures, distinct from challenge-signing requests in the ordinary Gap-DH game. No source signing operation is removed.

## Pending tokens and the one-shot finish

The finite `pendingCount` sums current token presence below the actual allocated Server-attempt counter. `pending_new`, `slotWeight_le`, `pending_clear` and `pending_extend` establish its elementary accounting laws. `accept_pending` and `accept_pending_count` follow literal source acceptance: every attempt allocates one index and installs at most one returned token there. `build_pending` and `build_pending_count` follow the actual builder: a present token is disposed of on every result, including sealing, allocation or writer failure. An absent token costs no builder work. The already proved operational invariant supplies the fact that present tokens lie below the allocated counter; it is established by the actual initial state and preserved by actual handlers.

`finish_pending`, `handler_pending_quiet` and `handler_pending_count_quiet` preserve the complete pending registry for other original capabilities, including the full Beacon finish, public queries and post-registration reveal. `pending_initial` gives the actual empty initial registry. `run_potential_invariant` transports an arbitrary resource potential through every supported state and the complete result-dependent continuation, consuming an invariant only after its preservation is supplied.

The actual Beacon finish runs only in the original `InitSent` state. `finish_coins` retains its complete cost `(D + 64)*initSentFlag`. The existing source `finish_step` proves that every such attempt leaves that phase, including failures, and other capabilities preserve it. The proof does not impose a new one-finish restriction on the adversary.

## Native build and receive costs

`registration_step_uniform` and `registration_uniform` interpret the actual native registration callbacks on their shared commitment cache. Only a commitment hash can sample, at most 64 bytes on a cache miss. `build_uniform` uses the exact `tail_native` projection to retain the complete seal log and source result, then consumes the existing native builder's one-attempt hash bound. A present-token build therefore costs at most 64 uniform queries even when sealing or either writer fails. The same source bound retains at most one attempted seal, one frame writer and one Phase 2 writer, separately.

`beacon_after_uniform` follows the literal initial KDF, optional application getter and complete raw receive. The source raw program permits up to 51 ratchet KDF callbacks and at most one hash and one optional opening. Its KDF callbacks are the actual deterministic fixed HKDF, so its total uniform cost is at most 64. Arbitrary raw parsing, cache/future paths, failed commitment/opening and later sequence-one/binding rejection retain their effects. `simulate_onCtx` and `beacon_after_coins` preserve the whole cache computation when it is lifted into the authentication game; they do not introduce another cache or charge the hash allowance once per KDF callback.

## Complete adaptive body and constructed reduction

`familyCoins_uniform`, `liftCoins_uniform` and `onCtx_uniform` preserve complete lifted-source sampling bounds. `stage_coins`, `client_coins`, `accept_coins`, `build_coins`, `hash_coins` and `handler_coins` give the actual handler bills. The Server root consumer performs its original erasure/consumption and one family request without direct sampling; the family's randomness is charged separately by B6.

`coinPotential` reserves the full prefix and possible build cost for every remaining accept, 64 for each current pending token, the complete active finish cost, and the adversary's remaining coin/hash allowances. `pending_weight_le`, `handler_flag_quiet`, `handler_cost_le` and `handler_potential` prove that every actual step pays its immediate bill while retaining sufficient potential for the continuation. `run_coins` lifts this through the complete adaptive API; `initial_potential` discharges the initial token/phase state; `body_coins` additionally charges the actual source-ordered eager generation and Phase 1. `body_budget_expanded` retains every primitive's base contribution explicitly. Unrestricted repeated builds, finishes, HMAC queries and post-registration reveals remain allowed; their actual refusal, consumed-token, phase and family behavior determine the cost.

`scan_uniform`, `reduction_resources` and `reduction_game_uniform` instantiate the exact existing B6 reduction, without replacing it by another adversary. The extractor makes zero challenge-signing requests, at most `2*qH*(Q+1) + 2*(Q+1)*(qH+Q+1) + qH` ordinary decision requests, and at most `u + 64*(qH+Q+1)` uniform requests. The final `qH` decision term is the existing candidate extractor, not another protocol-query allowance. The ordinary challenger additionally samples its own Server identity and Beacon prekey with 64 byte-valued requests. `reduction_game_budget` expands the full ordinary-game bound to:

```text
256 + qCoin + 160*Q + 64*(qHash + qH)
+ uGen + Q*uEnc + uDec
+ r*(bGen + Q*bEnc + bDec).
```

The B6 probability bound and coefficient one are unchanged. This package supplies resource premises; it adds no cryptographic loss, target guessing factor, acceptance premise or security assumption. B8b must still instantiate its actual separately sampled context and selected-entry continuation. B9b must still construct the actual optional-plaintext CTX reduction and its selected-key event. The final headline remains a consuming obligation. Serialization, persistence and primitive internals remain outside the approved proof scope; source transcriptions and the permanent primitive/runtime contracts remain as previously documented.
