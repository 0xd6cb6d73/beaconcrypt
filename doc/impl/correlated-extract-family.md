# Correlated secret-input Extract family

`PqxdhCorrelatedExtractFamily` connects the [authenticated same-secret source world](correlated-private-source-root.md) to an explicit ordinary secret-input family game. The source comparison has three coefficient-one terms: joint-use weak-EUF, ordinary ML-KEM IND-CCA, and the new family distinguishing advantage. The family term remains an additional cryptographic obligation. This checkpoint proves the reduction and its resource bounds; it does not assert that the new advantage is small or that ordinary HMAC PRF security implies it.

## Exact primitive game

The real challenger samples one uniformly random 32-byte secret `s`. A client can adaptively submit any 128-byte message `m` and receive the entire 64-byte value `HMAC-SHA512(zero64, FF32 || m || s)`. The client also has explicit finite uniform queries. The random challenger answers each distinct message with one uniformly sampled 64-byte value, retaining a consistent table for repeated messages. Its only winning observation is the client's final Boolean. Neither endpoint contains role acceptance, authentication, freshness, ownership or a protocol-secret recovery predicate.

The secret is a suffix of the Extract input. It is not the HMAC key: that key is the fixed public zero salt. Consequently this is an ordinary real-family versus random-function experiment for a specifically defined secret-input family, not ordinary secret-key HMAC PRF. The full-PRK reply deliberately exposes more than the protocol's projected root. No small-advantage contract is introduced as a Lean premise, and no reduction to textbook HMAC PRF is claimed.

The earlier one-sample `SecretInputSampler` endpoint cannot automatically discharge this adaptive interface. Placing the shared secret in its retained context would allow the whole PRK to be recomputed. Placing later adaptive family outputs behind a hidden service instead requires precisely an additional oracle interface. The existing fixed-zero-salt countermodel already separates ordinary HMAC PRF from Extract pseudorandomness. The present term displays that extra obligation instead of assuming independently random roots after the KEM hop.

`coordinates` concatenates the four exact 32-byte DH coordinates into the 128-byte public family message. `familyInput_source` identifies the resulting 192-byte input with the actual source input. `familyInput_length`, `familyInput_message_injective` and `familyInput_eq_iff` prove its width and exact duplicate-input behavior with the same suffix. These are byte-list statements; they assume no encoding canonicality, point injectivity or distinct generated keys. `random_hit` retains the existing complete PRK and cache, while `random_miss` samples and installs one new PRK.

## Complete private source reduction

The ordinary family client generates its own KEM pair, runs the complete private source preparation, and performs actual ordinary encapsulation. It retains its locally generated KEM secret, public key, preparation state and ciphertext. It never receives the family challenge secret. Even when the encapsulation's real shared secret is unused, that encapsulation remains part of the client's actual computation and cost.

An optional initial root queries the family at the actual four coordinates, then applies the real HMAC Expand and first-32-byte projection. The post handler retains the separate public CCA service, including its challenge block. Every private request at the challenge ciphertext queries the same family at that request's unchanged coordinates. Every other private ciphertext runs actual decapsulation and the same supplied production root function, retaining its optional failure. Public fixed-HKDF evaluations remain the original local function in both worlds. There is no public HKDF random table.

`root_real` uses only the existing functional `SourceRootCorrect` law to identify actual Extract/Expand output. `post_real`, `post_complete`, `resume_real` and `reduction_real` preserve arbitrary full continued output and the represented private state. `real_eq_correlated` moves the independent family secret past the entire preparation using a full continued distribution equality. It preserves the actual keygen/preparation/encapsulation operations and all later correlated requests; it does not use a marginal key-pair equality. The original identity/prekey/KEM/one-time order remains covered by the prior complete source-prefix theorem.

Private `Protocol.State`, role state, selected input and source history are interpreter context inside the reduction, not values newly exposed to a network adversary. Source validation, optional rejection and role ownership still determine which private calls occur. Local access to the reduction's own KEM secret does not provide the independent family secret. Other ciphertexts or public guessed inputs that happen to produce related values remain available to the family client; no collision or independence premise suppresses them.

## Source bound and limits

`correlated_advantage_eq` identifies the exact extra distance with this ordinary family advantage. `authenticated_family_bound` composes it with the published actual all-candidate source theorem:

`distance(actual optional source, random-Extract-family continuation) ≤ joint-use weak-EUF + ordinary IND-CCA + secret-input-family advantage`.

Each term has coefficient one. The bound retains the original signature service's converted-static-DH auxiliary capability, actual target key-generation support, optional native/total compatibility, perfect KEM correctness, explicit pure functional decapsulation, the source root representation law, and the selector's stated extra-signing/creation restrictions. Those functional or schedule contracts are not replaced by authentication premises. The source observer remains private and all actual private challenge-ciphertext derivations remain allowed.

The random comparison still computes real Expand under each installed PRK. Repeated inputs share that PRK. The [ordinary Expand follow-on](correlated-root-expand.md) now replaces the projected roots by a consistent uniform table through an indexed ordinary HMAC sum; it preserves this same PRK-family observation before the replacement. Multiple separately sampled or related family secrets, global role registration/delivery/reveal instantiation, pinned-Server Phase2 authentication and the final integrated protocol theorem remain separate. In particular this family result does not supply the missing static-DH receiver-authentication argument.

## Query and computation ledger

`PqxdhCorrelatedExtractQueryBounds` proves all counts on the actual programs through every possible reply and continuation. Let `K` and `E` bound actual interpreted KEM key generation and encapsulation. Let `B` and `D` bound the uniform requests made by one actual base operation and decapsulation. Preparation has original public class caps `uPre,bPre,dPre`; the private post computation has public caps `uPost,bPost,dPost` and private-attempt cap `R`.

The family reduction's local uniform cap is `Q = K + uPre + B*bPre + D*dPre + E + uPost + B*bPost + D*(dPost+R)`. It makes at most `1+R` family queries. The optional initial root accounts for the one. Every private attempt is counted, including repeated, matching and rejected requests, although a matching request itself performs no local decapsulation. Public CCA challenge rejection likewise remains counted by the original logical cap.

| Actual checked program | Uniform-request cap |
| --- | --- |
| Ordinary family reduction | `Q` |
| Complete real family challenger | `32+Q` |
| Complete random family challenger | `Q+64*(1+R)` |

The real family oracle's HMAC evaluation adds no sampling. The random challenger has no secret-key draw; a cache hit samples nothing, and a miss samples 64 byte-valued draws. `random_run_uniform` retains the complete table through arbitrary continuations before projecting the game result. One arbitrary finite client uniform request counts once. These bounds are derived independently of the evaluated source/family distribution equality.

The prior `rootProtocol_sampler_bounds` supplies the concrete authenticated source protocol's preparation and post caps, including interpreted source creation, both coin channels, native/total branch maximum and actual observer work. The original source's independent sampling ledger remains unchanged. Local source signature/DH/reveal/verification work, actual public fixed-HKDF evaluations, parsing, copies, cache lookup and state/history work are still computation. Each family request evaluates one local Expand; each real family-oracle request also evaluates one Extract at the 192-byte input. The complete reduction is not assigned a free local runtime merely because these deterministic operations do not use the uniform oracle. Native primitive and global byte/runtime instantiation remain explicit obligations.

## Focused validation

Both final modules and all 33 persistent dependency reports passed the targeted build and direct checks. The full Lean build passed 3,209 jobs, the direct root check passed, and inventory validation passed with 161 handwritten Lean modules and 310 unique reviewed artifacts. The fresh transcript-fidelity suite passed all 16 tests in 12.72 seconds. Formatting, whitespace and placeholder/custom-axiom scans passed. Fresh fetched and direct `origin/vcvio` both identified `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. The two imports, named theorem/guard gates and two inventory additions preserve all previous paths and ordering. No Rust or ProVerif source changed, and no full mutation suite was rerun for this proof/documentation checkpoint. These results validate the focused source/family reduction and its explicit outstanding obligation, not a complete integrated protocol security claim.
