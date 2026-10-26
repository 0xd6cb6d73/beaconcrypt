# HB-115: selected message-key and live experiment interfaces

HB-115 supplies the actual source sampler for a selected record's message key, a CTX reduction that preserves adaptively generated surrounding keys, a private honest-application observation interface and dynamic native Beacon creation. Eleven modules add 82 guarded statements. These are checked composition interfaces with concrete source and primitive reductions. The final source-to-CTX compiler, byte-level freshness simulation and replicated symbolic correspondence remain active work; these separate results are not asserted to close that composition automatically.

## Actual first- and later-record source endpoints

`PqxdhAdaptiveMessageKeySource.first_bound` and `later_bound` connect the original generated adaptive-target source comparison to an ordinary uniform message key sampled after the complete retained source preparation, selected nonce and next chain. Every other source field and callback remains in the original continuation. The source first32 message key, second32 next-chain value and final12 nonce reconstruct one full76 response. The two latter values are private simulator data, not necessarily public observations. The equality quantifies over the complete continuation and evaluated distribution, not only the marginal key distribution.

The first-record comparison retains the original coordinate reduction loss. A later record at depth + 2 additionally pays `(T + 1)/2^256 + Σ[j<T](j + 1)/2^256`, where `T = 7 + 67*qPost`. This term handles the actual prior-input collision and chronological cached-prefix normalization. It does not assume that the final source lookup is always a fresh table miss. The remaining coordinate loss is the actual HB-112 joint identity, KEM, Extract, HMAC, tester and chain-collision loss already carried through HB-114's proved target projection.

The preparation bills are `qPrior + 108` for record one and `qPrior + 64 + V + 120` for a later record. Here V is the actual stopped-source sampler bill derived from the original post and callback caps. The first preparation pays shared64 + nonce12 + next-chain32; the later one also pays the complete76 parent draw. The ordinary primitive challenger supplies its separate 32-byte selected key. The final mathematical observers still take that key to reconstruct the source and freshness checks. They are not themselves executable key-free CTX reductions.

| Module and statements | Meaning |
| --- | --- |
| `PqxdhAdaptiveFinalMaterial.later_source`, `later_bound` | Instantiate the existing averaged later-source endpoint at remaining depth zero, retaining the actual source support and event, then compose its explicit cached-prefix/input-collision terms with the original coordinate reduction. |
| `PqxdhAdaptiveFirstMaterial.source`, `bound` | Identify record one's actual full76 source continuation from the empty private table and consume the original coordinate bound. Completed/common branches retain their original decision; unused draws are removed only by a complete-distribution equality. |
| `PqxdhFinalMaterialKeySplit.reconstruct`, `complete` | Reconstruct the exact full response and move the uniform selected key after the retained nonce and next chain through the entire continuation. |
| `PqxdhAdaptiveMessageKeySource.first_source`, `later_source`, `first_bound`, `later_bound` | Give the exact ordinary key-last distributions and the corresponding constructed source advantage bounds. The preparations include actual original state and supported stopped continuations. |
| `PqxdhAdaptiveMessageKeyResources.first_prepare`, `later_prepare` | Derive both complete preparation bills from the original source certificate and actual primitive callback costs. |

## The hidden material slot

`RawCtxSelectedMessageKey` uses a private selected-material marker together with unchanged known material. Interpreting the marker inserts the selected key while retaining its nonce; every old slot, staged skipped key and source control field remains exact. Different slots may have equal byte values. This representation does not assume alias freedom or answer a forbidden selected-key reveal.

| Statements | Meaning |
| --- | --- |
| `decoded_selected` | The native full76 decoder produces the original next chain and selected material with its actual nonce. |
| `known_kernel`, `known_slots`, `known_receive`, `known_send` | Lifting earlier material into known slots preserves the entire old kernel, staged entries, receive request and send request when interpreted back. |
| `receive_selected`, `send_selected` | The exact source resumption installs the selected marker while retaining all state, failure and advancement behavior. |
| `key_observed`, `decoded_observed`, `receive_observed`, `receive_prepared` | A previously justified uniform full76 response factors through the ordinary key-last experiment, including the complete actual receive continuation. Fixed HKDF is not declared uniform by these equalities. |
| `prepare_receive_bound` | Actual receive preparation pays its original sampler plus 44 nonce/next-chain byte draws, with the challenger key counted separately. |

## CTX with adaptively generated surrounding keys

`AdaptiveCtxDynamicKnownKeys` gives one selected key to the ordinary CTX challenger. Other calls supply their actual known keys, decoders and history slots at the moment those calls occur. They need not be fixed in advance or independent of prior replies, and equal key bytes are allowed. The reduction performs their real local work and forwards every hash request to the same challenger cache. Known-call arguments are private simulator data. They are not new network disclosures.

`AdaptiveCtxDynamicKnownBounds.selected_integrity` compares the real selected source with its replay endpoint. Its explicit loss is the constructed validation IND$ advantage, plus `qHash/2^128`, plus twice the sum of the constructed attempt-indexed INT-CTXT advantages over all qRaw attempts, plus `qRaw/2^512`. `selected_privacy` adds the constructed view IND$ advantage to reach the existing random-view endpoint. Both retain the existing `qSeal < 2^96` precondition and the ordinary nonce-rejecting interface. The actual source compiler must still prove its nonce behavior, decoder consistency and complete query/candidate ledger; successful publication alone is not substituted for all internal seal attempts.

| Statements | Meaning |
| --- | --- |
| `AdaptiveCtxDynamicKnownKeys.selected_step`, `known_step`, `linked_step`, `linked_schedule` | Every selected and known-key request has the same actual optional reply, complete histories and common hash cache through the entire adaptive continuation. |
| `AdaptiveCtxDynamicKnownKeys.schedule_interpretation`, `source_view` | The constructed ordinary client has no selected-key argument and gives the same complete execution or decision after challenger interpretation. |
| `AdaptiveCtxDynamicKnownBounds.target_step`, `target_bound` | Known local operations create no selected seal/raw query; selected calls preserve their exact source category. |
| `AdaptiveCtxDynamicKnownBounds.hash_step`, `hash_bound` | Every selected public hash and forwarded known-key hash is charged. |
| `AdaptiveCtxDynamicKnownBounds.uniform_step`, `uniform_bound`, `decision_budgets` | Explicit local randomness and selected seal/raw/hash ledgers remain separate and hold for the actual constructed client. |
| `AdaptiveCtxDynamicKnownBounds.selected_integrity`, `selected_privacy` | Consume the maintained ordinary CTX/nonce-AEAD reductions with the explicit losses above and every adaptive acceptance attempt included. |
| `AdaptiveCtxDynamicKnownBounds.plaintext_step`, `plaintext_bound`, `decision_plaintext_bound` | Preserve the selected plaintext-byte bill through the actual adaptive wrapper and final decision client. Known local encryption is not an uncounted target request. |

No new primitive implementation or security theorem is asserted. The modified nonce-AEAD endpoints and programmable classical ROM remain the previously stated primitive contracts. Known-key local AEAD, fixed HKDF, parsing, table access and copying remain actual computation; the query counts do not declare that work free.

## Live application and allocation

The [private application guide](live-private-application-observation.md) explains all 24 statements in `LiveApplicationObservation` and `LiveApplicationNative`. The actual role families, shared primitive cache, public fixed-HKDF and reveal services remain present. An honest application callback receives only its own state and explicit random interface. Public logging includes the request and actual ciphertext reply, while privileged raw receive continues to return its actual optional plaintext. Acceptance-only network delivery is a distinct capability. The same joint initial sampler gives the same full public-observation distribution; the native sampling bill is `qInitial + 64*qPublic + qHonest*qApplication`.

The [creation guide](live-beacon-creation.md) explains all 16 statements in `PqxdhLiveBeaconBirth`. Normal validated construction generates identity, prekey and KEM in source order and installs the complete Fresh state before later API calls. The one-time draw remains later. Dynamic allocation preserves earlier indices and common state; its actual birth count bounds the possible owner indices. The sampling bill is `(32 + qPrekey + qKeygen)*qBirth + qOwner*qCall`, with the actual initial sampler and later one-time work counted separately. Instantiating every owner capability and dynamic Server registration remains necessary.

## Remaining consuming obligations

The concrete source compiler must externalize selected seal/open operations without knowing the key, forward the challenger's actual optional plaintext and preserve both raw and public observations. Direct selected-material disclosure must be handled by the source freshness event. Adaptive known-key, root, chain and public-HKDF candidates can equal the selected key; these byte comparisons require counted events and a proved coupling, not a silent marker-inequality premise. Common attacker-owned or ineligible branches retain their original decisions, so privacy cancellation and authentication gating remain distinct.

Inner cryptographic sealing, optional serialization and successful public record publication are also distinct histories. Ordinary send advancement survives failed serialization in the actual source, but transactional registration retries and unpublished seal origin require their own complete accounting. Dynamic creation must be embedded into the original generated-root experiment with all repeated signing attempts counted. The target-relative symbolic event map must retain actual public recipe equality after permitted compromise. Snapshots, persistence and restoration remain excluded, and public fixed HKDF is never replaced globally by an independent table.
