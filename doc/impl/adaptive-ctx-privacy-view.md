# Adaptive one-key CTX privacy view

This HB-85 extension connects the existing complete-cache adaptive CTX comparison to an ordinary Boolean nonce-AEAD IND$ experiment. It preserves the actual optional plaintext interface and every failed private lookup, then projects only the original adversary's final decision before replacing ciphertexts. The record key retained by earlier coupling proofs is analysis state; it is never part of this distinguisher's output or an adversary reveal.

For a Boolean adaptive client with source caps `qHash`, `qSeal`, `qRaw` and `qSeal < 2^96`, `AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound` proves:

```
Adv(canonical public decision, explicit random replay simulator)
  <= AdvIND$(prefix validation reduction)
   + qHash / 2^128
   + 2 * sum(i < qRaw, AdvINTCTXT(indexed reduction i))
   + qRaw / 2^512
   + AdvIND$(ciphertext view reduction).
```

The prefix reduction is the unchanged `AdaptiveCtxPrefixValidation.validationReduction`. Each integrity reduction is the unchanged `AdaptiveRawNonceAead.indexedReduction` applied to the original `wrapped` CTX client, original raw decoder and actual index. Both copies of that same family remain: one pays for the opening-reply simulation and the other for the retained-key prefix-event transfer. The private dictionary term counts every raw slot once. The new `viewReduction` is a separate ordinary Boolean encryption distinguisher; no primitive security premise is added or silently strengthened.

## Exact optional-reply simulation

`PublicHistory` stores only successful full CTX records returned by original sealing queries and the plaintext submitted with each request. `recordReply` updates it only for a successful seal. `publicReply` decodes the original raw bytes and compares the complete nonce, associated data and CTX record against that history. It returns the previously submitted plaintext on an exact match, and otherwise returns none. It does not recover a hidden plaintext or insert one into an adversarial target.

`guard` forwards each unchanged source request before choosing the response delivered to the original client. Non-raw replies are unchanged. A raw request still executes its actual parser/private-cache/counter operations, including a failed lookup or rejected opening; only its resulting optional reply is replaced with `publicReply`. `guardedClient` retains that full public history. This history is public to the chosen-plaintext component client because the same client submitted every recorded plaintext. That observation is not a claim that a network attacker knows every honest application's plaintext.

`guardedRaw_eq_replay` proves exact equality of the raw-query result and complete next state after this replacement. `loggedImpl_recordReply` proves that the redundant public history equals the direct source's actual successful full-record history after every supported source query. No key freshness, honest-cache-only provenance or private-cache absence assumption is needed. `guard_query_complete` combines those facts into complete per-query equality, and `guard_run_complete` lifts it through arbitrary adaptive continuations. `guardedGame_complete` erases only the duplicate public log. `retainedGuard_complete` retains the same sampled key jointly with the entire source result and cache while proving equality with the existing full-tuple replay game. These are full computation equalities, not comparisons of marginal ciphertext distributions.

`viewReduction` runs the existing ordinary `sourceClient` on this guarded client and returns only the original Boolean decision. The ordinary client forwards encryption and explicit uniform requests, and uses its issued plaintext log for opening simulation. `viewReduction_real_eq` first uses the checked full-source interpreter equality and then the complete guarded/replay equality to establish the exact ordinary real IND$ experiment. Thus no ciphertext replacement is justified by exposing a terminal secret key to the adversary.

`randomView` is explicitly `modifiedNonceAeadINDDollarRandomExp` applied to that same reduction. Its sealing oracle returns independent ciphertext body and tag bytes of the submitted length at fresh nonces and rejects nonce reuse. The same key-free CTX source-cache code and full-tuple replay guard remain in the simulator. It samples no hidden record key. This definition is a concrete ordinary primitive client; it is not a new assumption. A stronger description as an independently specified canonical random CTX source still needs a separate equality proof. The present theorem does not infer that different projections, repeated expansion outputs or unrelated keys are independent.

`replay_random_advantage` identifies this one hop exactly with the new ordinary IND$ advantage. `canonical_replay_advantage_bound` contracts the previously checked complete-cache coupling to the original Boolean decision. `canonical_random_advantage_bound` then applies the Boolean triangle inequality, retaining all terms shown above. The existing classical hash-ROM interpretation and exact modified nonce-AEAD contracts are unchanged; collision resistance alone does not supply that ROM interface.

## Query and byte accounting

`guard_query_bound` and `guardedClient_query_bound` preserve any source query-class budget because each original slot forwards one identical request. Raw attempts include malformed, repeated and rejected inputs. `viewReduction_seal_bound` gives the new reduction exactly the source upper cap `qSeal`, with no additional validation seal. `viewReduction_uniform_bound` gives `qCoins + 64*(qHash + qSeal + qRaw)` explicit uniform-oracle calls. Every actual digest miss contributes 64 byte-valued draws; `qCoins` may count arbitrary finite uniform requests and is not restricted to byte draws.

The weighted statements `guard_plaintext_step`, `sourcePlaintext_bind`, `guardRun_plaintext_bound` and `guardedClient_plaintext_bound` retain the total submitted plaintext-byte budget through arbitrary initial public histories and all possible adaptive replies. `viewReduction_plaintext_bound` transfers that same `qBytes` budget to the ordinary client without adding a plaintext or dropping rejected submissions.

`viewReal_uniform_bound` charges the complete ordinary real experiment `32 + qCoins + 64*(qHash + qSeal + qRaw)` uniform calls, including its 32 key-byte draws. `viewRandom_uniform_bound` charges the complete random experiment `qCoins + 64*(qHash + qSeal + qRaw) + qBytes + 16*qSeal`, with no key sampling. Nonce-reuse rejection can reduce actual draws but does not remove a submitted request from its source budget. These resource statements do not require the strict nonce-space cap; the privacy theorem still needs it through the existing prefix-validation proof.

The unchanged prefix-validation reduction has `qSeal + 1` seals, the same source/digest uniform cap and the same `qBytes` budget because its extra message is empty. Its complete random challenger has the separate `16*(qSeal + 1)` tag cap. Each indexed integrity reduction has at most `qSeal` seals, the inherited uniform cap and one final verification of the unchanged selected tuple. Earlier stopping bounds include every source raw position. The two integrity coefficients in the probability bound do not represent extra primitive queries within a single selected reduction.

All byte decoding, full-record comparisons, history scans/copies, primitive evaluations and state bookkeeping remain local computation. The source and reduction budgets count oracle requests and submitted payload bytes, not compiled machine instructions or physical memory. The inherited abstract finite cache and oracle representations do not by themselves prove compiled Lean executability or a machine-runtime bound.

## Remaining protocol boundary

The component has one hidden encryption key and the existing typed `RawDecoder` parameter. It preserves source cache effects but does not consume ratchet keys, serialize whole-owner send/receive state or implement the native CryptoFrame parser. Per-key nonce discipline is inherited from the ordinary sealing endpoint; equal nonces under unrelated keys are not forbidden by this theorem. Native source provenance, correlated evolving keys, copied/restored state, permitted reveals, target/session selection and the common global experiment remain separate work.

An eventual confidentiality statement must specify which native API results reach the adversary. If a public receive capability releases a target plaintext, its freshness or declassification policy must account for that release. This component returns the actual permitted optional plaintext and proves no secrecy claim that contradicts that interface. It does not establish assigned-ID equality, global protocol secrecy, an unrestricted post-registration state machine or computational soundness of all ProVerif constructors.

No primitive algorithm or implementation proof is attempted. Primitive functional/security contracts, compiler and native-code correspondence, physical erasure and deployment storage integrity, rollback resistance, ownership, crash behavior and linearizable persistence remain explicitly outside this focused result.

Focused validation passes the two new modules and all twenty persistent guarded dependency reports, the complete 3,196-job Lean build, direct root import, reviewed inventory with 146 handwritten Lean modules and 295 unique entries, formatting, placeholder/custom-axiom and disabled-linter scans, and whitespace checks. All guarded dependencies are standard `propext`, `Quot.sound` and, where used, `Classical.choice`. The initial root check caught the new imports after the module documentation; moving them into the existing import block resolved that integration error, and the complete build and direct root were rerun successfully. Fresh fetched and direct private-remote `vcvio` refs both returned `8330cdef4f4659931b6764a026cd90c4caf833a4`, already an ancestor of this focused topic. No runtime or ProVerif interface changes here; the complete runtime, symbolic and mutation matrix remains required on the eventual reconciled integration result, and no global closure is claimed.
