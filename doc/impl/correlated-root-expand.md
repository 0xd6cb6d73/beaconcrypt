# Ordinary Expand for correlated source roots

`PqxdhCorrelatedExpand`, `PqxdhCorrelatedExpandHybrid` and `PqxdhCorrelatedExpandQueryBounds` extend the [correlated Extract-family comparison](correlated-extract-family.md) to a consistent table of uniform 32-byte roots. The actual optional private source is bounded by joint-use weak-EUF, ordinary ML-KEM IND-CCA, the explicit secret-input Extract-family advantage, and a sum of ordinary HMAC PRF advantages. This step reduces real Expand under the random PRKs; it does not discharge the additional Extract-family obligation.

## Exact source and cache observation

`rootReduction` independently constructs the same private source preparation and continuation using a root-valued oracle. It generates its own KEM pair, retains the complete preparation and actual encapsulation work, and keeps the KEM secret in private interpreter context. The optional initial root and all private requests at the challenge ciphertext query that oracle at the original 128-byte DH coordinates. Nonmatching ciphertexts still run actual optional decapsulation and the supplied production root function. Public CCA requests retain their separate challenge block and original effects. Public fixed-HKDF evaluation remains the real local function.

`compile_post`, `compile_resume` and `compile_reduction` are full program equalities before any cryptographic interpreter is applied. Their compiler obtains a full PRK from the earlier family oracle, performs actual Expand, and returns only its first 32 bytes. It never supplies a PRK to the protocol client. Private `Protocol.State` and the original source/role state remain reduction context rather than new network observations.

`projectCache` preserves every family address and maps its stored PRK to its derived root. `projectCache_update`, `rootImpl_step` and `rootImpl_complete` identify the full adaptive result and projected table with an independently defined root service that samples one PRK on each new address, computes real Expand, and caches the root. Repeated addresses reuse the same root. These equalities require neither PRK/root injectivity nor distinct DH encodings or generated keys. Only private PRK coordinates are projected; original source replies, effects and continued state are retained. `reduction_expanded_eq` attaches this exact root service to the published same-secret source reduction.

## Ordinary HMAC hybrid

`scan` executes the original client up to an indexed root request. It runs preceding root requests against a consistent uniform-root table and preserves all explicit coins, cache entries and the entire remaining continuation. Its index counts every original root request, including cache hits. If the client finishes first, the scan retains that completed result and cache. The all-continuation query bound rules out an unprocessed root request after the final boundary.

`scan_zero_complete`, `scan_succ_complete` and `scan_bound_complete` prove the initial, adjacent and final complete-run equalities. A selected cache miss is the sole root value changed at an adjacent boundary; the remaining suffix uses real Expand on fresh locally sampled PRKs and reuses all earlier roots. A hit reuses its cached root in both worlds.

`indexedReduction` is the existing ordinary one-query HMAC reduction with this full stopped context and continuation. It always issues the actual `INFO_PQ || 1` challenge query, including on completed or cache-hit branches. Those branches ignore the answer but retain the challenge operation and its cost. The real HMAC challenger samples a uniform 64-byte key; its answer supplies real Expand. The random HMAC challenger samples the 64-byte answer whose first 32 bytes supply the uniform root. `indexed_real`, `indexed_random` and `indexed_advantage` identify the exact adjacent distributions and ordinary Boolean distinguishing advantage. Only independently sampled, unused challenge values are erased in the evaluated equality; resource bounds are separately proved on the actual programs.

`expanded_uniform_bound` sums these adjacent distances over `q` original root positions. There is no additional stopping, duplicate-address or session-selection multiplier. Repeated coordinates keep the same table entry throughout; uniform outputs at different addresses may still collide.

## Actual authenticated source bound

`authenticated_uniform_roots_bound` composes the exact source observation and hybrid with the existing actual all-candidate private source theorem:

`distance(actual optional source, consistent uniform-root continuation) ≤ joint-use weak-EUF + ordinary IND-CCA + secret-input-family advantage + Σ i<q ordinary HMAC PRF advantage(i)`.

Each term has coefficient one. `source_uniform_ledger` supplies `q = 1+R`, where `R` bounds all original private post-root attempts. The optional initial request accounts for the one. Repeated, matching and rejected private attempts remain counted even when an attempt requires no root-oracle query.

The theorem retains the original functional source-root representation, optional native/total encapsulation compatibility, actual generated-key support, perfect KEM correctness and explicit pure functional decapsulation, attached-format law, and stated selector extra-signing/creation restrictions. These are the same functional and schedule obligations of the earlier source theorem. They are not inferred from authentication. Private requests at the challenge ciphertext remain allowed and jointly share the same family input convention; only the separate public CCA service blocks that ciphertext.

The ideal randomizes roots for the one selected challenge-secret family. Other private ciphertexts and public primitive calls remain actual. This is not yet a theorem for multiple independently sampled or related family secrets, native global registration/delivery/compromise, or a root/record schedule instantiated from all protocol roles. Distinct source coordinates, record-key independence, chain/reveal policies and pinned-Server Phase2 authentication require their own arguments. The specialized Gap-DH recovery endpoint does not itself supply that receiver-authentication simulation. No public HKDF random table or protocol-conclusion premise is introduced here.

## Query and computation ledger

Let `K` and `E` bound actual interpreted KEM key generation and encapsulation, and let `B` and `D` bound the uniform requests used by one actual base operation and decapsulation. Preparation has original public caps `uPre,bPre,dPre`; the private post computation has public caps `uPost,bPost,dPost` and private-attempt cap `R`. The complete local source bound is `Q = K + uPre + B*bPre + D*dPre + E + uPost + B*bPost + D*(dPost+R)`. The existing `rootProtocol_sampler_bounds` instantiates these caps from the authenticated private source, including source creation, both coin channels, completed-branch native/total maxima and actual observer work.

The root-valued source bounds are proved directly through every possible root reply. They are not pulled backward from the PRK compiler, which need not be surjective onto arbitrary 32-byte replies. `cached_run` retains the complete table. `selectedRun_uniform` counts original source coin requests once across the stopped prefix and continued suffix, with a conservative 64-draw allowance for each original root slot. Earlier ideal misses actually sample 32 bytes; later real misses sample 64-byte PRKs; hits sample nothing.

| Actual checked program | Uniform-request cap | Primitive-query cap |
| --- | --- | --- |
| Root-valued source reduction | `Q` | `1+R` root requests |
| Direct real-Expand cached-root game | `Q+64*(1+R)` | Local real Expand at fresh entries |
| Direct uniform cached-root game | `Q+32*(1+R)` | Consistent table lookups |
| Each indexed ordinary HMAC client | `Q+64*(1+R)` | One HMAC challenge |
| Each complete real HMAC challenger | `64+Q+64*(1+R)` | One HMAC challenge |
| Each complete random HMAC challenger | `64+Q+64*(1+R)` | One HMAC challenge |

The real challenger adds 64 byte-valued draws for its hidden key. The random challenger has no key draw and adds 64 for its one fresh challenge answer. These are checked upper bounds, including unused challenges, rather than assertions of exact total trace lengths. One arbitrary finite explicit uniform request counts once. Actual encapsulation is still paid even when its original shared secret is unused. The earlier actual source, joint-EUF, CCA and Extract-family ledgers remain unchanged.

Local HMAC/Expand, public fixed-HKDF, signatures, DH, verification, byte conversion, cache lookup and full continuation/state work remain computation. The scan is a finite recursive program over the actual client, with no enumeration of the input universe. The inherited functional-cache representation and native byte/runtime implementation still require their existing implementation correspondence; a zero uniform-query cost does not make deterministic work free.

## Focused validation

All three final modules and their 61 persistent kernel-dependency reports passed direct checks. The targeted build passed 3,141 jobs, the full Lean build passed 3,212 jobs, and the direct root check passed. Inventory validation passed with 164 handwritten Lean modules and 313 unique reviewed artifacts. The fresh transcript-fidelity suite passed all 16 tests in 12.53 seconds. Formatting, whitespace and placeholder/custom-axiom scans passed. Fresh fetched and direct `origin/vcvio` both identified `8330cdef4f4659931b6764a026cd90c4caf833a4`, an ancestor of this topic. Three imports, named statement/guard gates and three inventory additions preserve all previous paths and ordering. No Rust or ProVerif source changed, and no full mutation suite was rerun for this proof/documentation checkpoint. These are focused source/Expand validation results; the additional Extract-family and native/global obligations above remain open.

## Combined topic validation

The current computational topic ports all three modules and 61 statements unchanged from `8851b3dd660a0103c060f228442bf22345d617ea`, together with both material-interpretation modules and 33 statements unchanged from `42ec049a10eccb8bb2865f4b7eb3678dd3e1fc2d`. The incoming ordinary Expand documentation also updates the earlier Extract-family paragraph to point to this now-checked hop. The material interpretation preserves noninjective payloads and complete callback effects; the surrounding source KDF/begin/resume/owner erasure and computational material-distribution obligations remain separate. Shared references are reconciled semantically while preserving the newer symbolic integration.

All five modules and 94 persistent dependency guards pass direct checking without diagnostics. The combined full Lean library passes 3,299 jobs. Policy, root-import, reviewed-inventory and whitespace gates pass with 249 handwritten Lean modules and 413 reviewed artifacts; all previous 408 paths and their order remain. HB-91 now records 440 operational statements, while HB-94 retains its 59-statement independent primitive-key scope. Fresh formatting and all sixteen transcript-fidelity tests pass, with the fidelity suite taking 12.18 seconds. No Rust or ProVerif source changed, and no Rust mutation rerun is required under the current user instruction.

The verified source bound retains joint-use weak-EUF, ordinary CCA, the explicit additional secret-input Extract-family advantage and at most `1+R` ordinary one-query HMAC terms. The complete source and reduction ledgers above include every original private attempt, duplicate lookup and unused challenge. These focused combined-topic results do not assert smallness of the extra Extract-family advantage, source-wide root-family independence, global compromise freshness, pinned-Server authentication or the final computational-symbolic theorem. The complete final verification matrix on the eventual validated global integration is still required.
