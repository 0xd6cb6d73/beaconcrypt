# Server schedules and public primitive services (HB-91)

The three modules `RawCtxServerMixed`, `RawCtxServerServices` and `RawCtxServerServiceBounds` connect established Server operations and public primitive services in one adaptive source experiment. The same assigned-u64 peer map supplies identity-derived associated data, selected ratchet and publication handle. The same complete primitive state survives every call, including failed commitment/AEAD attempts. Original optional ciphertext/plaintext replies reach the original client continuation; adaptive stopping does not discard earlier effects.

This follows the reviewed integration topic at `61c7a83f3ea8f9b817a26ae87cbbb4685f9bf574`. It is an operational and resource composition. Registration, Beacon/Server replication, identity services, reveal and restoration transitions, material-position freshness, multi-key cryptographic reductions and the common symbolic/computational security event still need their enclosing experiment. A finite machine-ID map is a representation of native storage, not an enrolled-session resource bound. No identity, associated-data or record-key injectivity premise is introduced.

## Same-map source execution

`rawServer` preserves the existing source order: header routing, peer-associated-data lookup, same-entry lookup, complete owner receive, and replacement of the selected kernel. Header rejection and missing peers increment the raw-attempt counter and make no private primitive call. `sendServer` embeds the existing native send wrapper, including immutable local sender lookup, same-peer associated data, empty/exhausted rejection and publication of an advanced send state after an allocated send fails.

`raw_interpretation` and `send_interpretation` equate these computations with the existing source-shaped native games for arbitrary stateful primitive implementations. Their returned value includes the entire Server and primitive poststate. `server_interpretation` proves the corresponding one-step state reassociation, and `schedule_interpretation` proves whole `OracleComp` equality under arbitrary adaptive interleaving and target selection. These equalities retain all original replies and the complete client result; they do not replace dependent peer execution by independent one-key games.

`raw_bound` and `send_bound` derive each primitive class cap from the actual selected source helper. The dummy sender/decoder arguments in their inherited one-direction budget lemmas are unused arguments to those lemmas; they do not appear in source execution. `schedule_bound` and `schedule_bounds` compose these source caps without a scheduling or peer-selection factor. `shared_uniform` interprets the same mixed Server through the existing common KDF/commitment-cache state and counts its complete uniform-oracle work.

## Public services and private state

The extended client interface includes caller randomness, public BLAKE2b commitment queries and the existing exact-width HKDF projection interface. Private cryptographic draws remain within the backend. `public_coin` forwards only the caller's requested uniform answer and preserves the private Server and primitive states; it does not expose backend coins.

`same_hash` identifies public and private commitment requests as literally the same backend request. `public_hash` proves that the public request reads and extends the identical CTX random-oracle cache used by source sealing and opening. Failed and successful prior lookups remain in that cache. This uses the stated CTX ROM interpretation; collision resistance alone does not supply a programmable random oracle.

`public_hkdf` evaluates the supplied fixed source's complete stream and returns the requested first-32, second-32 or final-12 projection. Both source labels and exact input bytes remain in the address. Repeated projections and repeated inputs retain the same source function. No public HKDF random table, independent public outputs or public-HKDF/random-table advantage is used.

The backend receives one `source.crypto`, shared by public HKDF evaluation and functional AEAD. Its KDF callback remains an explicit parameter here. These equations alone do not prove that an arbitrary callback computes that same source's HKDF. The separately checked `RawCtxSourceHkdf` concrete callback provides that functional instantiation; cryptographic chain-output replacement still needs the actual-source material-position and freshness connection.

`native_interpretation` equates the embedded native backend with the existing complete shared-cache interpreter. The extended `server_interpretation` and `schedule_interpretation` then identify the full actual source/public computation, preserving the Server map, primitive auxiliary state, cache, original result and every adaptive reply continuation.

## Complete query accounting

A five-coordinate structural `Bounded` budget limits sends, raw receives, caller uniform requests, public hash requests and public HKDF requests. It constrains every possible reply continuation. `source_bound` projects each coordinate to an ordinary selective query bound, including rejected requests and deterministic public HKDF calls. Denote the respective caps by S, R, U, H and K, and let C bound the uniform-oracle cost of each interpreted native KDF callback for every request and primitive state.

| Checked source/backend quantity | Bound |
| --- | --- |
| Native ratchet KDF calls | S + 51R |
| Native AEAD seals | S |
| Native AEAD opens | R |
| Shared private/public commitment queries | S + R + H |
| Native writer calls | S |
| Original caller uniform requests | U |
| Original public fixed-HKDF projection evaluations | K |
| Complete interpreted uniform-oracle calls | U + C(S + 51R) + 64(S + R + H) |

The 51 coefficient follows the source receive-window proof, including arbitrary represented entry states and failed attempts. No assumption makes unspecified ambient queries free. `bill_step` proves exact coordinate consumption; `weighted_bound` composes per-step bounds through the complete stateful program. `source_uniform_step`, `uniform_bill` and `schedule_uniform` derive the displayed uniform bound. Each send costs at most C+64, each raw attempt 51C+64, each caller uniform request one, each public hash query 64, and each deterministic public HKDF evaluation zero additional uniform requests.

`nativeLift_bound` preserves individual native classes. `backend_step`, `native_bill`, `backend_bound` and `backend_bounds` prove the five concrete native caps in this same extended schedule. Public hash requests contribute to the existing private commitment class, while public HKDF and caller randomness keep their distinct source coordinates.

The aggregate unit is uniform-oracle calls. Explicit 64-byte CTX cache-miss samples consist of byte-valued uniform calls; caller randomness can request another finite range. Zero uniform cost for fixed HKDF, functional AEAD or writing means those functions use no additional randomness in this presentation. Their primitive evaluations, input lengths, byte processing, parser/writer traversals, copies, maps and supplied local computation retain their actual work. The K public projection evaluations and all native callback counts remain explicit. This ledger is not a compiled-runtime or byte-work bound.

## Trust and observation scope

The exact source games retain arbitrary optional native effects. The shared specialization uses total functional AEAD, the stated total CTX ROM and an optional functional writer. Writer success does not guarantee native parser success, canonical encoding or availability. Native reader/writer/map/slot representation, immutable field access and synchronous ownership remain functional source/library boundaries. Compiler and primitive implementations, allocator/OS behavior, physical erasure, foreign-runtime copies, storage integrity/rollback resistance, linearizable CAS and crash behavior remain the documented external contracts.

The raw API returns actual optional plaintext. An enclosing network experiment must specify which API replies are declassified and apply its target-plaintext freshness rules; these interfaces alone imply no secrecy from an observer explicitly given the target plaintext. Complete state in theorem results is private analysis state, not an added adversarial reveal service. Current-chain compromise, copied/restored material and repeated failed-receive derivations still require explicit global treatment. These modules do not assert post-compromise recovery, assigned-ID agreement for later records or a global computational interpretation of every symbolic correspondence.

## Milestone validation

Independent review inspected all 27 theorem statements and bodies, the full-state simulation, the five source budgets, the shared commitment-cache wiring, real public HKDF evaluation and the observation/trust limitations. Fresh full `lake build` passed 3,251 jobs; the three modules contain exactly 9, 7 and 11 guarded axiom reports. Reviewed inventory passed with 201 handwritten Lean units and 365 total entries, and root-import, forbidden-placeholder/custom-axiom, Rust formatting and whitespace checks passed. The fresh transcript-fidelity run passed all 16 tests, including its independent mutation controls. Production, symbolic models and runtime validation inputs are unchanged in this milestone; the complete configured mutation run and final integration matrix remain separately required.
