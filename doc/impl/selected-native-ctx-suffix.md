# Selected native CTX suffix

This lane resumes the unfinished selected-message suffix after the Lean 4.34 migration. It changes proof code only. The selected message key is the first 32 bytes of the already justified full76 output; its nonce and next chain remain the original final12 and second32 projections. The work does not assert that arbitrary native clients can be simulated without this key.

## Exact raw receive compiler

`RawCtxSelectedReceiveCompiler.native_raw` connects the actual extracted whole-owner raw receive to an executable program over the dynamic selected/known-key CTX interface. The executable `receive`, `calls`, and `raw` definitions have no selected-message-key parameter. Only the mathematical `evaluated` interpreter and native material interpretation receive that key. The compiled program forwards the original raw bytes inside the existing checked universal context framing; it never recovers a plaintext and inserts it into an adversarial target.

The theorem holds for arbitrary raw input and arbitrary represented owner state. Empty input, parser rejection, wrong sender, malformed payload, invalid AD width, stale or consumed cached slots, exhausted/future receive paths, failed commitment and failed AEAD opening retain the original behavior. Success consumes the actual source-selected material through the same original finish. The API returns exactly the challenger's optional plaintext, and the equation retains the complete owner, attempted-receive count, metadata, auxiliary source state and commitment cache. It erases only added CTX game bookkeeping when projecting back to source state. The full component state remains in the compiled experiment.

`RawCtxSelectedReceiveScope` proves target and context preservation for the actual admission and every typed KDF reply before any opening result exists. Its scoped driver projection lemma is instantiated with concrete source and CTX callbacks. The raw prelude derives the nonempty-input, decoder, sender/AD validation and protected-payload facts needed by the component adapter; none is a successful-opening assumption.

Every raw attempt has at most one dynamic CTX call, including malformed or rejected attempts. The underlying source driver still charges up to 51 private-table lookups, and the lookup route preserves predecessor priority, selected address, retained cache values and real source fallback. The total dynamic bound does not erase those local lookup costs, parser work or the primitive-internal hash/AEAD ledgers. These existing component ledgers remain the relevant endpoint query bounds.

## Recovered source adapters

`PqxdhSelectedMessageBeacon.owner_source` proves the complete attempted Beacon finish under the exact selected-material source driver. Preparation, response getter, optional original initializer, sequence-one and binding checks, abort/established phase, publication and ambient state are retained. The initializer keeps every known kernel field, including possible byte aliases. This is a source representation equation; it does not yet replace all finish callbacks by an ordinary CTX challenger.

`PqxdhSelectedMessageBuilder.ready_source` proves the corresponding complete initial Server builder equation using the actual selected-material send driver. It retains current allocation and identity checks, consumed registration data supplied by the surrounding source builder, first seal, erase callback, optional serializer result and publication. The native interpreter alone receives the selected message key. This equation does not yet discharge the selected-nonce stop in the complete CTX reduction.

`RawCtxSelectedChallengeFamily` recovers the executable finite role-family compiler, including original frontend routing, parser, sender/AD selection, reveals, real public HKDF and both outer stop and inner native failure options. Its seven checked statements cover prior/public behavior, retained stopping observations, fresh-event falsification on a hidden reveal, and the candidate bill. A bounded schedule with `qReveal` reveal requests adds at most `qReveal` known candidates, including repeated and unsuccessful attempts. This count is not a key-guessing probability theorem. This module is an executable candidate for composition; its current statements do not prove that the entire mixed family schedule equals production.

## Remaining suffix obligations

The complete mixed suffix must still join raw receive with source send, Beacon finish and initial Server publication in one stopped adaptive execution. The selected-nonce refusal must be retained and charged by the actual source occurrence/ownership trace. The original final Gate/Fresh event, target-record/session selection, known-key alias and reveal candidate events must be connected to that same execution. The saved-descriptor continuation must be compiled concretely; a general native pending client can inspect secret material and is not assumed simulatable.

No primitive internals, snapshots, persistence or restoration are modeled. Public HKDF remains real. The CTX component uses the previously declared classical shared random-oracle and nonce-AEAD contracts; this lane adds no cryptographic security assumption or advantage bound.
