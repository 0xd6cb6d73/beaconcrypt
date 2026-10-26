# First acceptance and its source history

`PqxdhServerAuthCtxAcceptanceHistory` proves the operational history needed to use the selected CTX receipt lemmas in a complete Server-authentication execution. The original source records only the first accepted response, together with its actual touch and seal logs. Later queries cannot overwrite that observation. The proof works for arbitrary typed derivation and native-tail replies, including the uniformly replaced 108-byte factor; it does not import the original-key game invariant into that hybrid.

## What is preserved

`History` has three properties. While the Beacon remains in `InitSent`, no acceptance has been recorded. Any recorded observation contains prefixes of the current touch and seal logs. Its touch log ends with the actual Beacon derivation request and contains no earlier Beacon request. The existing `Shape` invariant supplies only allocation and one-shot source chronology. Neither invariant asserts key independence, an honest selected identity, a successful opening or authentication.

The source type calls this observation a `Snapshot`. It is a ghost record used to define the first-acceptance event; this module neither models nor reasons about saving, restoring or rolling back protocol state.

## Concrete source cases

`History.finishTouched` consumes the literal `finishOutcome` function after the actual prepared request has been appended. The original phase transition leaves the Beacon aborted or established on every optional staged result. If acceptance occurs, the original `Ghost.accept` captures exactly the current logs. A failed preparation has no staged value and cannot manufacture an acceptance; `History.finishNone` proves that branch separately. `finish_history` joins all original raw preparation, root rejection, ordinary-root continuation, selected continuation and final-publication branches. It retains the actual optional result and all callback effects in the supported program.

`History.transport`, `prefix` and `derived` preserve prior accepted observations through the actual Server allocation and derivation updates. `skeleton_history` covers every original API operation, including both builder routes, public HMAC inside and outside the root domain, commitment hashing, coins and installed-kernel reveals. `handler_history` includes the exact one-shot designation and sticky table refusal. `program_history` proves preservation through arbitrary adaptive continuations. `History.initial` discharges the initial obligation from the literal empty ghost, and `run_history` applies it to the original complete factor-side run.

`History.first` identifies the same literal Beacon message in the accepted observation and the final source log. `History.input` therefore equates their actual byte inputs without assuming root, key or encoding injectivity. The final accepted message is not reconstructed by matching output bytes.

## Complete suffix behavior

`finish_grows` and `finishTouched_grows` prove that final acceptance handling preserves every prior log entry and any existing accepted observation. `finish_step_grows` covers the complete raw callback; `skeleton_grows` covers every source capability. `handler_grows` and `program_grows` lift these facts through the full designation/refusal wrapper and arbitrary adaptive suffixes. The actual session-attempt counter never decreases. Source writer failures, derivation rejections and permitted reveals remain in those executions.

`accepted_suffix` uses the recorded observation's preservation to prove that later source traffic cannot change the original W1/W2 event once acceptance exists. No final adversary decision replaces that event and no additional target or raw-attempt selection is introduced.

## Scope and remaining proof

These twenty statements are source-history results. They introduce no oracle request, loss or security premise and retain all existing source and component work. They do not claim that an accepted record is fresh, that every component seal was published, or that a source acceptance is already an ordinary CTX forgery. The next consumer must preserve the reviewed session-indexed `Origins` and ordinary component `Good` invariants through the actual compiled handler, use the retained-table chronology to exclude an ordinary-root acceptance from the selected input, and map the remaining original event to the existing all-attempt authentication observer. The stopped global source coupling, exact sampler and full reduction bills remain separate checked consumers under construction.

Public HKDF remains real. The approved joint-use primitive, restricted programmable Extract, shared CTX/BLAKE2b ROM, abstract message codec and external primitive/compiler contracts are unchanged. No serialization implementation or persistence result is added.
