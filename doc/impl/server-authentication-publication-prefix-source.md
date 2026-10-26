# Actual publication timing before the first selected raw request

The sixteen statements in `PqxdhServerAuthPublicationPrefixStop` and `PqxdhServerAuthPublicationPrefixSource` give the concrete source a before-raw publication observation and connect it to the already bounded stopped source. The observation records whether an actual selected outer publication completed before the first selected raw request. A publication after that request cannot change the captured event. The actual accepted-owner/public-journal implication remains a separate consumer; this package does not infer publication authentication from the prefix comparison alone.

## Exact prefix observation

`PrefixStop.Spec` adds private Boolean markers to the unchanged dynamic component interface. A marker returns only Unit; it is never sent to the adversary. `erase` removes markers, and `kill` terminates when a true marker is encountered. `erase_lift` and `kill_lift` prove that lifting an original component program preserves all its queries, replies and continuation when it contains no marker.

`capture` keeps the actual selected seal reply and a sticky publication flag. It forwards every preceding real component query and reply, including known-key work with equal key bytes. On a marker, it updates the flag. On the first selected raw request, it returns the current flag and actual saved record/raw pair without decoding or issuing the opening. If there is no saved record or no raw request, there is no candidate. `capture_query` gives the exact nonraw callback equation; no query is resampled.

`capture_seen_zero` proves that once a publication marker precedes the raw cutoff, a clean-prefix event has zero probability under any complete stateful component interpreter. This statement retains the interpreter's full evolving state; it does not condition the remaining randomness on publication. `clean_capture` uses that fact in a structural induction to prove an exact probability equality: the event requiring a false prefix flag and a candidate predicate has the same probability as that predicate on capture after killing at the first true marker. The predicate must reject the absent candidate. `source_clean` retains the actual selected-key draw and initial shared component state in this equality.

The full flagged capture may execute more prefix queries than the killed program on already published paths. The equality is of the stated event probabilities, not of terminal interpreter states after a kill. On all preceding continuing branches, the component requests, replies and state are shared. This distinction avoids a false unconditional distributional equality and avoids any writer-conditioned tag law.

## Actual callback markers

`PrefixSource.program` recursively executes the literal original optional source handler and its existing stop monitor. After the entire callback returns, it emits `Filter.published` for the actual public reply and the source mark in the callback's initial state. Thus only an actual successful selected outer build emits true. Missing tokens, rejected native builds, ordinary builds and component refusals remain their original branches. All source operational fields and the complete analysis ghost are retained between continuing callbacks.

`program_erase` removes these private markers and recovers the original adaptive source program. Its terminal `optional` projection retains the reply and full local state on a continuing result. A refused result becomes `none`; the comparison does not claim to return that refused branch's local terminal state. Every callback and its underlying component interpreter effects have already occurred. `program_kill` proves that killing these exact markers, then flattening the extra interpreter option, yields the existing `Filter.sourceFiltered` execution. The marker is not an assumed successful-publication indicator or an extra security premise.

`client` draws the full original context and 76-byte residual in their original order before this source continuation. `client_erase` recovers the original complete CTX client after discarding its unused terminal decision. `client_kill` recovers `Dominance.actualClient` after discarding only terminal values. The established capture transformation ignores those terminal values. `program_map` additionally permits the public API journal or another pure terminal observation to be retained in the proof and projected away at capture, without changing any callback or source state.

## Concrete bound and counts

`clean_bound` combines the actual marker placement, exact clean/killed equality and the published unconditional reference bound. For the fixed source owner coordinate, it states:

```text
Pr[no selected publication before first raw, and captured decoded tag matches]
  ≤ AdvIND$(PublicationPrivacy.validation)
    + H / 2^128
    + AdvIND$(PublicationPrivacy.view)
    + 1 / 2^128.
```

The reductions remain the previously constructed unconditional reference reductions, with coefficient one at this hop. `H = entryReductionBudget + 76 = 332 + qCoin + (160 + E) Q + 64 qHash + 64 qH + G + D`, where `G`, `E` and `D` include their declared KEM/base costs. The existing source coin, accept-attempt, hash and public-HMAC caps discharge the complete context and callback work. Neither marker handling nor this equality introduces a new cryptographic assumption, selection factor or primitive endpoint.

`capture_prunes` preserves every component query before the cutoff relative to the marker-erased client, for every possible reply. `capture_no_raw` proves zero selected opening requests, including malformed first raw bytes. `capture_budget` inherits arbitrary generalized query certificates from the actual source client. `capture_bills` instantiates the total dynamic-interface allowance `H`, separate uniform/hash route allowances `H`, one selected seal, zero selected raw openings and the source-derived weighted plaintext bound `Usize.max`. Local marker and journal computation is not claimed to have zero runtime.

The ordinary reductions and real/random challenger counts are unchanged from the [capture-domination guide](server-authentication-publication-dominance.md): `B0 = H + 64 (H + 1)`, uniform allowance `B0` and seal caps two/one for validation/view, real totals `32 + B0`, and random totals `B0 + Usize.max + 32` and `B0 + Usize.max + 16`. Those are separate primitive-interface ledgers, not a replacement for global logical signing, KEM, root and chain accounting.

## Remaining accepted-event connection

The accepted-record proof must show that the actual matching raw attempt has a false publication flag when the literal owner's public journal has no successful build before the first successful finish. That consumes source owner chronology, mark persistence, first acceptance, inactive later finish behavior and the exact attempt-time history. The immutable flag must be the one recorded at the raw attempt, so later successful publication cannot retroactively change it. The ordinary authentication alternative and the existing owner-indexed Gap-DH, collision and five key-schedule losses then remain in the final bound.

No writer totality, codec injectivity, equality-based session identification, honest selected key or new reveal restriction is assumed here. Primitive implementations and the existing approved cryptographic/message contracts remain external. No Rust behavior, ProVerif query, saved-state or persistence model changes. Final global experiment and computational/symbolic correspondence work remains open.
