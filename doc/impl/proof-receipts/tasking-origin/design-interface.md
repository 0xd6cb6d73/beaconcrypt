# Exact-ID Server-to-Beacon near-origin design

Status: proposed source projection from central `fa1a174e72dfb2f33ff97a9a0a9f1654b5c93418`; not a proved result. This reverses the retained direction of L2 but requires its own process proof and source/knowledge argument. No existing model, theorem or verdict is changed.

## Target statement and chronological state

Select one fresh Beacon identity `kB`, retaining its prekey, one-time and KEM secrets and source generation order, and the modeled independent honest Server identity `kS`. The selected Beacon may take any pin, but the origin query targets only successful receives with exact Server signing identity `ed_public(kS)`. It does not authenticate an attacker-owned pin as that protected Server. The intended ordinary query is:

```text
event(S2bSelectedIdentity(kB)) &&
event(FsReceived(server_to_beacon(),ed_public(kS),ed_public(kB),assigned,root,t,m))
==> event(S2bPublished(server_to_beacon(),ed_public(kS),ed_public(kB),assigned,root,t,m)).
```

Only post-registration positions two and three emit this new receive event. Sequence one was already accepted by the exact one-active-finish registration operation, with its actual Server own-ID check, binding prefix and assigned ID. Thus the later worker starts at `(r,cached2)=(1,false)`, with materials at literal s2b positions two and three. Its successful transitions are `(1,false)--2-->(2,false)`, `(1,false)--3-->(3,true)`, `(2,false)--3-->(3,false)`, and `(3,true)--2-->(3,false)`. Every failure retains the entire entry pair, fixed identities, actual IDs, root and associated data; every attempted call consumes a receive slot. The final security profile retains three receive attempts, two post-registration send allocations and the first-far-success cutoff.

The public frame sender in this direction is the actual Server own ID, checked against the Beacon's stored expected Server ID. The query's assigned ID is the Beacon's authenticated peer assignment. These are different fields and remain different through seal/open calls and events. No later assigned-ID equality or global peer-routing injectivity is inferred.

## Registration, sends and observed outputs

Reuse the reviewed A1 candidate verification, source root helper, delayed one-use pending build and single active finish. Successful build both publishes the response and installs a Server send worker for its exact `(server identity, beacon identity, server own ID, assigned ID, root, AD)` tuple. The chosen builder is permitted to differ from the accepting object when the source's same-identity/same-own-ID checks permit the move. Distinct dynamic accepts keep distinct private continuations even when public labels repeat.

The send worker permits arbitrary chosen plaintext or independent fresh application bytes at each allocation. Preserve failed seal advancement: allocation consumes its position and advances its chain even if the optional seal result fails; only an actual successful frame return emits `S2bPublished`. It must use the current builder's own sender ID and selected peer's AD. Source requests before establishment, missing peers, empty inputs or exhausted send windows return their actual public failure observation; they do not create a publication event.

After the exact finish, the selected Beacon has a later receive worker with a public call label and raw frame input. Successful open returns exactly the plaintext produced by `open_frame` on the original adversarial frame. Parser, wrong-route, old-target, commitment and AEAD failures return None and preserve the complete entry receive state. No secretly recovered plaintext is inserted into an adversary-supplied target. Source malformed-byte details remain under the existing abstract-message contract, while adapter argument/provenance and scheduling are checked at this boundary.

## Stronger observations and source recipes

For each successful honest Server accept, disclose the exact initial b2s chain and the exact s2b chain after consuming positions one, two and three, namely `ratchet_next(ratchet_next(ratchet_next(server_to_beacon_chain(root))))`. Keep the s2b initial chain and materials one through three private. Disclose a full root only when the accepted exact Ed signing identity differs from the selected Beacon identity. These are explicit stronger-adversary observations to be proved safe in the process; they are not production APIs or a claim that swapping direction labels proves separation.

For the selected partnered root, the disclosed initial b2s chain supplies every omitted opposite-direction record material, ciphertext construction and optional opening result through actual public recipes. Prior to eliminating an opposite-direction step, its exact root/chain provenance still needs a proof: a successful selected finish with the protected Server pin must identify an actual successful source build/root. The previously proved A1 initial-origin statement is a candidate lemma, but its applicability to added tasking/receive outputs must be justified, not assumed. Its stronger s2b-chain-two disclosure makes later s2b material publicly computable; the new model discloses only chain four. Independent private application bytes may be named in the source ledger, but no secret-dependent message or fictitious publication may be manufactured.

Before first far success, actual far targets in this direction lie in the finite envelope four through fifty-four. Given the publicly disclosed literal chain four, the exact future material is the public recipe `ratchet_material(ratchet_next^(t-4)(chain4))`. A claim-specific near projection may evaluate the original frame's actual opening, reproduce its optional plaintext/None observation from that recipe, retain failure poststate, and cut at first far success. This must preserve every near input, reply and event ordering. It is not the older hidden-reply L3 deletion. Every omitted source attempt, derivation, parser call and primitive operation remains in the common query/work bill.

The source identity selection must reuse A2's exact signing-key occurrence classification, including caller-known compound keys, fresh hidden imports and the absence of Server signing outputs. Protect protocol-mandated Ed/X joint-use exactly in T0. Any use of the separate A2 arbitrary-peer DH service belongs only to the identity-knowledge proof; it must never be smuggled into the C1 comparison. Public-key conversion equality is not equality of signing identities.

## Uniqueness and controls

First attempt ordinary origin in the unchanged three-slot process, retaining the full tuple. Injectivity may then follow from a separately reviewed same-process occurrence argument: one active finish installs only one selected Beacon receiver and each successful transition removes its accepted near target. Unlike b2s, the selected Beacon's single-finish lifecycle may make equal-root-to-accept constructor injectivity unnecessary for this local uniqueness lemma; verify that no second selected worker or alternate finish event exists before using that simplification.

The negative control discloses the selected s2b chain at position two and reruns exactly the ordinary-origin formula. A selected honest cache witness should receive position three followed by cached position two. If its cheapest witness bound is two, only a checked third-input-unscheduled prefix embedding may transfer reachability to the three-slot security process. No unknown or timeout is accepted as a control.

## Secrecy observation boundary

This public actual-plaintext interface is suitable for origin but does not satisfy unrestricted legacy `attacker(m)` message secrecy. Delivering a genuine target ciphertext returns its plaintext by design. That fact is not a production vulnerability. Legacy S1/S2 keep the trusted application's plaintext private, while a public decryption experiment must state target-opening/release freshness for exact tuples, raw aliases, replay and cache paths.

Existing computational components do not silently resolve that choice. `RawCtxSelectedMessageFreshness.fresh_factor` handles byte-valued chain/key disclosures, including cross-owner aliases; it is not a no-target-plaintext-release predicate. `AdaptiveCtxPrivacyGuard.publicReply` and `recordReply` use successful seal history with the originally submitted plaintext, and `guard_run_complete` retains the complete adaptive replay comparison; that endpoint's caller already supplied its plaintext and does not establish secrecy of a fresh hidden application payload. Any later challenge-message adaptation must consume the existing primitive IND$ interface and expose its exact release policy, without adding a protocol-authentication assumption. This milestone proposes origin only; no new message-secrecy claim follows from opposite-direction state separation.
