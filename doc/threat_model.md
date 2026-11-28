<!-- SPDX-License-Identifier: 0BSD -->

# Adversary
# Power
The adversary for a C2 protocol is assumed to be able to do the following:
- Read and log everything that goes over the open internet
- Have full access to external provider infrastructure

Notably, this means that the adversary can read TLS plaintexts if the protocol is terminated within the provider's boundary.

This is intentionally a fairly maximalist definition, but it is useful to capture e.g. a corrupt, disgruntled or coerced insider at a service provider.

## Goal
The adversary is assumed to have two goals:
- Access sensitive information from beacon output
- Send arbitrary commands to legitimate beacons

Exfiltrated data secrecy and tasking integrity are, in my eyes, existential aspects of a useful C2 infrastructure. See Tim MalcomVetter’s [Responsible Red Teams](https://malcomvetter.medium.com/responsible-red-teams-1c6209fd43cc) medium post.

The attacker may register arbitrary malicious beacons and controls all key material for those beacons. Init contains three attached Ed25519 signatures under the Beacon identity and no Beacon ML-DSA credential or protected Beacon ML-DSA signing oracle. This does not authorize an attacker-owned registration to receive another beacon's tasking. The C2 application must send each tasking only to its intended session. The current symbolic profile checks honest-session isolation while requiring valid responses and a recoverable routed canary for attacker-owned registrations; it does not verify the surrounding application's recipient-selection policy. Server response origin relies on the pinned Server ML-DSA-65 public key and the retained mandatory response signature. Beacon authentication is Ed25519-only; removing the Beacon ML-DSA credential does not provide post-quantum Beacon authentication.

## Availability and open registration
Availability is not a protocol goal, but the library's resource use under this adversary is bounded only by the embedding application. Registration is open: each registration that a malicious beacon completes adds an established peer to the server, and each accepted registration adds a 64-byte replay marker. Markers are permanent, because removing one would let a recorded Init be replayed. Peers can be retired with `retire_peer`, which erases the ratchet, keeps the marker, and never reassigns the key ID. Snapshot owners can also set a runtime peer limit, and row owners can keep a quota in an application row inside the registration transaction. Neither replaces admission control: applications that accept registrations from the internet must rate-limit them before calling the library. Snapshot owners re-encode the complete server state on every commit, so their per-message cost grows linearly with the number of peers and markers. The row API keeps per-operation cost constant.

Two properties are deliberate and constrain applications:
- `finish_registration` is single-shot. Any failure aborts the pending Beacon, including a failure caused by one injected unauthenticated message ahead of the genuine response. The server has already consumed that registration, so the application must construct a new Beacon, with new keys, to register again.
- Each direction of a session tolerates at most 50 frames that are never delivered over its lifetime. A skipped key leaves the receive cache only when its frame arrives, so after 50 permanent losses only strictly in-order traffic is accepted, and the next lost frame makes every later frame in that direction unacceptable until a lost one is delivered. Long-lived sessions over lossy transports should retransmit or re-register.

## Modality
The adversaries has two modes, active or passive. An active adversary means they will attempt to send or modify existing messages to any principal in our protocol. This includes MitM-style attacks. A passive adversary will only listen.

This threat model assumes that the adversary will not compromise the C2 server
or a legitimate beacon and has no access to either execution environment. Its
control of a separately registered malicious beacon is explicit above; against
legitimate principals, the attacker exists only on the wire.

*This is obviously unreasonable*, an active PQ attacker is highly likely state-sponsored, at least in the short to medium term. Such an attacker almost certainly does not mind RCEing your C2. However, I think this limitation is required to bound analysis to those aspects that beaconcrypt itself can address. The rest is up to C2 developpers.

It is also assumed that the attacker does not modify the staged beacons at rest or in transit. That is, the compiled-in Server Ed25519 key, ML-DSA-65 key and numeric identity-key ID must retain their authentic values. Replacing the trusted Server pins with attacker-controlled values can defeat registration authentication. This, too, is unreasonable, yet in my mind required. Indeed, I don't see how this issue can be resolved as even something like a key transparency log can be subverted by this kind of attacker. This is a massive assumption, and all but forces the hypothetical beaconcrypt user to host their C2 and staging infrastructure in a manner which only breaks TLS on-premises.

# C2 protocol
## Principals
Our protocol has two principals:
- The server, a standard central CS-style teamserver that issues taskings and stores responses
- The beacon, a piece of software running on compromised machines which receives taskings from the server and sends responses back to it

The means of communications between these principals is unspecified and can be either public or private, but it is assumed to happen over the open-internet.

## Goals
Our protocol aims to provide a confidential and integrity-protected way for the server to send its taskings to the beacons. It must be computationally infeasible for attackers to substitute their tasking with a legitimate one. The beacon must be able to verify that the received taskings are legitimate and to send a response with the same guarantees.
