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

This assumes that the C2 protocol used doesn't broadcast taskings, and that those are only sent to the beacon for which they are relevant. This means that a  maliciously-registered beacon cannot learn potentially sensitive information from taskings.

## Modality
The adversaries has two modes, active or passive. An active adversary means they will attempt to send or modify existing messages to any principal in our protocol. This includes MitM-style attacks. A passive adversary will only listen.

This threat model assumes that the adversary will not attempt to compromise the C2 server or the beacon itself and that it has no access to the environment in which either of these are running. In other words, the attacker only exists on the wire.

*This is obviously unreasonable*, an active PQ attacker is highly likely state-sponsored, at least in the short to medium term. Such an attacker almost certainly does not mind RCEing your C2. However, I think this limitation is required to bound analysis to those aspects that beaconcrypt itself can address. The rest is up to C2 developpers.

It is also assumed that the attacker does not modify the staged beacons at rest or in transit. That is, the attacker cannot replaced the compiled-in server public key with its own. Indeed, doing so allows the attacker to MitM the beacon's registration and completely breaks any security properties. This, too, is unreasonable, yet in my mind required. Indeed, I don't see how this issue can be resolved as even something like a key transparency log can be subverted by this kind of attacker. This is a massive assumption, and all but forces the hypothetical beaconcrypt user to host their C2 and staging infrastructure in a manner which only breaks TLS on-premises.

# C2 protocol
## Principals
Our protocol has two principals:
- The server, a standard central CS-style teamserver that issues taskings and stores responses
- The beacon, a piece of software running on compromised machines which receives taskings from the server and sends responses back to it

The means of communications between these principals is unspecified and can be either public or private, but it is assumed to happen over the open-internet.

## Goals
Our protocol aims to provide a confidential and integrity-protected way for the server to send its taskings to the beacons. It must be computationally infeasible for attackers to substitute their tasking with a legitimate one. The beacon must be able to verify that the received taskings are legitimate and to send a response with the same guarantees.
