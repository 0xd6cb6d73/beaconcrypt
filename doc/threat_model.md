<!-- SPDX-License-Identifier: 0BSD -->

# Adversary
# Power
The adversary for a C2 protocol is assumed to be able to do the following:
- Read and log everything that goes over the open internet
- Have full access to external provider infrastructure

Notably, this means that the adversary can read TLS plaintexts if the protocol is terminated within the provider's boundary.

## Goal
The adversary is assumed to have two goals:
- Access sensitive information from beacon output
- Send arbitrary commands to legitimate beacons

This assumes that the C2 protocol used doesn't use broadcast to send taskings, and that those are only sent to the beacon for which they are relevant.

## Modality
The adversaries has two modes, active or passive. An active adversary means they will attempt to send or modify existing messages to any principal in our protocol. This includes MitM-style attacks. A passive adversary will only listen.

This threat model assumes that the adversary will not attempt to compromise the C2 server or the beacon itself and that it has no access to the environment in which either of these are running. In other words, the attacker only exists on the wire.

# C2 protocol
## Principals
Our protocol has two principals:
- The server, a standard central CS-style teamserver that issues taskings and stores responses
- The beacon, a piece of software running on compromised machines which receives taskings from the server and sends responses back to it

The means of communications between these principals is unspecified and can be either public or private, but it is assumed to happen over the open-internet.

## Goals
Our protocol aims to provide a confidential and integrity-protected way for the server to send its taskings to the beacons. It must be computationally infeasible for attackers to substitute their tasking with a legitimate one. The beacon must be able to verify that the received taskings are legitimate and to send a response with the same guarantees.
