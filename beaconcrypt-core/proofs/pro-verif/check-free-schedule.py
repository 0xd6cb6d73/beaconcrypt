#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Run and check the free-schedule (fs) ProVerif scenarios, one query per run.

Every target is one ProVerif process with one query, run serially. The checker
requires the exact expected RESULT line or lines of the target's class, both in
the primary output and in the verification summary. It rejects "cannot be
proved", unknown or inconclusive results, unconfirmed traces, errors, and every
warning except ProVerif's termination warnings (see TERMINATION_WARNING), and
it requires exactly one reconstructed trace for every FALSE result. Classes:
security (TRUE, counted as evidence; one claim per query file, so a claim run in
several forms counts once), definitional (TRUE by construction, never
counted), witness (FALSE with a trace: the event is reachable), control (a
negative-control mutant: FALSE with a trace when the mutant breaks a claim, or
TRUE without a trace for an inverted control, whose mutant makes a witness
unreachable) and limitation (FALSE with a trace: documented expected
consequence of an owner decision). Every result is a symbolic result for a
bounded process, never a computational bound.
"""

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve().parent

CLASSES = ("security", "definitional", "witness", "control", "limitation")
TRUE_CLASSES = ("security", "definitional")

REGISTRATION = "fs-registration"
RECORDS_S2B = "fs-records-s2b"
RECORDS_B2S = "fs-records-b2s"
SCENARIOS = (REGISTRATION, RECORDS_S2B, RECORDS_B2S)

# Shared loader of every fs target, in this order, before the scenario libraries.
COMMON_LOADER = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
)

# fs-registration: the consumed-set and binding libraries, then the processes.
CONSUMED = "fs-registration-consumed.pvl"
NOCHECK = "fs-control-nocheck.pvl"
BINDING = "fs-registration-binding.pvl"
UKS = "fs-control-uks.pvl"
REGISTRATION_PROCESS = "fs-registration.pvl"
# Security results run at K_reg = 3; witnesses, controls, definitional checks and
# limitations run at the smallest bound that exhibits them.
REGISTRATION_SECURITY_BOUND = 3

# fs-records-s2b: the receive-window, finish-gate and taskings libraries, the
# receive step, the bound file with K_r receive attempts, then the process. One
# bundle per Server object; K_s = 2 and T_max = 3 with the far branch are fixed in
# the libraries. Security results run at K_r = 3; witnesses and controls run at
# the smallest K_r that exhibits them.
WINDOW = "fs-records-s2b-window.pvl"
RETAIN = "fs-control-retain.pvl"
STALE = "fs-control-stale.pvl"
FAILMUT = "fs-control-failmut.pvl"
GATE = "fs-records-s2b-gate.pvl"
NOGATE = "fs-control-nogate.pvl"
TASKINGS = "fs-records-s2b-taskings.pvl"
CHOSEN = "fs-records-s2b-taskings-chosen.pvl"
S2B_RECEIVE = "fs-records-s2b-receive.pvl"
S2B_PROCESS = "fs-records-s2b.pvl"
S2B_SECURITY_BOUND = 3
# Secrecy and the witness that the attacker reads a tasking are false by
# construction when the adversary chooses whole plaintexts, so they use the fresh
# taskings.
S2B_FRESH_ONLY = ("fs-records-s2b-s1.pv", "fs-records-s2b-s4.pv")

# fs-records-b2s: the receive-window, binding and sends libraries, the Server receive
# step, the bound file with K_r receive attempts, then the process. One bundle per
# Server object; K_s = 2 and T_max = 2 with the far branch are fixed in the libraries.
# The binding libraries are those of fs-registration, so that the record-form C-UKS
# control is the same mutant. Security results run at K_r = 3; witnesses and controls
# run at the smallest K_r that exhibits them.
B2S_WINDOW = "fs-records-b2s-window.pvl"
B2S_RETAIN = "fs-control-b2s-retain.pvl"
B2S_STALE = "fs-control-b2s-stale.pvl"
SENDS = "fs-records-b2s-sends.pvl"
SENDS_CHOSEN = "fs-records-b2s-sends-chosen.pvl"
B2S_RECEIVE = "fs-records-b2s-receive.pvl"
B2S_PROCESS = "fs-records-b2s.pvl"
B2S_SECURITY_BOUND = 3
# Record secrecy, record identity agreement and the witness that the attacker reads a
# record of a Beacon with another pin are false (or reachable) by construction when the
# adversary chooses whole Beacon plaintexts: it knows its own plaintext, and it can seal
# the plaintext it chose for an honest Beacon on a peer it registered itself. They use
# the fresh sends.
B2S_FRESH_ONLY = (
    "fs-records-b2s-s2.pv",
    "fs-records-b2s-uksr.pv",
    "fs-records-b2s-pinread.pv",
)
# E21: the reviewed finite symbolic trace argument transfers exactly the two C2/C4 formulas below from chosen-message fail-stop to failure-interleaving at K_r=3. Failed opens preserve all worker state and produce no public reply; deletion/reindexing preserves honest outputs, attacker knowledge and non-rejection events, excluding input-consumption labels. This is not an optional-result-bit/raw-plaintext or source-global equivalence. See doc/impl/proverif-failstop-trace-simulation.md.
B2S_FAILSTOP_QUERIES = ("fs-records-b2s-c2.pv", "fs-records-b2s-c4.pv")
# Every b2s query file ends with one of the two main processes (E3): the pin-free
# process, in which the attacker chooses the pinned Server key and Server ID of every
# Beacon, or the process in which every Beacon pins the honest key and ID. Every trace of
# the second is a trace of the first, so a TRUE result of the first implies the same
# query in the second, and a FALSE result of the second is one of the first. The b2s
# guide (step 13) lists which targets run in which process; a security result that runs
# only with honest pins rests, for other pins, on the simulation argument written there.
B2S_ANY_PIN = "process FsRecordsB2sMainAnyPin()"
B2S_HONEST_PIN = "process FsRecordsB2sMain()"

# Each mutant library and the real library it replaces.
MUTANTS = {
    NOCHECK: CONSUMED,
    UKS: BINDING,
    RETAIN: WINDOW,
    STALE: WINDOW,
    FAILMUT: WINDOW,
    NOGATE: GATE,
    B2S_RETAIN: B2S_WINDOW,
    B2S_STALE: B2S_WINDOW,
}

A1 = "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) ==> inj-event(FsServerCommitted(obj_1,s,b,init_1,kid,root_1,ad,p))"
A1_NON_INJECTIVE = "event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) ==> event(FsServerCommitted(obj_1,s,b,init_1,kid,root_1,ad,p))"
A2 = "event(FsServerAccepted(obj_1,s,ed_public(k),init_1,rid,root_1)) ==> event(FsBeaconStarted(s2,ed_public(k),init_1,rid)) || attacker(k)"
R1 = "event(FsServerAccepted(obj_1,s,b,i1,rid,r1))@i && event(FsServerAccepted(obj_1,s,b,i2,rid,r2))@j ==> i = j"
R1_PRIME = "event(FsServerAccepted(obj_1,s,ed_public(k),i1,rid1,r1))@i && event(FsServerAccepted(obj_1,s,ed_public(k),i2,rid2,r2))@j ==> i = j || attacker(k)"
R2 = "event(FsServerReplayRejected(obj_1,s,b,rid)) ==> event(FsServerAccepted(obj_1,s,b,init_1,rid,root_1))"
R3 = "not (event(FsServerReplayRejected(obj_1,s,ed_public(k),rid)) && event(FsBeaconStarted(s,ed_public(k),init_1,rid)))"
R4 = "event(FsBeaconStarted(s2,b,init_1,rid)) && event(FsServerAccepted(o1,s,b,i1,rid,r1))@i && event(FsServerAccepted(o2,s,b,i2,rid,r2))@j ==> i = j"
R5 = "event(FsServerAcceptFailed(obj_1,s,b,rid))@i && event(FsServerAccepted(obj_1,s,b,init_1,rid,root_1))@j ==> i > j"
S3_SERVER = "event(FsServerCommitted(obj_1,s,ed_public(k),init_1,kid,root_1,ad,p)) && attacker(root_1) ==> attacker(k)"
S3_BEACON = (
    "not (event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) && attacker(root_1))"
)
W1 = "not event(FsBeaconEstablished(s,b,init_1,fs_kid(1),root_1,ad,p))"
W2 = "not event(FsBeaconEstablished(s,b,init_1,fs_kid(2),root_1,ad,p))"
W3 = "not (event(FsServerAccepted(obj_1,s,ed_public(k),init_1,rid,root_1)) && attacker(k))"

S2B_A1 = "inj-event(FsBeaconEstablished(s,b,init_2,kid,root_2,ad,p)) ==> inj-event(FsServerCommitted(obj_2,s,b,init_2,kid,root_2,ad,p))"
S2B_A1_NON_INJECTIVE = "event(FsBeaconEstablished(s,b,init_2,kid,root_2,ad,p)) ==> event(FsServerCommitted(obj_2,s,b,init_2,kid,root_2,ad,p))"
S2B_A2 = "event(FsServerAccepted(obj_2,s,ed_public(k),init_2,rid,root_2)) ==> event(FsBeaconStarted(s2,ed_public(k),init_2,rid)) || attacker(k)"
S2B_C1 = "inj-event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m)) ==> inj-event(FsSent(server_to_beacon,s,b,kid,root_2,t,m))"
S2B_C1_NON_INJECTIVE = "event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m)) ==> event(FsSent(server_to_beacon,s,b,kid,root_2,t,m))"
S2B_C3 = "event(FsReceived(d,s,b,kid,root_2,t,m1))@i && event(FsReceived(d,s,b,kid,root_2,t,m2))@j ==> i = j"
S2B_C4 = "not event(FsFarAccepted(server_to_beacon,s,b,kid,root_2,t))"
S2B_S1 = "event(FsSent(server_to_beacon,s,ed_public(k),kid,root_2,t,m)) && attacker(m) ==> attacker(k)"
S2B_A3 = "not event(FsBeaconFinishOpenedLater(s,b,t))"
S2B_C5A = "event(FsReceived(server_to_beacon,s,b,kid,root_2,3,m3))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,2,m2))@j ==> i > j"
S2B_C5B = "event(FsReceiveRejected(server_to_beacon,s,b,kid,root_2,t,f))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m))@j ==> i > j"
S2B_C5C = "event(FsReceivedFrame(server_to_beacon,s,b,kid,root_2,t,f))@i && event(FsReceiveRejected(server_to_beacon,s,b,kid,root_2,t,f))@j ==> i > j"
S2B_S4 = "not (event(FsSent(server_to_beacon,s,b,kid,root_2,2,m)) && attacker(m))"

B2S_A1 = "inj-event(FsBeaconEstablished(ed_public(SERVER_IDENTITY_SECRET[]),b,init_2,kid,root_2,ad,p)) ==> inj-event(FsServerCommitted(obj_2,ed_public(SERVER_IDENTITY_SECRET[]),b,init_2,kid,root_2,ad,p))"
B2S_A2 = "event(FsServerAccepted(obj_2,s,ed_public(k),init_2,rid,root_2)) ==> event(FsBeaconStarted(s2,ed_public(k),init_2,rid)) || attacker(k)"
B2S_C2 = "inj-event(FsReceived(beacon_to_server,s,ed_public(k),kid,root_2,t,m)) ==> inj-event(FsSent(beacon_to_server,s,ed_public(k),kid,root_2,t,m)) || attacker(k)"
# C3 is split. Its security target fixes the direction to Beacon-to-Server, whose
# FsReceived events only the Server receive emits. The Server-to-Beacon instance, the
# Beacon's finish at sequence one, holds by construction in this scenario (one finish
# per Beacon session, a fresh identity per session, no Beacon receive window), so it is
# the definitional check C3-finish and is never counted as evidence.
B2S_C3 = "event(FsReceived(beacon_to_server,s,b,kid,root_2,t,m1))@i && event(FsReceived(beacon_to_server,s,b,kid,root_2,t,m2))@j ==> i = j"
B2S_C3_FINISH = "event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m1))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m2))@j ==> i = j"
B2S_C4 = (
    "event(FsFarAccepted(beacon_to_server,s,ed_public(k),kid,root_2,t)) ==> attacker(k)"
)
B2S_S2 = "not (event(FsSent(beacon_to_server,ed_public(SERVER_IDENTITY_SECRET[]),b,kid,root_2,t,m)) && attacker(m))"
B2S_PINREAD = "not (event(FsSent(beacon_to_server,s,b,kid,root_2,t,m)) && attacker(m))"
B2S_UKSR = "event(FsReceived(beacon_to_server,s,b1,kid1,root1,t1,m)) && event(FsSent(beacon_to_server,s,b2,kid2,root2,t2,m)) ==> b1 = b2"
B2S_C5A = "event(FsReceived(beacon_to_server,s,b,kid,root_2,2,m2))@i && event(FsReceived(beacon_to_server,s,b,kid,root_2,1,m1))@j && event(FsSent(beacon_to_server,s,b,kid,root_2,1,m1)) && event(FsSent(beacon_to_server,s,b,kid,root_2,2,m2)) ==> i > j"
B2S_C5B = "event(FsReceiveRejected(beacon_to_server,s,b,kid,root_2,t,f))@i && event(FsReceived(beacon_to_server,s,b,kid,root_2,t,m))@j && event(FsSent(beacon_to_server,s,b,kid,root_2,t,m)) ==> i > j"
B2S_C5C = "event(FsReceivedFrame(beacon_to_server,s,b,kid,root_2,t,f))@i && event(FsReceiveRejected(beacon_to_server,s,b,kid,root_2,t,f))@j && event(FsReceived(beacon_to_server,s,b,kid,root_2,t,m)) && event(FsSent(beacon_to_server,s,b,kid,root_2,t,m)) ==> i > j"
B2S_S4 = "not (event(FsReceived(beacon_to_server,s,ed_public(k),kid,root_2,t,m)) && attacker(k))"
B2S_FAR = "not (event(FsFarAccepted(beacon_to_server,s,ed_public(k),kid,root_2,t)) && attacker(k))"


@dataclass(frozen=True)
class Target:
    name: str
    scenario: str
    cls: str
    bound: int
    hooks: tuple
    query: str
    results: tuple
    inverted: bool = False
    failstop: bool = False

    def libraries(self):
        if self.scenario == REGISTRATION:
            return (
                COMMON_LOADER
                + self.hooks
                + (
                    REGISTRATION_PROCESS,
                    f"fs-registration-k{self.bound}.pvl",
                )
            )
        if self.scenario == RECORDS_S2B:
            return (
                COMMON_LOADER
                + self.hooks
                + (
                    S2B_RECEIVE,
                    f"fs-records-s2b-kr{self.bound}.pvl",
                    S2B_PROCESS,
                )
            )
        if self.scenario == RECORDS_B2S:
            form = "-failstop" if self.failstop else ""
            return (
                COMMON_LOADER
                + self.hooks
                + (
                    B2S_RECEIVE,
                    f"fs-records-b2s-kr{self.bound}{form}.pvl",
                    B2S_PROCESS,
                )
            )
        raise ValueError(f"unknown fs scenario: {self.scenario}")

    def expected_true(self):
        return self.cls in TRUE_CLASSES or self.inverted

    def expected_traces(self):
        return 0 if self.expected_true() else 1

    def bounds(self):
        if self.scenario == RECORDS_S2B:
            return f"K_reg = 1, (K_s, K_r, T_max) = (2, {self.bound}, 3)"
        if self.scenario == RECORDS_B2S:
            form = ", fail-stop" if self.failstop else ""
            return f"K_reg = 1, (K_s, K_r, T_max) = (2, {self.bound}, 2){form}"
        return f"K_reg = {self.bound}"


def registration(name, cls, bound, query, results, consumed=CONSUMED, binding=BINDING):
    return Target(
        name, REGISTRATION, cls, bound, (consumed, binding), query, tuple(results)
    )


def records_s2b(
    name,
    cls,
    bound,
    query,
    results,
    window=WINDOW,
    gate=GATE,
    taskings=TASKINGS,
    inverted=False,
):
    return Target(
        name,
        RECORDS_S2B,
        cls,
        bound,
        (window, gate, taskings),
        query,
        tuple(results),
        inverted,
    )


def records_b2s(
    name,
    cls,
    bound,
    query,
    results,
    window=B2S_WINDOW,
    binding=BINDING,
    sends=SENDS,
    failstop=False,
):
    return Target(
        name,
        RECORDS_B2S,
        cls,
        bound,
        (window, binding, sends),
        query,
        tuple(results),
        failstop=failstop,
    )


TARGETS = (
    registration("A1", "security", 3, "fs-registration-a1.pv", [A1 + " is true."]),
    registration("A2", "security", 3, "fs-registration-a2.pv", [A2 + " is true."]),
    registration("R1", "security", 3, "fs-registration-r1.pv", [R1 + " is true."]),
    registration(
        "R1'", "security", 3, "fs-registration-r1prime.pv", [R1_PRIME + " is true."]
    ),
    registration(
        "S3-server",
        "security",
        3,
        "fs-registration-s3-server.pv",
        [S3_SERVER + " is true."],
    ),
    registration(
        "S3-beacon",
        "security",
        3,
        "fs-registration-s3-beacon.pv",
        [S3_BEACON + " is true."],
    ),
    registration("R2", "definitional", 2, "fs-registration-r2.pv", [R2 + " is true."]),
    registration("R3", "witness", 2, "fs-registration-r3.pv", [R3 + " is false."]),
    registration("R5", "witness", 2, "fs-registration-r5.pv", [R5 + " is false."]),
    registration("W1", "witness", 1, "fs-registration-w1.pv", [W1 + " is false."]),
    registration("W2", "witness", 2, "fs-registration-w2.pv", [W2 + " is false."]),
    registration("W3", "witness", 1, "fs-registration-w3.pv", [W3 + " is false."]),
    registration("R4", "limitation", 1, "fs-registration-r4.pv", [R4 + " is false."]),
    registration(
        "C-NOCHECK",
        "control",
        2,
        "fs-registration-r1.pv",
        [R1 + " is false."],
        consumed=NOCHECK,
    ),
    registration(
        "C-UKS",
        "control",
        1,
        "fs-registration-a1.pv",
        [A1 + " is false.", "(even " + A1_NON_INJECTIVE + " is false.)"],
        binding=UKS,
    ),
    records_s2b(
        "s2b-A1",
        "security",
        3,
        "fs-records-s2b-a1.pv",
        [S2B_A1 + " is true."],
        taskings=CHOSEN,
    ),
    records_s2b(
        "s2b-A2",
        "security",
        3,
        "fs-records-s2b-a2.pv",
        [S2B_A2 + " is true."],
        taskings=CHOSEN,
    ),
    records_s2b(
        "s2b-C1",
        "security",
        3,
        "fs-records-s2b-c1.pv",
        [S2B_C1 + " is true."],
        taskings=CHOSEN,
    ),
    records_s2b(
        "s2b-C3",
        "security",
        3,
        "fs-records-s2b-c3.pv",
        [S2B_C3 + " is true."],
        taskings=CHOSEN,
    ),
    records_s2b(
        "s2b-C4",
        "security",
        3,
        "fs-records-s2b-c4.pv",
        [S2B_C4 + " is true."],
        taskings=CHOSEN,
    ),
    records_s2b(
        "s2b-S1", "security", 3, "fs-records-s2b-s1.pv", [S2B_S1 + " is true."]
    ),
    records_s2b(
        "s2b-A3", "witness", 1, "fs-records-s2b-a3.pv", [S2B_A3 + " is false."]
    ),
    records_s2b(
        "s2b-C5a", "witness", 2, "fs-records-s2b-c5a.pv", [S2B_C5A + " is false."]
    ),
    records_s2b(
        "s2b-C5b", "witness", 2, "fs-records-s2b-c5b.pv", [S2B_C5B + " is false."]
    ),
    records_s2b(
        "s2b-C5c", "witness", 1, "fs-records-s2b-c5c.pv", [S2B_C5C + " is false."]
    ),
    records_s2b(
        "s2b-S4", "witness", 1, "fs-records-s2b-s4.pv", [S2B_S4 + " is false."]
    ),
    records_s2b(
        "s2b-C-RETAIN-C1",
        "control",
        3,
        "fs-records-s2b-c1.pv",
        [S2B_C1 + " is false.", "(but " + S2B_C1_NON_INJECTIVE + " is true.)"],
        window=RETAIN,
    ),
    records_s2b(
        "s2b-C-RETAIN-C3",
        "control",
        3,
        "fs-records-s2b-c3.pv",
        [S2B_C3 + " is false."],
        window=RETAIN,
    ),
    records_s2b(
        "s2b-C-NOGATE",
        "control",
        1,
        "fs-records-s2b-a1.pv",
        [S2B_A1 + " is false.", "(even " + S2B_A1_NON_INJECTIVE + " is false.)"],
        gate=NOGATE,
    ),
    records_s2b(
        "s2b-C-STALE",
        "control",
        3,
        "fs-records-s2b-c3.pv",
        [S2B_C3 + " is false."],
        window=STALE,
    ),
    records_s2b(
        "s2b-C-FAILMUT",
        "control",
        2,
        "fs-records-s2b-c5b.pv",
        [S2B_C5B + " is true."],
        window=FAILMUT,
        inverted=True,
    ),
    records_b2s(
        "b2s-A1",
        "security",
        3,
        "fs-records-b2s-a1.pv",
        [B2S_A1 + " is true."],
        sends=SENDS_CHOSEN,
    ),
    records_b2s(
        "b2s-A2",
        "security",
        3,
        "fs-records-b2s-a2.pv",
        [B2S_A2 + " is true."],
        sends=SENDS_CHOSEN,
    ),
    records_b2s(
        "b2s-C2", "security", 3, "fs-records-b2s-c2.pv", [B2S_C2 + " is true."]
    ),
    records_b2s(
        "b2s-C2-chosen-fs",
        "security",
        3,
        "fs-records-b2s-c2.pv",
        [B2S_C2 + " is true."],
        sends=SENDS_CHOSEN,
        failstop=True,
    ),
    records_b2s(
        "b2s-C3",
        "security",
        3,
        "fs-records-b2s-c3.pv",
        [B2S_C3 + " is true."],
        sends=SENDS_CHOSEN,
    ),
    records_b2s(
        "b2s-C4",
        "security",
        3,
        "fs-records-b2s-c4.pv",
        [B2S_C4 + " is true."],
        sends=SENDS_CHOSEN,
        failstop=True,
    ),
    records_b2s(
        "b2s-S2", "security", 3, "fs-records-b2s-s2.pv", [B2S_S2 + " is true."]
    ),
    records_b2s(
        "b2s-UKSr", "security", 3, "fs-records-b2s-uksr.pv", [B2S_UKSR + " is true."]
    ),
    records_b2s(
        "b2s-C3-finish",
        "definitional",
        1,
        "fs-records-b2s-c3-finish.pv",
        [B2S_C3_FINISH + " is true."],
        sends=SENDS_CHOSEN,
    ),
    records_b2s(
        "b2s-C5a", "witness", 2, "fs-records-b2s-c5a.pv", [B2S_C5A + " is false."]
    ),
    records_b2s(
        "b2s-C5b", "witness", 2, "fs-records-b2s-c5b.pv", [B2S_C5B + " is false."]
    ),
    records_b2s(
        "b2s-C5c", "witness", 2, "fs-records-b2s-c5c.pv", [B2S_C5C + " is false."]
    ),
    records_b2s(
        "b2s-S4", "witness", 1, "fs-records-b2s-s4.pv", [B2S_S4 + " is false."]
    ),
    records_b2s(
        "b2s-FAR", "witness", 1, "fs-records-b2s-far.pv", [B2S_FAR + " is false."]
    ),
    records_b2s(
        "b2s-PINREAD",
        "witness",
        1,
        "fs-records-b2s-pinread.pv",
        [B2S_PINREAD + " is false."],
    ),
    records_b2s(
        "b2s-C-UKS",
        "control",
        1,
        "fs-records-b2s-uksr.pv",
        [B2S_UKSR + " is false."],
        binding=UKS,
    ),
    records_b2s(
        "b2s-C-RETAIN",
        "control",
        3,
        "fs-records-b2s-c3.pv",
        [B2S_C3 + " is false."],
        window=B2S_RETAIN,
    ),
    records_b2s(
        "b2s-C-STALE",
        "control",
        3,
        "fs-records-b2s-c3.pv",
        [B2S_C3 + " is false."],
        window=B2S_STALE,
    ),
)

FORBIDDEN = (
    "cannot be proved",
    "is unknown",
    "is inconclusive",
    "I could not confirm",
)

# ProVerif 2.05 starts every error line with "Error: " and every input, simplification
# and lemma warning line with "Warning: "; the checker rejects both, and any other line
# that mentions a warning. The one exception is the termination warning of the
# resolution selection function (selfun.ml), which comes in two forms, both accepted
# here and both fed by test-free-schedule-checker.py: "Termination warning: " followed
# by a clause and "Selecting <n>", or "Termination warning: Selecting an hypothesis
# matching the conclusion." followed by a suggested noselect declaration. ProVerif
# prints them when the only hypotheses it can select in a clause are ones that a nounif
# declaration (the reviewed heuristic nx, or one that ProVerif adds itself) marks as
# best avoided or that match the clause's conclusion, so that saturation might not
# terminate. The selection function only decides the order of resolution and is not an
# assumption: such a line concerns whether saturation ends, not the meaning of a verdict
# that ProVerif reports after saturation ended. A run whose saturation does not end hits
# the timeout or the address-space cap and fails. These lines are therefore accepted, in
# any number and for any target.
TERMINATION_WARNING = "Termination warning: "


def log_name(target):
    """The log file of one target; R1' and R1 must not share a log."""
    stem = re.sub(r"[^A-Za-z0-9]+", "-", target.name.replace("'", "prime"))
    return stem.strip("-") + ".log"


# The real and mutant hook libraries each scenario accepts, position by position.
HOOKS = {
    REGISTRATION: ((CONSUMED, NOCHECK), (BINDING, UKS)),
    RECORDS_S2B: ((WINDOW, RETAIN, STALE, FAILMUT), (GATE, NOGATE), (TASKINGS, CHOSEN)),
    RECORDS_B2S: (
        (B2S_WINDOW, B2S_RETAIN, B2S_STALE),
        (BINDING, UKS),
        (SENDS, SENDS_CHOSEN),
    ),
}


def validate_scenario(target):
    """Check the scenario-specific bound and hook libraries of one target."""
    if target.scenario not in SCENARIOS:
        raise ValueError(f"{target.name}: unknown fs scenario {target.scenario}")
    allowed = HOOKS[target.scenario]
    if len(target.hooks) != len(allowed) or any(
        hook not in choices for hook, choices in zip(target.hooks, allowed)
    ):
        raise ValueError(f"{target.name}: unknown scenario library")
    if target.failstop and target.scenario != RECORDS_B2S:
        raise ValueError(f"{target.name}: only fs-records-b2s has a fail-stop form")
    if target.scenario == REGISTRATION:
        if target.bound not in (1, 2, 3):
            raise ValueError(f"{target.name}: unsupported bound {target.bound}")
        if target.cls == "security" and target.bound != REGISTRATION_SECURITY_BOUND:
            raise ValueError(f"{target.name}: security results run at K_reg = 3")
    elif target.scenario == RECORDS_S2B:
        if target.bound not in (1, 2, 3):
            raise ValueError(f"{target.name}: unsupported bound {target.bound}")
        if target.cls == "security" and target.bound != S2B_SECURITY_BOUND:
            raise ValueError(f"{target.name}: security results run at K_r = 3")
        if target.query in S2B_FRESH_ONLY and target.hooks[2] != TASKINGS:
            raise ValueError(
                f"{target.name}: adversary-chosen plaintexts make this query false by construction"
            )
    else:
        if target.bound not in (1, 2, 3):
            raise ValueError(f"{target.name}: unsupported bound {target.bound}")
        if target.cls == "security" and target.bound != B2S_SECURITY_BOUND:
            raise ValueError(f"{target.name}: b2s security results run at K_r = 3")
        if target.query in B2S_FRESH_ONLY and target.hooks[2] != SENDS:
            raise ValueError(
                f"{target.name}: adversary-chosen plaintexts make this query false by construction"
            )
        if target.failstop and (
            target.cls != "security"
            or target.bound != B2S_SECURITY_BOUND
            or target.hooks[2] != SENDS_CHOSEN
            or target.query not in B2S_FAILSTOP_QUERIES
        ):
            raise ValueError(
                f"{target.name}: the fail-stop form only extends a listed security result "
                "to adversary-chosen plaintexts"
            )


def uncommented(text):
    """ProVerif text without its (* ... *) comments, whitespace normalised."""
    return " ".join(re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S).split())


def b2s_pins(text):
    """The main process a b2s query file runs: "any" (pin-free) or "honest"."""
    body = " " + uncommented(text)
    if body.count(" process ") == 1:
        if body.endswith(" " + B2S_ANY_PIN):
            return "any"
        if body.endswith(" " + B2S_HONEST_PIN):
            return "honest"
    raise ValueError("a b2s query file must end with one of the two main processes")


def validate_legacy_scope(directory=HERE):
    """Preserve the explicit projection boundary when renewing source tripwires."""
    marker = (
        "(* @beaconcrypt-fidelity-v1 legacy_profiles.scope="
        "classical_projection:MLDSA_guards_not_globally_lifted *)"
    )
    if (directory / "production-transcript-interface.pvl").read_text().count(
        marker
    ) != 1:
        raise ValueError(
            "legacy profiles require the reviewed classical-projection scope"
        )


def validate_targets(targets=TARGETS, directory=HERE):
    """Check the manifest itself: classes, bounds, libraries and query files."""
    validate_legacy_scope(directory)
    names = [target.name for target in targets]
    if len(set(names)) != len(names):
        raise ValueError("duplicate fs target name")
    if len({log_name(target) for target in targets}) != len(targets):
        raise ValueError("two fs targets share a log file")
    used_queries = {scenario: set() for scenario in SCENARIOS}
    for target in targets:
        if target.cls not in CLASSES:
            raise ValueError(f"{target.name}: unknown class {target.cls}")
        validate_scenario(target)
        mutants = [hook for hook in target.hooks if hook in MUTANTS]
        if len(mutants) != (1 if target.cls == "control" else 0):
            raise ValueError(
                f"{target.name}: a control loads exactly one mutant, others none"
            )
        if target.inverted and target.cls != "control":
            raise ValueError(f"{target.name}: only a control can be inverted")
        if not target.results:
            raise ValueError(f"{target.name}: no expected result")
        verdict = " is true." if target.expected_true() else " is false."
        if not target.results[0].endswith(verdict):
            raise ValueError(f"{target.name}: result polarity does not match its class")
        for line in target.results:
            if any(word in line for word in FORBIDDEN):
                raise ValueError(
                    f"{target.name}: an inconclusive result is never expected"
                )
        for library in target.libraries():
            if not (directory / library).is_file():
                raise ValueError(f"{target.name}: missing library {library}")
        if not (directory / target.query).is_file():
            raise ValueError(f"{target.name}: missing query file {target.query}")
        if (
            target.failstop
            and "FsReceiveRejected" in (directory / target.query).read_text()
        ):
            raise ValueError(
                f"{target.name}: a fail-stop target cannot mention FsReceiveRejected"
            )
        if not target.query.startswith(target.scenario + "-"):
            raise ValueError(f"{target.name}: query file of another scenario")
        if target.scenario == RECORDS_B2S:
            try:
                b2s_pins((directory / target.query).read_text())
            except ValueError as error:
                raise ValueError(f"{target.name}: {error}") from error
        used_queries[target.scenario].add(target.query)
    for scenario in SCENARIOS:
        present = {path.name for path in directory.glob(f"{scenario}-*.pv")}
        used = used_queries[scenario]
        if present != used:
            raise ValueError(
                f"fs query files and targets differ: unused={sorted(present - used)} "
                f"missing={sorted(used - present)}"
            )


def check_output(output, target):
    """Require exactly the expected results of one single-query run."""
    for word in FORBIDDEN:
        if word in output:
            raise ValueError(f"{target.name}: ProVerif output contains '{word}'")
    if re.search(r"^(Error|Warning)", output, re.M):
        raise ValueError(f"{target.name}: ProVerif reported an error or warning")
    for line in output.splitlines():
        if "warning" in line.lower() and not line.startswith(TERMINATION_WARNING):
            raise ValueError(
                f"{target.name}: ProVerif reported a warning: {line[:120]}"
            )
    if output.count("Verification summary:") != 1:
        raise ValueError(f"{target.name}: missing or duplicated verification summary")
    primary, summary = output.split("Verification summary:")
    results = re.findall(r"^RESULT (.+)$", primary, re.M)
    reported = re.findall(r"^Query (.+)$", summary, re.M)
    if results != list(target.results) or reported != [target.results[0]]:
        raise ValueError(
            f"{target.name}: exact query/verdict mismatch\nexpected={list(target.results)!r}\n"
            f"primary={results!r}\nsummary={reported!r}"
        )
    if primary.count("A trace has been found.") != target.expected_traces():
        raise ValueError(f"{target.name}: reconstructed trace count changed")


def command(proverif, target, directory=HERE):
    arguments = [proverif]
    for library in target.libraries():
        arguments.extend(["-lib", str(directory / library)])
    arguments.append(str(directory / target.query))
    return arguments


def run_process(arguments, log_path, timeout, address_space_kib):
    """Run one process; return (seconds, peak RSS in KiB, exit code, timed out)."""

    def limit():
        if address_space_kib:
            bytes_limit = address_space_kib * 1024
            resource.setrlimit(resource.RLIMIT_AS, (bytes_limit, bytes_limit))

    timed_out = threading.Event()
    start = time.monotonic()
    with open(log_path, "w") as log:
        process = subprocess.Popen(
            arguments, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limit
        )

        def expire():
            timed_out.set()
            process.kill()

        timer = threading.Timer(timeout, expire)
        timer.start()
        try:
            _, status, usage = os.wait4(process.pid, 0)
        finally:
            timer.cancel()
    seconds = time.monotonic() - start
    process.returncode = os.waitstatus_to_exitcode(status)
    return seconds, usage.ru_maxrss, process.returncode, timed_out.is_set()


def check_target(proverif, target, logdir, timeout, address_space_kib):
    log_path = logdir / log_name(target)
    seconds, peak, returncode, timed_out = run_process(
        command(proverif, target), log_path, timeout, address_space_kib
    )
    if timed_out:
        raise ValueError(f"{target.name}: timeout after {timeout} s ({log_path})")
    if returncode:
        raise ValueError(f"{target.name}: ProVerif exited {returncode} ({log_path})")
    try:
        check_output(log_path.read_text(), target)
    except ValueError as error:
        raise ValueError(f"{error} ({log_path})") from error
    return seconds, peak


def security_claims(targets):
    """The distinct security claims among targets: one per scenario and query file.

    A claim run in several forms has one query file and several security targets (in
    fs-records-b2s, C2 runs with fresh records in the failure-interleaving receive and
    with adversary-chosen records in the fail-stop receive); it counts once.
    """
    return {
        (target.scenario, target.query)
        for target in targets
        if target.cls == "security"
    }


def run(proverif, targets, logdir, timeout, address_space_kib, results_path):
    validate_targets()
    rows = []
    failures = []
    for target in targets:
        try:
            seconds, peak = check_target(
                proverif, target, logdir, timeout, address_space_kib
            )
        except ValueError as error:
            failures.append(str(error))
            print(f"FAILED {target.name}: {error}", flush=True)
            continue
        verdict = "TRUE" if target.expected_true() else "FALSE"
        rows.append((target, verdict, seconds, peak))
        print(
            f"{target.name}: {target.cls}, {target.bounds()}: {verdict} as expected "
            f"in {seconds:.2f} s, peak RSS {peak} KiB",
            flush=True,
        )
    if results_path:
        with open(results_path, "w") as output:
            output.write(
                "target\tscenario\tclass\tbound\tverdict\tseconds\tpeak_rss_kib\n"
            )
            for target, verdict, seconds, peak in rows:
                output.write(
                    f"{target.name}\t{target.scenario}\t{target.cls}\t{target.bounds()}\t"
                    f"{verdict}\t{seconds:.2f}\t{peak}\n"
                )
    if failures:
        raise SystemExit("fs ProVerif check failed:\n" + "\n".join(failures))
    total = sum(row[2] for row in rows)
    checked = [row[0] for row in rows]
    security = sum(1 for target in checked if target.cls == "security")
    claims = len(security_claims(checked))
    print(
        f"fs ProVerif targets: {len(rows)} exact results in {total:.1f} s of serial ProVerif "
        f"time; counted as evidence: {security} security targets, {claims} distinct security "
        "claims (one per query file; a claim run in several forms counts once); symbolic and "
        "bounded, not computational bounds."
    )


def run_logged(
    proverif, targets, log_dir, timeout, address_space_kib, results_path, scratch=None
):
    """Run with logs in log_dir, or in a temporary directory that is removed only on success.

    Every failure message names the log of the failing target, so a failed run keeps its
    temporary directory and says where it is.
    """
    if log_dir:
        log_dir.mkdir(parents=True, exist_ok=True)
        run(proverif, targets, log_dir, timeout, address_space_kib, results_path)
        return
    directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-fs-logs-", dir=scratch))
    try:
        run(proverif, targets, directory, timeout, address_space_kib, results_path)
    except BaseException:
        print(f"fs ProVerif logs kept in {directory}", file=sys.stderr, flush=True)
        raise
    shutil.rmtree(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per target")
    parser.add_argument(
        "--address-space-kib",
        type=int,
        default=0,
        help="address-space cap per ProVerif run in KiB, as for ulimit -v (0: none)",
    )
    parser.add_argument(
        "--log-dir",
        type=Path,
        help="keep every ProVerif log here (default: a temporary directory, kept on failure)",
    )
    parser.add_argument("--results", type=Path, help="write a TSV of times and peaks")
    parser.add_argument(
        "--scenario",
        choices=SCENARIOS,
        help="run only the targets of this scenario (default: every scenario)",
    )
    parser.add_argument(
        "--only", action="append", default=[], help="run only this target"
    )
    parser.add_argument("--list", action="store_true", help="list the targets and exit")
    args = parser.parse_args()
    validate_targets()
    targets = tuple(
        target
        for target in TARGETS
        if args.scenario is None or target.scenario == args.scenario
    )
    if args.list:
        for target in targets:
            libraries = " ".join(target.libraries()[len(COMMON_LOADER) :])
            print(
                f"{target.name}\t{target.cls}\t{target.bounds()}\t{target.query}\t{libraries}"
            )
        return
    if args.only:
        unknown = set(args.only) - {target.name for target in targets}
        if unknown:
            parser.error(f"unknown target: {sorted(unknown)}")
        targets = tuple(target for target in targets if target.name in args.only)
    run_logged(
        args.proverif,
        targets,
        args.log_dir,
        args.timeout,
        args.address_space_kib,
        args.results,
    )


if __name__ == "__main__":
    sys.exit(main())
