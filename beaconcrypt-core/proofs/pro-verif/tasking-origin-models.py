#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Maintain the reviewed reverse-direction source projection and local replay cases.

Whole-process transformations and finite branch checks maintain the paper premises.
They do not mechanize source-event/knowledge induction or a computational reduction.
"""

import importlib.util
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "tasking_record_models", HERE / "record-origin-models.py"
)
RECORD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECORD)
tokens = RECORD.tokens
once = RECORD.once


def rename(source):
    return source.replace("L2", "S2b").replace("l2_", "s2b_")


def registration(source):
    result = rename(source)
    result = once(
        result,
        "S2bRecv1(builder,ed_public(SERVER_IDENTITY_SECRET),identity,assigned,root,ad,ratchet_material(beacon_to_server_chain(root)),ratchet_material(ratchet_next(beacon_to_server_chain(root))),ratchet_next(ratchet_next(beacon_to_server_chain(root))),0,false)",
        "S2bSend2(builder,ed_public(SERVER_IDENTITY_SECRET),identity,accepted_id,assigned,root,ad,ratchet_next(server_to_beacon_chain(root)))",
    )
    result = once(
        result,
        "if leak_initial then out(c,beacon_to_server_chain(root))",
        "if leak_initial then out(c,ratchet_next(server_to_beacon_chain(root)))",
    )
    result = once(
        result,
        "out(c,(ratchet_next(server_to_beacon_chain(root)),ratchet_next(ratchet_next(beacon_to_server_chain(root)))))",
        "out(c,(beacon_to_server_chain(root),ratchet_next(ratchet_next(ratchet_next(server_to_beacon_chain(root))))))",
    )
    result = once(
        result,
        "in(c,(server_identity:bitstring,server_key_id:key_id));",
        "in(c,(beacon_owner:bitstring,server_identity:bitstring,server_key_id:key_id));",
    )
    result = once(
        result,
        "S2bSend1(server_identity,beacon_identity,assigned_key_id,root,associated_data,beacon_to_server_chain(root))",
        "S2bRecv1(beacon_owner,server_identity,beacon_identity,server_key_id,assigned_key_id,root,associated_data,ratchet_material(ratchet_next(server_to_beacon_chain(root))),ratchet_material(ratchet_next(ratchet_next(server_to_beacon_chain(root)))),ratchet_next(ratchet_next(ratchet_next(server_to_beacon_chain(root)))),1,false)",
    )
    return once(
        result,
        "build_call:bitstring, fail_build:bool));",
        "build_call:bitstring, fail_build:bool)) [precise];",
    )


def receive(source):
    result = rename(source).replace("beacon_to_server()", "server_to_beacon()")
    result = once(
        result,
        "fun s2b_send(bitstring,bool,bitstring,bool)",
        "fun s2b_send(bitstring,bitstring,bool,bitstring,bool)",
    )
    result = result.replace(
        "b:bitstring,kid:key_id", "b:bitstring,sender:key_id,kid:key_id"
    )
    result = result.replace("Next(owner,s,b,kid,", "Next(owner,s,b,sender,kid,")
    result = once(result, "fs_seq(t:nat),=kid)", "fs_seq(t:nat),=sender)")
    result = result.replace(",kid,frame)", ",sender,frame)")
    result = re.sub(r"\b[012]\b", lambda match: str(int(match.group()) + 1), result)
    return once(result, "cached:bool)=1.", "cached:bool)=0.")


def sends(source):
    result = rename(source).replace("beacon_to_server()", "server_to_beacon()")
    result = result.replace(
        "s:bitstring,b:bitstring,kid:key_id",
        "owner:bitstring,s:bitstring,b:bitstring,sender:key_id,kid:key_id",
    )
    result = result.replace("s2b_send(call:", "s2b_send(=owner,call:")
    result = result.replace("S2bSend2(s,b,kid,", "S2bSend2(owner,s,b,sender,kid,")
    result = result.replace(",kid,plaintext)", ",sender,plaintext)")
    result = re.sub(r"\b[12]\b", lambda match: str(int(match.group()) + 1), result)
    return result.replace("S2bSend2", "S2bSend3").replace("S2bSend1", "S2bSend2")


def cache_receiver(source):
    result = once(
        source,
        "event S2bPublished(direction,bitstring,bitstring,key_id,bitstring,nat,bitstring).",
        "event S2bPublished(direction,bitstring,bitstring,key_id,bitstring,nat,bitstring).\nevent S2bCachedAccepted(bitstring,bitstring,key_id,bitstring,bitstring).",
    )
    anchor = "if t=2 && cached then (let plaintext=open_frame(m1,ad,fs_seq(2),sender,frame) in ("
    return once(
        result, anchor, anchor + "\n event S2bCachedAccepted(s,b,kid,root,plaintext);"
    )


def local_transition(r, cached, target, valid_frame, opening_succeeds):
    if not valid_frame:
        return r, cached, False
    if target <= r:
        if target == 2 and cached and opening_succeeds:
            return r, False, True
        return r, cached, False
    if target == 2 and opening_succeeds:
        return 2, cached, True
    if target == 3 and opening_succeeds:
        return 3, True if r == 1 else cached, True
    return r, cached, False


def replay_cases():
    remaining = {(1, False): {2, 3}, (2, False): {3}, (3, True): {2}, (3, False): set()}
    count = 0
    for entry, available in remaining.items():
        for target in (0, 1, 2, 3, 4):
            for valid in (False, True):
                for opened in (False, True):
                    r, cached, accepted = local_transition(
                        *entry, target, valid, opened
                    )
                    after = r, cached
                    if after not in remaining:
                        raise ValueError(
                            "tasking receiver leaves its four-state invariant"
                        )
                    if accepted and target not in available:
                        raise ValueError("tasking receiver accepts a consumed target")
                    if remaining[after] != (
                        available - {target} if accepted else available
                    ):
                        raise ValueError("tasking receiver removes the wrong target")
                    if not accepted and after != entry:
                        raise ValueError("tasking rejection changes entry state")
                    count += 1
    return count


def validate(directory=HERE):
    for suffix, transform in (
        ("", registration),
        ("-receive", receive),
        ("-sends", sends),
    ):
        expected = transform(
            (directory / ("record-origin" + suffix + ".pvl")).read_text()
        )
        actual = (directory / ("tasking-origin" + suffix + ".pvl")).read_text()
        if tokens(actual) != tokens(expected):
            raise ValueError("tasking source transformation changed: " + suffix)
        ghost = cache_receiver(actual) if suffix == "-receive" else actual
        if tokens(
            (directory / ("tasking-origin-cache" + suffix + ".pvl")).read_text()
        ) != tokens(ghost):
            raise ValueError(
                "tasking cache witness changes more than its one ghost event: " + suffix
            )
    for bound in (2, 3):
        expected = " ".join(
            f"expand S2b_RECV_STEP(S2bRecv{i},"
            + (f"S2bRecv{i+1}" if i < bound else "S2bRecvStop")
            + ")."
            for i in range(bound, 0, -1)
        )
        if tokens((directory / f"tasking-origin-kr{bound}.pvl").read_text()) != tokens(
            expected
        ):
            raise ValueError("tasking receive bound or continuation changed")
    source = (directory / "tasking-origin-auth.pv").read_text()
    control = (directory / "tasking-origin-leak-control.pv").read_text()
    if tokens(control) != tokens(
        once(source, "process S2bMain(false)", "process S2bMain(true)")
    ):
        raise ValueError(
            "tasking control changes the origin query or process beyond disclosure"
        )
    if replay_cases() != 80:
        raise ValueError("incomplete tasking guard partition")
