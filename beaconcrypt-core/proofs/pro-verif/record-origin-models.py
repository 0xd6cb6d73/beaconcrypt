#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Pin the reviewed selected near-record projection and local replay premises.

This is a finite syntax/transition audit. Source-event and knowledge reflection,
T0 root occurrence uniqueness and arbitrary trace induction are paper arguments.
"""

import importlib.util
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "record_origin_retained", HERE / "delayed-response-models.py"
)
RETAINED = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(RETAINED)
tokens = RETAINED.tokens
once = RETAINED.once


def registration(source):
    result = once(
        source,
        "event A1Root(bitstring).",
        "event A1Root(bitstring).\nevent L2SelectedIdentity(bitstring).",
    )
    result = once(
        result,
        "let A1Accept(leak_initial:bool)",
        "let A1Accept(selected_identity:bitstring,leak_initial:bool)",
    )
    result = once(
        result,
        "(if leak_initial then out(c,server_to_beacon_chain(root))) |",
        "(if leak_initial then out(c,beacon_to_server_chain(root))) |\n   (if identity <> selected_identity then out(c,root)) |",
    )
    result = once(
        result,
        "out(c,(ratchet_next(server_to_beacon_chain(root)),beacon_to_server_chain(root)));",
        "out(c,(ratchet_next(server_to_beacon_chain(root)),ratchet_next(ratchet_next(beacon_to_server_chain(root)))));",
    )
    result = once(
        result,
        "out(c,a1_reply(build_call,a1_some(response)))",
        "out(c,a1_reply(build_call,a1_some(response)));\n   L2Recv1(builder,ed_public(SERVER_IDENTITY_SECRET),identity,assigned,root,ad,ratchet_material(beacon_to_server_chain(root)),ratchet_material(ratchet_next(beacon_to_server_chain(root))),ratchet_next(ratchet_next(beacon_to_server_chain(root))),0,false)",
    )
    result = once(
        result,
        "letfun A1Finish(server_identity: bitstring,",
        "letfun A1Finish(server_key_id:key_id, server_identity: bitstring,",
    )
    result = once(
        result,
        "if frame_sender = SERVER_KEY_ID then",
        "if frame_sender = server_key_id then",
    )
    result = once(
        result,
        "let A1Beacon() =",
        "let A1Beacon(beacon_identity_secret:bitstring,beacon_prekey_secret:bitstring,beacon_pq_secret:bitstring,beacon_one_time_secret:bitstring) =",
    )
    for name in (
        "beacon_identity_secret",
        "beacon_prekey_secret",
        "beacon_pq_secret",
        "beacon_one_time_secret",
    ):
        result = once(result, f"  new {name}: bitstring;\n", "")
    result = once(
        result,
        "  let server_identity = ed_public(SERVER_IDENTITY_SECRET) in",
        "  in(c,(server_identity:bitstring,server_key_id:key_id));",
    )
    result = once(
        result,
        "= A1Finish(server_identity,",
        "= A1Finish(server_key_id,server_identity,",
    )
    result = once(
        result,
        "out(c, a1_reply(finish_call, a1_some(application_payload)))",
        "out(c, a1_reply(finish_call, a1_some(application_payload)));\n    L2Send1(server_identity,beacon_identity,assigned_key_id,root,associated_data,beacon_to_server_chain(root))",
    )
    result = result[: result.index("let A1Main(")] + """let L2Main(leak_initial:bool)=
 out(c,ed_public(SERVER_IDENTITY_SECRET));
 new selected_identity_secret:bitstring;
 event L2SelectedIdentity(selected_identity_secret);
 new selected_prekey_secret:bitstring;
 new selected_pq_secret:bitstring;
 new selected_onetime_secret:bitstring;
 (A1Accept(ed_public(selected_identity_secret),leak_initial) |
 A1Beacon(selected_identity_secret,selected_prekey_secret,selected_pq_secret,selected_onetime_secret)).
"""
    return result.replace(" [precise]", "")


def precise_inputs(source, expected):
    count = 0
    lines = []
    for line in source.splitlines(keepends=True):
        if re.match(r"\s*!?in\(c,", line):
            if not line.rstrip().endswith(";") or "[precise]" in line:
                raise ValueError("changed host-input annotation anchor")
            line = line.rstrip()[:-1] + " [precise];\n"
            count += 1
        lines.append(line)
    if count != expected:
        raise ValueError("changed exact host-input annotation count")
    return "".join(lines)


def cache_receiver(source):
    source = once(
        source,
        "event L2Published(direction,bitstring,bitstring,key_id,bitstring,nat,bitstring).",
        "event L2Published(direction,bitstring,bitstring,key_id,bitstring,nat,bitstring).\nevent L2CachedAccepted(bitstring,bitstring,key_id,bitstring,bitstring).",
    )
    anchor = "if t=1 && cached then (let plaintext=open_frame(m1,ad,fs_seq(1),kid,frame) in ("
    return once(
        source, anchor, anchor + "\n event L2CachedAccepted(s,b,kid,root,plaintext);"
    )


def local_transition(r, cached, target, valid_frame, opening_succeeds):
    """The reviewed finite control abstraction; plaintext/opening is uninterpreted."""
    if not valid_frame:
        return r, cached, False
    if target <= r:
        if target == 1 and cached and opening_succeeds:
            return r, False, True
        return r, cached, False
    if target == 1 and opening_succeeds:
        return 1, cached, True
    if target == 2 and opening_succeeds:
        return 2, True if r == 0 else cached, True
    return r, cached, False


def replay_cases():
    """Check the exact four-state invariant for every relevant guard class."""
    remaining = {(0, False): {1, 2}, (1, False): {2}, (2, True): {1}, (2, False): set()}
    count = 0
    for entry, available in remaining.items():
        for target in (0, 1, 2, 3):
            for valid_frame in (False, True):
                for opening_succeeds in (False, True):
                    r, cached, accepted = local_transition(
                        *entry, target, valid_frame, opening_succeeds
                    )
                    after = (r, cached)
                    if after not in remaining:
                        raise ValueError("near receive leaves the four-state invariant")
                    expected = available - {target} if accepted else available
                    if accepted and target not in available:
                        raise ValueError("near receive accepts a consumed target")
                    if remaining[after] != expected:
                        raise ValueError(
                            "near receive does not remove exactly its accepted target"
                        )
                    if not accepted and after != entry:
                        raise ValueError("failed receive changes entry state")
                    count += 1
    return count


def validate(directory=HERE):
    original = (directory / "delayed-response.pvl").read_text()
    actual = (directory / "record-origin.pvl").read_text()
    if tokens(actual) != tokens(registration(original)):
        raise ValueError(
            "record origin differs from exact retained registration transformation"
        )
    bound = (directory / "record-origin-kr3.pvl").read_text()
    expected = "expand L2_RECV_STEP(L2Recv3,L2RecvStop). expand L2_RECV_STEP(L2Recv2,L2Recv3). expand L2_RECV_STEP(L2Recv1,L2Recv2)."
    if tokens(bound) != tokens(expected):
        raise ValueError("record origin must retain all three receive attempts")
    control = (directory / "record-origin-leak-control.pv").read_text()
    query = (directory / "record-origin-auth.pv").read_text()
    if tokens(control) != tokens(
        once(query, "process L2Main(false)", "process L2Main(true)")
    ):
        raise ValueError(
            "chain leak control differs beyond the single disclosure switch"
        )
    for filename, count in (
        ("record-origin.pvl", 5),
        ("record-origin-sends.pvl", 2),
        ("record-origin-receive.pvl", 1),
    ):
        content = (directory / filename).read_text()
        if filename == "record-origin-receive.pvl":
            content = cache_receiver(content)
        expected = precise_inputs(content, count)
        derivative = filename.replace("record-origin", "record-origin-cache", 1)
        if tokens((directory / derivative).read_text()) != tokens(expected):
            raise ValueError(
                "cache witness differs beyond ghost event and host-input annotations: "
                + filename
            )
    kr2 = (
        "expand L2_RECV_STEP(L2Recv2,L2RecvStop). expand L2_RECV_STEP(L2Recv1,L2Recv2)."
    )
    if tokens((directory / "record-origin-kr2.pvl").read_text()) != tokens(kr2):
        raise ValueError("cache witness must preserve exact two-slot prefix")
    if replay_cases() != 64:
        raise ValueError("incomplete local replay guard classes")
