#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Maintain the exact trusted-application observation and fresh-publication delta.

The finite comparison pins complete process tokens. The target-name preserving
source induction remains a separately reviewed paper, not a new primitive premise.
"""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "application_record_models", HERE / "record-origin-models.py"
)
RECORD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECORD)
tokens = RECORD.tokens
once = RECORD.once
PROFILES = {
    "b2s": ("record-origin", "L2", "l2", "beacon_to_server", 1),
    "s2b": ("tasking-origin", "S2b", "s2b", "server_to_beacon", 2),
}


def registration(source, direction):
    result = once(
        source,
        "raw:bitstring,accept_call:bitstring));",
        "raw:bitstring,accept_call:bitstring)) [precise];",
    )
    if direction == "b2s":
        result = once(
            result,
            "build_call:bitstring, fail_build:bool));",
            "build_call:bitstring, fail_build:bool)) [precise];",
        )
    return result


def receive(source, direction):
    _, event, low, _, _ = PROFILES[direction]
    anchor = low + "_some(plaintext)"
    if source.count(anchor) != 3:
        raise ValueError("successful receive reply roster changed")
    result = source.replace(anchor, low + "_some(" + low + "_received())")
    decl = f"fun {low}_none():bitstring [data]."
    return once(
        result,
        decl,
        decl
        + f"\nfun {low}_received():bitstring [data].\nevent {event}FreshPublished(direction,bitstring,bitstring,key_id,bitstring,nat,bitstring).",
    )


def sends(source, direction, leak=False):
    _, event, _, label, first = PROFILES[direction]
    chunks = source.split("new fresh[]:bitstring;")
    if len(chunks) != 3:
        raise ValueError("fresh send branch roster changed")
    for index in (1, 2):
        sequence = first + 2 - index
        anchor = f"event {event}Published({label}(),s,b,kid,root,{sequence},plaintext);"
        extra = f" event {event}FreshPublished({label}(),s,b,kid,root,{sequence},plaintext);"
        if leak:
            extra += " out(c,plaintext);"
        chunks[index] = once(chunks[index], anchor, anchor + extra)
    restriction = (
        "new fresh:bitstring;" if direction == "b2s" else "new fresh[]:bitstring;"
    )
    return restriction.join(chunks)


def query(direction):
    _, event, _, label, _ = PROFILES[direction]
    return f"""query k:bitstring,kid:key_id,root:bitstring,t:nat,m:bitstring;
 event({event}FreshPublished({label}(),ed_public(SERVER_IDENTITY_SECRET),ed_public(k),kid,root,t,m)) && event({event}SelectedIdentity(k)) && attacker(m).
process {event}Main(false)
"""


def validate(directory=HERE):
    for direction, (old, _, _, _, _) in PROFILES.items():
        prefix = "application-secrecy-" + direction
        for suffix, transform in [
            ("", registration),
            ("-receive", receive),
            ("-sends", sends),
        ]:
            expected = transform(
                (directory / (old + suffix + ".pvl")).read_text(), direction
            )
            if tokens((directory / (prefix + suffix + ".pvl")).read_text()) != tokens(
                expected
            ):
                raise ValueError(
                    "application observation/process delta changed: "
                    + direction
                    + suffix
                )
        expected = sends(
            (directory / (old + "-sends.pvl")).read_text(), direction, True
        )
        if tokens((directory / (prefix + "-leak-sends.pvl")).read_text()) != tokens(
            expected
        ):
            raise ValueError("plaintext leak control delta changed: " + direction)
        for suffix in ["", "-leak"]:
            if tokens((directory / (prefix + suffix + ".pv")).read_text()) != tokens(
                query(direction)
            ):
                raise ValueError(
                    "exact selected fresh-publication query changed: "
                    + direction
                    + suffix
                )
