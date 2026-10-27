#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the exact retained Beacon finish and binding-removal derivative.

This syntax comparator checks the stated local transformation. The finite
source-event/knowledge projection is the separate reviewed paper argument.
"""

import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def tokens(text):
    pattern = r'"(?:\\.|[^"\\])*"|\(\*.*?\*\)|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|==>|<=>|<>|<=|>=|&&|\|\||<-|->|[^\s]'
    return tuple(
        match[0]
        for match in re.finditer(pattern, text, re.S)
        if not match[0].startswith("(*")
    )


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(
            "changed unique delayed-response transformation anchor: " + old
        )
    return text.replace(old, new, 1)


def retained_beacon(source):
    source = source[source.index("let FsBeacon() =") :]
    prefix, finish = source.split("  in(c, response: bitstring) [precise];\n")
    finish = finish[: finish.index("  event FsBeaconEstablished(")]
    helper = (
        "letfun A1Finish(server_identity: bitstring, beacon_identity: bitstring, "
        "beacon_prekey_secret: bitstring, beacon_identity_secret: bitstring, "
        "beacon_one_time_secret: bitstring, beacon_pq_secret: bitstring, "
        "response: bitstring) =\n"
        + finish
        + "  (assigned_key_id, root, associated_data, application_payload).\n\n"
    )
    prefix = once(prefix, "let FsBeacon() =", "let A1Beacon() =")
    marker = "  event FsBeaconStarted(server_identity, beacon_identity, init, registration_id);"
    prefix = once(
        prefix,
        marker,
        "  out(c, a1_public(beacon_identity, beacon_prekey, beacon_one_time, beacon_pq));\n"
        "  in(c, start_call: bitstring) [precise];\n" + marker,
    )
    return (
        helper
        + prefix
        + """  in(c, (finish_call: bitstring, response: bitstring)) [precise];
  let (assigned_key_id: key_id, root: bitstring, associated_data: bitstring, application_payload: bitstring) = A1Finish(server_identity, beacon_identity, beacon_prekey_secret, beacon_identity_secret, beacon_one_time_secret, beacon_pq_secret, response) in (
    event A1Root(root);
    event FsBeaconEstablished(server_identity, beacon_identity, init, assigned_key_id, root, associated_data, application_payload);
    out(c, a1_reply(finish_call, a1_some(application_payload)))
  ) else out(c, a1_reply(finish_call, a1_none())).
"""
    )


def without_binding(source):
    result = source.replace("A1Finish(", "A1WrongFinish(")
    result = result.replace("A1Beacon()", "A1WrongBeacon()")
    result = result.replace("A1Main(", "A1WrongMain(")
    start = result.index(
        "  if binding = beaconcrypt_core__pqxdh__RegistrationKeyIdBinding("
    )
    end = result.index("  (* The adapter pin checks", start)
    guard = result[start:end]
    if tokens(guard) != tokens(
        "if binding = beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(assigned_key_id)) then"
    ):
        raise ValueError("binding control would remove more than the exact guard")
    return result[:start] + result[end:]


def validate(directory=HERE):
    source = (directory / "fs-registration.pvl").read_text()
    model = (directory / "delayed-response.pvl").read_text()
    role = model[model.index("letfun A1Finish(") : model.index("let A1Main(")]
    if tokens(role) != tokens(retained_beacon(source)):
        raise ValueError(
            "delayed-response Beacon/finish differs from exact retained role transformation"
        )
    control = (directory / "delayed-response-wrong-binding.pvl").read_text()
    if tokens(control) != tokens(without_binding(model)):
        raise ValueError(
            "binding control differs outside the single guard and injective role renaming"
        )
    query = (directory / "fs-registration-a1.pv").read_text()
    expected = once(query, "process FsRegistrationMain()", "process A1Main(false)")
    if tokens((directory / "delayed-response-a1.pv").read_text()) != tokens(expected):
        raise ValueError("delayed response must retain the full original A1 formula")
