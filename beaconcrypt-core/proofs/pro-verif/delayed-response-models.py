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


COUNTERFACTUAL_ASSIGNED = "delayed_counterfactual_ad_omitted_assigned_id"
COUNTERFACTUAL_LIBRARY = "delayed-response-wrong-binding-ad-omits-assigned-id.pvl"
# The positive half of the same counterfactual: the binding check present.
COUNTERFACTUAL_BINDING_LIBRARY = "delayed-response-ad-omits-assigned-id.pvl"
COUNTERFACTUAL_LIBRARIES = (COUNTERFACTUAL_LIBRARY, COUNTERFACTUAL_BINDING_LIBRARY)


def ad_omits_assigned_id(source):
    """Counterfactual control only (never a production profile).

    Registration version 3 binds the response assigned ID twice: as the LE64
    last field of the transcript inside AD151 and as the authenticated
    eight-byte payload prefix. In the binding-removed control the relabeled
    response is already rejected by AEAD/CTX opening under AD151. This replaces
    only the assigned-ID transcript field of the two AD151 derivations (the
    pending Server build and the Beacon finish) by one fixed public constant,
    so the control again isolates the removed binding check. It is applied to
    both delayed-response-wrong-binding.pvl (binding check removed: the original
    trace returns) and delayed-response.pvl (binding check present: A1 stays
    true), so the pair shows that the binding check alone blocks the trace.
    """
    if COUNTERFACTUAL_ASSIGNED in source:
        raise ValueError("counterfactual constant already present")
    result = once(
        source,
        "ed_public(SERVER_IDENTITY_SECRET),ephemeral,ciphertext,assigned) in",
        f"ed_public(SERVER_IDENTITY_SECRET),ephemeral,ciphertext,{COUNTERFACTUAL_ASSIGNED}) in",
    )
    result = once(
        result,
        "    response_server_identity, server_ephemeral, kem_ciphertext, assigned_key_id\n  ) in",
        f"    response_server_identity, server_ephemeral, kem_ciphertext, {COUNTERFACTUAL_ASSIGNED}\n  ) in",
    )
    if result.count("fs_associated_data(") != 2:
        raise ValueError("expected exactly two delayed-response AD derivations")
    header = "(* SPDX-License-Identifier: 0BSD *)\n"
    if not result.startswith(header):
        raise ValueError("delayed-response control header changed")
    return (
        header
        + "(* Counterfactual control only: the transcript AD omits the assigned ID. *)\n"
        + f"const {COUNTERFACTUAL_ASSIGNED}: key_id.\n"
        + result[len(header) :]
    )


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
    for source in (control, model):
        derived = ad_omits_assigned_id(source)
        if tokens(derived).count(COUNTERFACTUAL_ASSIGNED) != 3:
            raise ValueError(
                "assigned-ID counterfactual changed more than the two AD fields"
            )
    if tokens(without_binding(ad_omits_assigned_id(model))) != tokens(
        ad_omits_assigned_id(control)
    ):
        raise ValueError(
            "the two assigned-ID counterfactuals differ beyond the binding check"
        )
