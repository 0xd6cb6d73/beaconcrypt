#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Pin the complete Kr3 challenge, reply and public-host interface transforms.

Paired source/context simulation and the exact-T0 occurrence arguments remain
separately reviewed paper proofs. This comparator does not prove those claims.
"""

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "exact_strong_application_models", HERE / "application-secrecy-models.py"
)
APPLICATION = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(APPLICATION)
tokens = APPLICATION.tokens
once = APPLICATION.once
PROFILES = APPLICATION.PROFILES


def replace_count(source, old, new, count):
    if source.count(old) != count:
        raise ValueError("exact-interface strong transform anchor changed: " + old)
    return source.replace(old, new)


def kem_names(source):
    for name in ["ephemeral_secret", "kem_coins"]:
        source = once(source, f"new {name}: bitstring;", f"new {name}[]: bitstring;")
    return source


def registration(source, direction, auxiliary=False):
    if not auxiliary:
        source = replace_count(source, " [precise]", "", 2)
    if direction == "s2b":
        source = once(
            source,
            "ciphertext: bitstring, root: bitstring) =",
            "ciphertext: bitstring, root: bitstring, selected_identity:bitstring) =",
        )
        source = once(
            source,
            "A1Pending(token,accepted_id,verified,identity,ephemeral,ciphertext,root)",
            "A1Pending(token,accepted_id,verified,identity,ephemeral,ciphertext,root,selected_identity)",
        )
        call = "S2bSend2(builder,ed_public(SERVER_IDENTITY_SECRET),identity,accepted_id,assigned,root,ad,ratchet_next(server_to_beacon_chain(root)))"
        source = once(source, call, call[:-1] + ",selected_identity)")
    return source


def response_events(source):
    source = once(
        source,
        "event A1Root(bitstring).",
        "event A1Root(bitstring).\nevent ExactStrongBuiltResponse(bitstring,bitstring,bitstring,bitstring).\nevent ExactStrongFinishedResponse(bitstring,bitstring,bitstring,bitstring).",
    )
    source = once(
        source,
        "   out(c,a1_reply(build_call,a1_some(response)));",
        "   event ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET),identity,response,root);\n   out(c,a1_reply(build_call,a1_some(response)));",
    )
    return once(
        source,
        "    out(c, a1_reply(finish_call, a1_some(application_payload)));",
        "    event ExactStrongFinishedResponse(server_identity,beacon_identity,response,root);\n    out(c, a1_reply(finish_call, a1_some(application_payload)));",
    )


def receive(source, direction, auxiliary=False, control=False):
    _, _, low, _, _ = PROFILES[direction]
    arguments = (
        "bitstring,bool,bitstring,bool"
        if direction == "b2s"
        else "bitstring,bitstring,bool,bitstring,bool"
    )
    declaration = f"fun {low}_send({arguments}):bitstring [data]."
    source = once(
        source,
        declaration,
        declaration.replace("bool,bitstring,bool", "bool,bitstring,bitstring,bool"),
    )
    if auxiliary:
        source = once(
            source,
            f"in(c,{low}_receive(=owner,call:bitstring,frame:bitstring));",
            f"in(c,{low}_receive(=owner,call:bitstring,frame:bitstring)) [precise];",
        )
    if control:
        source += "\nevent ExactStrongProbe(bool,bitstring).\n"
    return source


def sends(source, direction, kind="equivalence"):
    _, event, low, label, first = PROFILES[direction]
    source = replace_count(
        source,
        "use_chosen:bool,chosen:bitstring,fail_seal:bool",
        "use_chosen:bool,left:bitstring,right:bitstring,fail_seal:bool",
        2,
    )
    source = replace_count(
        source, "let plaintext=chosen in", "let plaintext=left in", 2
    )
    source = replace_count(
        source, "fail_seal:bool));", "fail_seal:bool)) [precise];", 2
    )
    fresh = "new fresh:bitstring;" if direction == "b2s" else "new fresh[]:bitstring;"
    fresh += " let plaintext=fresh in"
    eligibility = (
        "s=ed_public(SERVER_IDENTITY_SECRET)"
        if direction == "b2s"
        else "b=selected_identity"
    )
    if kind in ["leak", "ungated"]:
        condition = (
            "true" if kind == "ungated" else f"if {eligibility} then true else false"
        )
        replacement = f"new test_secret:bitstring; let eligible={condition} in let plaintext=if eligible then test_secret else left in"
    else:
        payload = "left" if kind == "origin" else "choice[left,right]"
        replacement = f"let plaintext=if {eligibility} then {payload} else left in"
    source = replace_count(source, fresh, replacement, 2)
    if direction == "s2b":
        source = replace_count(
            source,
            "chain:bitstring)=",
            "chain:bitstring,selected_identity:bitstring)=",
            2,
        )
        source = replace_count(
            source,
            "S2bSend3(owner,s,b,sender,kid,root,ad,ratchet_next(chain))",
            "S2bSend3(owner,s,b,sender,kid,root,ad,ratchet_next(chain),selected_identity)",
            4,
        )
    if kind in ["leak", "ungated"]:
        for sequence in [first, first + 1]:
            marker = f"event {event}FreshPublished({label}(),s,b,kid,root,{sequence},plaintext);"
            extra = " event ExactStrongProbe(eligible,plaintext);"
            if kind == "leak":
                extra += " out(c,plaintext);"
            source = once(source, marker, marker + extra)
    return source


def query(direction, kind):
    _, event, _, _, _ = PROFILES[direction]
    if kind == "equivalence":
        body = "nounif x:bitstring,y:bitstring; attacker(choice[x25519_public(x),x25519_public(y)]).\nset simplifyProcess = false.\n"
    elif kind == "origin":
        body = f"""query k:bitstring,response:bitstring,root:bitstring;
 event(ExactStrongFinishedResponse(ed_public(SERVER_IDENTITY_SECRET),ed_public(k),response,root)) && event({event}SelectedIdentity(k))
 ==> event(ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET),ed_public(k),response,root)).
"""
    else:
        body = "query m:bitstring; event(ExactStrongProbe(true,m)) && attacker(m).\n"
    return body + f"process {event}Main(false)\n"


def expected_files(directory=HERE):
    files = {
        "exact-interface-strong-registration.pvl": kem_names(
            (directory / "registration-set-admission.pvl").read_text()
        )
    }
    for direction in PROFILES:
        old = "application-secrecy-" + direction
        prefix = "exact-interface-strong-" + direction
        base = (directory / (old + ".pvl")).read_text()
        receiver = (directory / (old + "-receive.pvl")).read_text()
        sender = (directory / (old + "-sends.pvl")).read_text()
        files[prefix + ".pvl"] = registration(base, direction)
        files[prefix + "-auxiliary.pvl"] = registration(base, direction, True)
        files[prefix + "-origin.pvl"] = response_events(
            registration(base, direction, True)
        )
        files[prefix + "-receive.pvl"] = receive(receiver, direction)
        files[prefix + "-origin-receive.pvl"] = receive(receiver, direction, True)
        files[prefix + "-control-receive.pvl"] = receive(
            receiver, direction, True, True
        )
        for kind in ["equivalence", "origin", "leak", "ungated"]:
            suffix = "" if kind == "equivalence" else "-" + kind
            files[prefix + suffix + "-sends.pvl"] = sends(sender, direction, kind)
            files[prefix + suffix + ".pv"] = query(direction, kind)
    return files


def validate(directory=HERE):
    for name, expected in expected_files(directory).items():
        if tokens((directory / name).read_text()) != tokens(expected):
            raise ValueError(
                "exact-interface strong complete process delta changed: " + name
            )
