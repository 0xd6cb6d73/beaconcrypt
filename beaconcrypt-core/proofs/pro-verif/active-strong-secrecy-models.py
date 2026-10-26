#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reviewed token derivatives for the active strong-secrecy models.

These pure functions compute expected process text. They do not write models or
run ProVerif. The checker compares maintained, reviewable files to this text.
Unchanged source slices retain exact operations and generator order. The added
interface is chosen-plaintext testing and public optional-result bits only.
"""

import hashlib
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def token_digest(text):
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    return hashlib.sha256(" ".join(text.split()).encode()).hexdigest()


def label_calls(generated, direction):
    """Caller labels are experiment metadata; input bytes stay unchanged."""
    for filename, argument in (
        (f"{direction}.pvl", "response"),
        ("receive.pvl", "frame"),
    ):
        text = generated[filename]
        old = f"in(c, {argument}: bitstring) [precise];"
        require(text.count(old) == 1, "raw call input anchor changed")
        text = text.replace(
            old, f"in(c, (call_label: bitstring, {argument}: bitstring)) [precise];"
        )
        text = re.sub(
            r"fs_strong_reply\(\s*" + argument + r"\s*,\s*",
            f"fs_strong_reply(call_label, {argument}, ",
            text,
        )
        generated[filename] = text


def derive_b2s(directory):
    generated = {}

    def code(name):
        return re.sub(r"\(\*.*?\*\)", "", (directory / name).read_text(), flags=re.S)

    s = code("fs-records-b2s.pvl")
    beacon = s.index("let FsB2sBeacon(")
    receive = s.index("  in(c, response: bitstring) [precise];", beacon)
    a = s.index("  let kex_response(", receive)
    b = s.index("  event FsBeaconEstablished(", a)
    end = s.index("\nlet FsRecordsB2sMain()", b)
    pure = s[a:b]
    returned = "fs_strong_finished(assigned_key_id, root, associated_data, send_chain_1, send_chain_2, application_payload, finish_plaintext, initial_frame).\n\n"
    helper = (
        "fun fs_strong_finished(key_id, bitstring, bitstring, bitstring, bitstring, bitstring, bitstring, bitstring): bitstring [data].\nfun fs_strong_reply(bitstring, bool): bitstring [data].\nletfun fs_strong_finish(server_identity: bitstring, server_key_id: key_id, beacon_identity: bitstring,\n  beacon_prekey_secret: bitstring, beacon_identity_secret: bitstring, beacon_one_time_secret: bitstring,\n  beacon_pq_secret: bitstring, response: bitstring) =\n"
        + pure
        + returned
    )
    continuation = s[b:end].rstrip()
    if not continuation.endswith(")."):
        raise ValueError("Strong-secrecy source transformation anchor changed")
    continuation = continuation[:-1]
    new = (
        "  let fs_strong_finished(assigned_key_id: key_id, root: bitstring, associated_data: bitstring,\n    send_chain_1: bitstring, send_chain_2: bitstring, application_payload: bitstring,\n    finish_plaintext: bitstring, initial_frame: bitstring) =\n    fs_strong_finish(server_identity, server_key_id, beacon_identity, beacon_prekey_secret,\n      beacon_identity_secret, beacon_one_time_secret, beacon_pq_secret, response) in (\n  out(c, fs_strong_reply(response, true));\n"
        + continuation
        + "\n  ) else out(c, fs_strong_reply(response, false)).\n"
    )
    generated["b2s.pvl"] = helper + s[:a] + new + s[end:]
    s = code("fs-records-b2s-sends.pvl")
    for i in (1, 2):
        require(
            s.count(f"new record_{i}[]: bitstring;") == 1,
            "send challenge anchor changed",
        )
        s = s.replace(
            f"new record_{i}[]: bitstring;",
            f"in(c, (left_{i}: bitstring, right_{i}: bitstring)) [precise];\n  let record_{i} = if server_identity = ed_public(SERVER_IDENTITY_SECRET) then choice[left_{i}, right_{i}] else left_{i} in",
        )
    generated["sends.pvl"] = s
    s = code("fs-records-b2s-receive.pvl")
    for event, bit in [("FsReceivedFrame", "true"), ("FsReceiveRejected", "false")]:
        pattern = "(event " + event + "\\([^;]*?\\);)"
        s, n = re.subn(
            pattern,
            lambda m: m.group(1) + f"\n out(c, fs_strong_reply(frame, {bit}));",
            s,
        )
        require(n == (3 if bit == "true" else 4), "receive reply branch count changed")
    s, n = re.subn(
        "(event FsFarAccepted\\([^;]*?\\))\\s*else\\s*Failed\\(",
        "\\1; out(c, fs_strong_reply(frame, true))\\n      else out(c, fs_strong_reply(frame, false)); Failed(",
        s,
    )
    if not n == 1:
        raise ValueError("Strong-secrecy source transformation anchor changed")
    old = "  else\n    Next("
    if not s.count(old) == 1:
        raise ValueError("Strong-secrecy source transformation anchor changed")
    s = s.replace(old, "  else\n    out(c, fs_strong_reply(frame, false));\n    Next(")
    generated["interface.pvl"] = (
        "fun fs_strong_reply(bitstring, bool): bitstring [data].\n"
    )
    generated["b2s.pvl"] = generated["b2s.pvl"].replace(
        "fun fs_strong_reply(bitstring, bool): bitstring [data].\n", ""
    )
    generated["receive.pvl"] = s
    generated["query.pv"] = "process FsRecordsB2sMainAnyPin()\n"
    needle = "  out(c, fs_strong_reply(response, true));\n"
    if generated["b2s.pvl"].count(needle) != 1:
        raise ValueError("finish reply anchor changed")
    generated["b2s.pvl"] = (
        generated["b2s.pvl"]
        .replace(needle, "")
        .replace("  FsB2sSends(\n", needle + "  FsB2sSends(\n")
    )
    label_calls(generated, "b2s")
    return generated


def derive_s2b(directory):
    generated = {}

    def code(name):
        return re.sub(r"\(\*.*?\*\)", "", (directory / name).read_text(), flags=re.S)

    s = code("fs-records-s2b.pvl")
    beacon = s.index("let FsS2bBeacon()")
    start = s.index("  let kex_response(", beacon)
    branch = s.index("  if frame_t = 1 then", start)
    first = s.index("    let finish_plaintext = open_frame(", branch)
    event = s.index("    event FsBeaconEstablished(", first)
    recv = s.index("    FsS2bRecv1(", event)
    later = s.index("  else if frame_t = 2 then", recv)
    end = s.index("\nlet FsRecordsS2bMain()", later)
    # These are the only source pieces folded into the pure failure wrapper,
    # rather than copied literally below. Drift requires a fresh source review.
    require(
        token_digest(s[later:end])
        == "9ae6e2451036ba0459d99e93b3465704c61c7b9147cba0e0719a40b039dbcfc4",
        "later finish source changed",
    )
    require(
        token_digest(code("fs-records-s2b-gate.pvl"))
        == "fde9f2daab05858ec705420bb5f988781897a0d4b6847ebe7da6d9c02759affa",
        "sequence-one abort hook changed",
    )
    require(
        token_digest(code("fs-records-s2b-taskings-chosen.pvl"))
        == "fabb26255684dd6495f6506171e2b313f383480bbc051cd5a50844e0462c2cf8",
        "chosen application source changed",
    )
    require(
        " ".join(s[branch:first].split()) == "if frame_t = 1 then (",
        "initial finish branch changed",
    )
    prefix = s[start:branch]
    success = s[first:event]
    helper = (
        "fun fs_strong_s2b_finished(key_id,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring):bitstring [data].\nfun fs_strong_s2b_later(nat):bitstring [data].\nletfun fs_strong_s2b_finish(server_identity:bitstring,beacon_identity:bitstring,\n  beacon_prekey_secret:bitstring,beacon_identity_secret:bitstring,\n  beacon_one_time_secret:bitstring,beacon_pq_secret:bitstring,response:bitstring) =\n"
        + prefix
        + "  if frame_t = 1 then\n"
        + success
        + "    fs_strong_s2b_finished(assigned_key_id,root,associated_data,\n      receive_chain_2,receive_chain_3,receive_chain_4,application_payload,finish_plaintext,initial_frame)\n  else if frame_t = 2 then\n    let opened = open_frame(ratchet_material(receive_chain_2),associated_data,fs_seq(2),SERVER_KEY_ID,initial_frame) in\n    fs_strong_s2b_later(2)\n  else if frame_t = 3 then\n    let opened = open_frame(ratchet_material(receive_chain_3),associated_data,fs_seq(3),SERVER_KEY_ID,initial_frame) in\n    fs_strong_s2b_later(3).\n\n"
    )
    events = s[event:recv]
    receive = s[recv:later].rstrip()
    if not receive.endswith(")\n  )"):
        raise ValueError("Strong-secrecy source transformation anchor changed")
    receive = receive[:-4].rstrip()
    finish = (
        "  let finished = fs_strong_s2b_finish(server_identity,beacon_identity,\n    beacon_prekey_secret,beacon_identity_secret,beacon_one_time_secret,beacon_pq_secret,response) in (\n    let fs_strong_s2b_finished(assigned_key_id:key_id,root:bitstring,associated_data:bitstring,\n      receive_chain_2:bitstring,receive_chain_3:bitstring,receive_chain_4:bitstring,\n      application_payload:bitstring,finish_plaintext:bitstring,initial_frame:bitstring) = finished in (\n"
        + events
        + "    out(c,fs_strong_reply(response,true));\n    (out(fs_strong_partner,(assigned_key_id,root)) |\n"
        + receive
        + ")\n    ) else (\n      let fs_strong_s2b_later(t:nat) = finished in\n      event FsBeaconFinishOpenedLater(server_identity,beacon_identity,t);\n      out(c,fs_strong_reply(response,false))\n    )\n  ) else out(c,fs_strong_reply(response,false)).\n"
    )
    # Equivalence-only local observation quotient: a non-1 initial frame
    # terminates with None whether its silent later open succeeds or fails.
    # The omitted ghost event is not observed or queried by either target.
    # This does not erase computational primitive histories or query costs.
    cutoff = helper.index("  else if frame_t = 2 then")
    helper = helper[:cutoff].rstrip() + ".\n\n"
    helper = helper.replace("fun fs_strong_s2b_later(nat):bitstring [data].\n", "")
    old = (
        ") else (\n"
        "      let fs_strong_s2b_later(t:nat) = finished in\n"
        "      event FsBeaconFinishOpenedLater(server_identity,beacon_identity,t);\n"
        "      out(c,fs_strong_reply(response,false))\n"
        "    )"
    )
    require(finish.count(old) == 1, "terminal later-frame result branch changed")
    finish = finish.replace(old, ") else out(c,fs_strong_reply(response,false))")
    generated["s2b.pvl"] = helper + s[:start] + finish + s[end:]
    args = "server_identity:bitstring,beacon_identity:bitstring,assigned_key_id:key_id,root:bitstring,associated_data:bitstring"
    values = "server_identity,beacon_identity,assigned_key_id,root,associated_data"
    taskings = f"let FsStrongS2bTasking3({args},send_chain_3:bitstring) =\n  in(c,tasking_3:bitstring) [precise];\n  event FsSent(server_to_beacon(),{values.replace(',associated_data', '')},3,tasking_3);\n  out(c,seal_frame(ratchet_material(send_chain_3),associated_data,fs_seq(3),SERVER_KEY_ID,tasking_3)).\n\nlet FsStrongS2bSend2({args},send_chain_2:bitstring,send_chain_3:bitstring,tasking_2:bitstring) =\n  event FsSent(server_to_beacon(),{values.replace(',associated_data', '')},2,tasking_2);\n  out(c,seal_frame(ratchet_material(send_chain_2),associated_data,fs_seq(2),SERVER_KEY_ID,tasking_2));\n  FsStrongS2bTasking3({values},send_chain_3).\n\nlet FsS2bTaskings({args},send_chain_2:bitstring,send_chain_3:bitstring) =\n  in(c,(test:bool,left:bitstring,right:bitstring)) [precise];\n  if test then (\n    in(fs_strong_partner,(=assigned_key_id,=root));\n    FsStrongS2bSend2({values},send_chain_2,send_chain_3,choice[left,right])\n  ) else FsStrongS2bSend2({values},send_chain_2,send_chain_3,left).\n"
    generated["taskings.pvl"] = taskings
    s = code("fs-records-s2b-receive.pvl")
    for event, bit in [("FsReceivedFrame", "true"), ("FsReceiveRejected", "false")]:
        s, n = re.subn(
            "(event " + event + "\\([^;]*?\\);)",
            lambda m: m.group(1) + f"\n out(c,fs_strong_reply(frame,{bit}));",
            s,
        )
        require(n == (3 if bit == "true" else 4), "receive reply branch count changed")
    s, n = re.subn(
        "(event FsFarAccepted\\([^;]*?\\))\\s*else\\s*Next\\(",
        "\\1; out(c,fs_strong_reply(frame,true))\\n else out(c,fs_strong_reply(frame,false)); Next(",
        s,
    )
    if not n == 1:
        raise ValueError("Strong-secrecy source transformation anchor changed")
    old = "  else\n    Next("
    if not s.count(old) == 1:
        raise ValueError("Strong-secrecy source transformation anchor changed")
    s = s.replace(old, "  else\n    out(c,fs_strong_reply(frame,false));\n    Next(")
    generated["receive.pvl"] = s
    generated["query.pv"] = "process FsRecordsS2bMain()\n"
    label_calls(generated, "s2b")
    # Optional analysis precision is needed only at the challenge selection.
    # This changes no process operation, protocol bound or observable output.
    for name in ("s2b.pvl", "receive.pvl", "taskings.pvl"):
        generated[name] = generated[name].replace("[precise]", "")
    anchor = "in(c,(test:bool,left:bitstring,right:bitstring)) ;"
    require(
        generated["taskings.pvl"].count(anchor) == 1,
        "challenge precision anchor changed",
    )
    generated["taskings.pvl"] = generated["taskings.pvl"].replace(
        anchor, "in(c,(test:bool,left:bitstring,right:bitstring)) [precise];"
    )
    generated["query.pv"] = "set simplifyProcess = false.\n" + generated["query.pv"]
    return generated
