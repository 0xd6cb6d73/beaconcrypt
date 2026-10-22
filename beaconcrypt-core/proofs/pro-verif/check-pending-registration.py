#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check focused delayed/moved-token registration operations.

These are finite operational witnesses and a one-use structural check, not
replicated protocol authentication or a computational security reduction.
"""

import argparse
from dataclasses import dataclass
import fcntl
import importlib.util
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "pending_base", HERE / "check-free-schedule.py"
)
FS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FS)
NORMAL = "fs-pending-use.pvl"
CONTROL = "fs-control-pending-reuse.pvl"


@dataclass(frozen=True)
class PendingTarget(FS.Target):
    def libraries(self):
        return (
            FS.COMMON_LOADER
            + (
                FS.CONSUMED,
                FS.BINDING,
                "registration-set-admission.pvl",
                FS.REGISTRATION_PROCESS,
                "fs-pending-response.pvl",
            )
            + self.hooks
            + ("fs-pending-registration.pvl", "fs-pending-fixtures.pvl")
        )


CROSS = "event(SchedBuilt(origin_1,owner_4,token_2,next_1)) ==> origin_1 = owner_4"
REVERSE = "not event(SchedBuilt(owner_9,owner_9,sched_token(0),2))"
LINEAR = "event(SchedTokenConsumed(first,token_3))@i && event(SchedTokenConsumed(second,token_3))@j ==> i = j"
TARGETS = (
    PendingTarget(
        "pending-CROSS",
        "pending-registration",
        "witness",
        1,
        (NORMAL,),
        "fs-pending-cross-object.pv",
        (CROSS + " is false.",),
    ),
    PendingTarget(
        "pending-REVERSE",
        "pending-registration",
        "witness",
        2,
        (NORMAL,),
        "fs-pending-reverse-builds.pv",
        (REVERSE + " is false.",),
    ),
    PendingTarget(
        "pending-LINEAR",
        "pending-registration",
        "definitional",
        1,
        (NORMAL,),
        "fs-pending-single-use.pv",
        (LINEAR + " is true.",),
    ),
    PendingTarget(
        "pending-C-REUSE",
        "pending-registration",
        "control",
        1,
        (CONTROL,),
        "fs-pending-single-use.pv",
        (LINEAR + " is false.",),
    ),
)


def check_tail(directory=HERE):
    original = (directory / "registration-set-response.pvl").read_text()
    marker = "let RegistrationResponseBuilder("
    if original.count(marker) != 1:
        raise ValueError("response builder boundary changed")
    expected = (
        original[: original.index(marker)]
        .replace("RegistrationResponseTail", "SchedResponseTail")
        .replace("first_sequence()", "fs_seq(1)")
        .replace("registration_response_identifier(next)", "fs_kid(next)")
    )
    if FS.uncommented(expected) != FS.uncommented(
        (directory / "fs-pending-response.pvl").read_text()
    ):
        raise ValueError(
            "pending response differs outside the three explicit renamings"
        )


def check_token_service(directory=HERE):
    expected = {
        NORMAL: "letfun sched_reusable() = false.",
        CONTROL: "letfun sched_reusable() = true.",
    }
    for name, text in expected.items():
        if FS.uncommented((directory / name).read_text()) != text:
            raise ValueError("linear lifetime or its second-use control changed")
    model = FS.uncommented((directory / "fs-pending-registration.pvl").read_text())
    consume = model.split("let SchedConsume(", 1)[1].split("let SchedSpent(", 1)[0]
    anchors = (
        "event SchedTokenConsumed(owner, token);",
        "if counter < limit then",
        "if server_identity = ed_public(SERVER_IDENTITY_SECRET) && server_id = SERVER_KEY_ID then",
        "get registration_response_peers(=owner, =assigned",
        "SchedTail(owner, origin, token, request",
    )
    if any(consume.count(anchor) != 1 for anchor in anchors):
        raise ValueError("pending builder consumption/publication boundary changed")
    positions = [consume.index(anchor) for anchor in anchors]
    if " if " in consume[: positions[0]] or positions != sorted(positions):
        raise ValueError("token consumption no longer precedes every build guard")
    service = model.split("let SchedTokenService(", 1)[1].split("let SchedAccept(", 1)[
        0
    ]
    spent = model.split("let SchedSpent(", 1)[1].split("let SchedSecondUse(", 1)[0]
    second = model.split("let SchedSecondUse(", 1)[1].split(
        "let SchedTokenService(", 1
    )[0]
    if (
        service.count("in(lease,") != 1
        or "!in(lease," in service
        or service.count("[precise];") != 1
        or service.count("SchedConsume(owner, token,") != 1
        or "| if sched_reusable() then SchedSecondUse(token, lease, origin,"
        not in service
        or "else SchedSpent(lease)" not in service
    ):
        raise ValueError("the token's first-use input is no longer linear")
    if (
        spent.count("!in(lease,") != 1
        or "SchedConsume" in spent
        or "SchedReturn(request, sched_none(), lock, state, accepts, builds, counter, ticket_counter)"
        not in spent
    ):
        raise ValueError("spent token must return None for every later request")
    if (
        second.count("in(lease,") != 1
        or "!in(lease," in second
        or second.count("[precise];") != 1
        or second.count("SchedConsume(owner, token,") != 1
        or "| SchedSpent(lease)" not in second
    ):
        raise ValueError("control must add exactly one further token consumption")
    build = model.split("let SchedBuild(", 1)[1].split("let SchedAbsent(", 1)[0]
    if (
        build.count("get sched_pending(=token, origin: bitstring") != 1
        or "root: bitstring, lease: channel) in" not in build
        or "out(lease, (owner, data, failure_stage, request, lock, state, accepts, builds, counter, ticket_counter, limit))"
        not in build
    ):
        raise ValueError("pending handle or current-builder routing changed")
    if (
        "out(c, sched_reply(request, reply))" not in model
        or "out(c, sched_reply(request, sched_none()))" not in model
        or "let sched_call(call_id: bitstring, operation: bitstring) = request in"
        not in model
        or "let sched_accept(owner, raw, failure_stage) = operation in" not in model
        or "let sched_build(owner, token, data, failure_stage) = operation in"
        not in model
    ):
        raise ValueError("caller request/reply correlation was removed")
    for anchor in (
        "if accepts < accept_cap then",
        "if builds < build_cap then",
        "SchedMainWithCaps(2, 2, 2)",
    ):
        if model.count(anchor) != 1:
            raise ValueError("attempt or allocation bounds changed")


def check_publication(directory=HERE):
    model = FS.uncommented((directory / "fs-pending-registration.pvl").read_text())
    expected_outputs = {
        "out(c, sched_reply(request, reply))",
        "out(c, sched_reply(request, sched_none()))",
        "out(c, ed_public(SERVER_IDENTITY_SECRET))",
        "out(c, owner)",
    }
    outputs = []
    for match in re.finditer(r"\bout\(c,", model):
        depth = 1
        end = match.end()
        while depth and end < len(model):
            depth += (model[end] == "(") - (model[end] == ")")
            end += 1
        if depth:
            raise ValueError("unbalanced public output")
        outputs.append(model[match.start() : end])
    if len(outputs) != len(expected_outputs) or set(outputs) != expected_outputs:
        raise ValueError("public scheduler output exposes an unexpected field")
    accept = model.split("let SchedAccept(", 1)[1].split("let SchedBuild(", 1)[0]
    anchors = (
        "registration_set_verify(raw)",
        "get registration_set_consumed(=owner, =rid)",
        "registration_set_root(SERVER_IDENTITY_SECRET, identity, prekey, one_time, pq, failure_stage)",
        "insert registration_set_consumed(owner, rid);",
        "let token = sched_token(ticket_counter) in",
        "insert sched_pending(token, owner, server_identity, SERVER_KEY_ID, verified, core_init, ephemeral, ciphertext, root, lease);",
        "event SchedTokenCreated(owner, token);",
        "SchedReturn(request, sched_some_token(token),",
    )
    if any(accept.count(anchor) != 1 for anchor in anchors):
        raise ValueError("accepting provenance or opaque handle publication changed")
    positions = [accept.index(anchor) for anchor in anchors]
    if positions != sorted(positions):
        raise ValueError("pending publication precedes actual registration consumption")


def check_source(directory=HERE):
    root = directory.parents[2]
    source = (root / "beaconcrypt/src/server.rs").read_text()
    start = source.rindex("\n\tfn build_registration_response(")
    body = source[start : source.index("\n\tfn encrypt_and_update(", start)]
    compact = " ".join(body.split())
    if "reg_out: RegistrationOutput," not in compact:
        raise ValueError("source response token is no longer passed by move")
    if "consumed_registrations" in body:
        raise ValueError("builder now observes the accepting consumed set")
    for anchor in (
        "let RegistrationOutput { derived_secret, control: pending, } = reg_out;",
        "let next_key_id = verified_pqxdh::server_next_key_id(control).ok()?;",
        "let plaintext = data.unwrap_or(REGISTRATION_WITNESS);",
        "registration_response_len(plaintext.len(), next_key_id)?;",
        "if plaintext.is_empty() { return None; }",
        "self.control = next_control; Some(RegResponse",
    ):
        if anchor not in compact:
            raise ValueError(
                f"source moved-token/counter/payload/publication boundary changed: {anchor}"
            )
    ordered = (
        "let plaintext = data.unwrap_or(REGISTRATION_WITNESS);",
        "let next_key_id = verified_pqxdh::server_next_key_id(control).ok()?;",
        "registration_response_len(plaintext.len(), next_key_id)?;",
        "let RegistrationOutput {",
        "if plaintext.is_empty()",
        "encrypt_registration_message_with_ratchet(",
        "crate::wire::encode_response(KexResponse {",
        "self.control = next_control;",
    )
    positions = [compact.index(anchor) for anchor in ordered]
    if positions != sorted(positions):
        raise ValueError(
            "source size admission/token consumption/publication order changed"
        )


def validate_targets(targets=TARGETS, directory=HERE):
    FS.validate_targets(directory=directory)
    check_tail(directory)
    check_token_service(directory)
    check_publication(directory)
    check_source(directory)
    if len({target.name for target in targets}) != len(targets):
        raise ValueError("duplicate pending target")
    if len({FS.log_name(target) for target in targets}) != len(targets):
        raise ValueError("duplicate pending log")
    if {target.query for target in targets} != {
        path.name for path in directory.glob("fs-pending-*.pv")
    }:
        raise ValueError("pending query roster is incomplete")
    for target in targets:
        if (
            target.scenario != "pending-registration"
            or target.cls == "security"
            or target.bound not in (1, 2)
        ):
            raise ValueError(
                "pending fixtures have only their finite operational scope"
            )
        if target.hooks not in ((NORMAL,), (CONTROL,)) or (target.cls == "control") != (
            target.hooks == (CONTROL,)
        ):
            raise ValueError("only the negative control changes token use")
        for filename in (*target.libraries(), target.query):
            if not (directory / filename).is_file():
                raise ValueError(f"missing pending input {filename}")
        if (
            len(target.results) != 1
            or target.results[0].endswith(" is true.") != target.expected_true()
        ):
            raise ValueError("pending target class and verdict differ")
    if tuple(targets) != TARGETS:
        raise ValueError("exact four-target pending roster changed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--results", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--target", action="append", choices=[target.name for target in TARGETS]
    )
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    args = parser.parse_args()
    validate_targets()
    if args.check_only:
        print(f"pending registration manifest: {len(TARGETS)} focused targets checked")
        return
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("pending checks must retain the approved per-target caps")
    targets = [
        target
        for target in TARGETS
        if args.target is None or target.name in args.target
    ]
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    with args.lock.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        FS.run_logged(
            args.proverif,
            targets,
            args.log_dir,
            args.timeout,
            args.address_space_kib,
            args.results,
        )


if __name__ == "__main__":
    main()
