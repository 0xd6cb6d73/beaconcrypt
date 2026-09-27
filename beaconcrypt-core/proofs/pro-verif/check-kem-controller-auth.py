#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check original authentication events without any symbolic KEM algebra."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "kem_controller_generator", HERE / "generate-kem-controller-auth.py"
)
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)

ACCEPTED = "server_identity,beacon_identity,init,registration_id,root_input,root,origin"
INITIATED = "server_identity,beacon_identity,init,registration_id,origin"
COMPLETED = "main_agreement,main_sequence,main_payload,main_frame,main_claimed"
FIRST = "main_agreement,first_sequence,main_payload,main_frame,main_claimed"
RECORD = "main_agreement,main_sequence,main_payload,main_frame,main_server_assigned"
MESSAGE = "session,message_direction,message_sequence,sender,receiver,plaintext"


def correspondence(before, after, polarity="true"):
    return f"RESULT inj-event({before}) ==> inj-event({after}) is {polarity}."


AUTHENTICATION = (
    correspondence(f"ServerAccepted({ACCEPTED})", f"BeaconInitiated({INITIATED})"),
    correspondence("ServerBundleAccepted(bundle)", "BeaconBundleInitiated(bundle)"),
    correspondence(f"ServerAccepted({ACCEPTED})", f"RegistrationConsumed({INITIATED})"),
    correspondence(
        f"RegistrationConsumed({INITIATED})", f"BeaconInitiated({INITIATED})"
    ),
    correspondence(
        f"ServerResponseAborted({ACCEPTED})", f"RegistrationConsumed({INITIATED})"
    ),
    correspondence(
        f"BeaconAuthenticatedRegistrationCompleted({FIRST})",
        f"AuthenticatedRegistrationRecordSent({FIRST})",
    ),
    correspondence(f"MessageReceived({MESSAGE})", f"MessageSent({MESSAGE})"),
    correspondence(
        f"BeaconAuthenticatedRegistrationCompleted({COMPLETED})",
        "ServerAuthenticatedSessionCommitted(main_agreement,main_server_assigned)",
    ),
    correspondence(
        f"BeaconAuthenticatedRegistrationCompleted({COMPLETED})",
        f"AuthenticatedRegistrationRecordSent({RECORD})",
    ),
)
REACHABILITY = tuple(
    f"RESULT not event({event}) is false."
    for event in (
        f"ServerAccepted({ACCEPTED})",
        "ServerBundleAccepted(bundle)",
        f"RegistrationReplayRejected({INITIATED})",
        f"ServerResponseAborted({ACCEPTED})",
        "BeaconCommitted(transcript)",
        f"MessageReceived({MESSAGE})",
        "MaliciousRegistrationCommitted(transcript,plaintext)",
    )
) + ("RESULT not attacker(MALICIOUS_TASK_SECRET) is false.",)
CONTROLS = (
    "RESULT not event(KemControllerRejected(kem_generate_request(handle))) is false.",
    "RESULT not event(KemControllerRejected(kem_encapsulation_request(public_key))) is false.",
    "RESULT not event(KemControllerRejected(kem_decapsulation_request(handle,public_key,ciphertext))) is false.",
    "RESULT not (event(KemControllerReturned(kem_generate_request(left),kem_generate_reply(public_key))) && event(KemControllerReturned(kem_generate_request(right),kem_generate_reply(public_key))) && left ≠ right) is false.",
    "RESULT not (event(KemControllerReturned(kem_encapsulation_request(left),kem_encapsulation_reply(first,shared))) && event(KemControllerReturned(kem_encapsulation_request(right),kem_encapsulation_reply(second,shared))) && left ≠ right) is false.",
    "RESULT not (event(KemControllerReturned(kem_encapsulation_request(public_key),kem_encapsulation_reply(ciphertext,sent))) && event(KemControllerReturned(kem_decapsulation_request(handle,public_key,ciphertext),kem_decapsulation_reply(received))) && sent ≠ received) is false.",
)
EXPOSED = tuple(
    result.replace(" is true.", " is false.") for result in AUTHENTICATION[5:]
)
EXPECTED = {
    "authentication": AUTHENTICATION,
    "reachability": REACHABILITY,
    "controls": CONTROLS,
    "exposed": EXPOSED,
}


def canonical(result):
    # ProVerif adds numeric suffixes to the original quantified variable names.
    # No original query variable ends in _<number>; all event/field order stays.
    result = re.sub(r"\b([A-Za-z][A-Za-z0-9_]*)_[0-9]+\b", r"\1", result)
    return re.sub(r"\s+", "", result).replace("[]", "")


def check_output(mode, output):
    expected = tuple(map(canonical, EXPECTED[mode]))
    primary = tuple(
        canonical(line)
        for line in output.splitlines()
        if line.startswith("RESULT ") and not line.startswith("RESULT (even ")
    )
    if primary != expected:
        raise ValueError(
            f"{mode}: changed, missing, duplicated, unknown or reordered results: {primary}"
        )
    if output.count("Verification summary:") != 1:
        raise ValueError(f"{mode}: missing or duplicated verification summary")
    summary = output.split("Verification summary:")[1]
    summaries = tuple(
        canonical("RESULT " + line[6:])
        for line in summary.splitlines()
        if line.startswith("Query ")
    )
    if summaries != expected:
        raise ValueError(f"{mode}: final summary does not match exact query results")
    secondary = tuple(
        canonical(line)
        for line in output.splitlines()
        if line.startswith("RESULT (even ")
    )
    expected_secondary = (
        tuple(
            canonical(
                result.replace("RESULT ", "RESULT (even ").replace(
                    "inj-event", "event"
                )[:-1]
                + ".)"
            )
            for result in EXPOSED
        )
        if mode == "exposed"
        else ()
    )
    if secondary != expected_secondary:
        raise ValueError(f"{mode}: unexpected weaker-correspondence output")
    traces = 0 if mode == "authentication" else len(expected)
    if (
        output.count("A trace has been found.") != traces
        or "I could not confirm" in output
    ):
        raise ValueError(f"{mode}: every intended false result needs a confirmed trace")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(directory):
    GENERATOR.generate(directory)
    original = (HERE / "baseline.pv").read_text()
    (directory / "exposed.pv").write_text(
        GENERATOR.replace_exact(
            original, "process\n", "process\n  out(c, SERVER_IDENTITY_SECRET);\n", 1
        )
    )
    queries = re.findall(
        r"\bquery\b.*?\.", (directory / "queries.pvl").read_text(), flags=re.S
    )
    (directory / "exposed-queries.pvl").write_text("\n\n".join(queries[5:]) + "\n")


def run(args, directory):
    prepare(directory)
    libraries = [
        HERE / "production-transcript-interface.pvl",
        directory / "crypto.pvl",
        HERE / "extraction/lib.pvl",
        HERE / "kem-controller-interface.pvl",
        directory / "environment.pvl",
    ]
    queries = {
        "authentication": directory / "queries.pvl",
        "reachability": HERE / "reachability-queries.pvl",
        "controls": HERE / "kem-controller-controls.pvl",
        "exposed": directory / "exposed-queries.pvl",
    }

    def one(mode):
        process = (
            directory / "exposed.pv" if mode == "exposed" else HERE / "baseline.pv"
        )
        command = [args.proverif]
        for library in libraries + [queries[mode]]:
            command += ["-lib", str(library)]
        command.append(str(process))
        log = directory / f"{mode}.log"
        started = time.monotonic()
        with log.open("w") as output:
            result = subprocess.run(
                command,
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=args.timeout,
                check=False,
            )
        if result.returncode != 0:
            raise ValueError(f"{mode}: ProVerif exited {result.returncode}: {log}")
        check_output(mode, log.read_text())
        record = {
            "mode": mode,
            "command": command,
            "exit": result.returncode,
            "queries": len(EXPECTED[mode]),
            "seconds": time.monotonic() - started,
            "log_sha256": digest(log),
        }
        print(
            f"KEM controller {mode}: {record['queries']} exact results passed",
            flush=True,
        )
        return record

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        runs = list(pool.map(one, EXPECTED))
    inputs = [
        HERE / name
        for name in (
            "production-transcript-interface.pvl",
            "crypto.pvl",
            "extraction/lib.pvl",
            "environment.pvl",
            "queries.pvl",
            "baseline.pv",
            "reachability-queries.pvl",
            "kem-controller-interface.pvl",
            "kem-controller-controls.pvl",
            "generate-kem-controller-auth.py",
            "check-kem-controller-auth.py",
        )
    ]
    receipt = {
        "scope": "Nine original authentication correspondences under arbitrary public KEM replies; eighteen confirmed reachability/negative controls. No computational soundness or secrecy conclusion.",
        "inputs": {str(path.relative_to(HERE)): digest(path) for path in inputs},
        "generated": {
            path.name: digest(path)
            for path in sorted(directory.iterdir())
            if path.suffix in {".pv", ".pvl"}
        },
        "runs": runs,
    }
    (directory / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--timeout", type=int, default=240)
    parser.add_argument("--jobs", type=int, choices=range(1, 5), default=2)
    parser.add_argument("--log-dir", type=Path)
    args = parser.parse_args()
    if args.log_dir is not None:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(
            prefix="beaconcrypt-kem-controller-"
        ) as temporary:
            run(args, Path(temporary))


if __name__ == "__main__":
    main()
