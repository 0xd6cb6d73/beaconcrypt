#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the explicit-assumption joint ML-DSA/PQXDH session profile."""

import argparse
import hashlib
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "environment.pvl",
    "mldsa-auth.pvl",
    "quantum-capabilities.pvl",
)
MODEL_FILES = LIBRARIES + ("mldsa-joint-session.pvl", "mldsa-joint-session.pv")
MODEL_SHA256 = {
    "production-transcript-interface.pvl": "0993f0933677e37aa61ed9b52a3d7dfcfc884e982fb7d76b199c177be74b74de",
    "crypto.pvl": "af940d6fe6959644aa9712715cc730d1990e6b954bca0de8c7015262e7371b16",
    "extraction/lib.pvl": "c47011ed155a109d72ea99771ac08fcd5c30ca51cd3d705be6b3997a7a67deb6",
    "environment.pvl": "aef86503f38f04850fa9057c6f8fc2a634aeef390141fc364a7c79daf833be1d",
    "mldsa-auth.pvl": "09c409113e49aa61f4f7d777d30f3778a743ccab7a47cf9d7c506b146d29e403",
    "quantum-capabilities.pvl": "215da20adfe2ec160ee1793e2a1041f826755126c13f5634eda59bfdf09f88cd",
    "mldsa-joint-session.pvl": "0feea2541f66026068d05799d0a1a5329ccfd2e60fd7f0978088f7280c7b958b",
    "mldsa-joint-session.pv": "51f1803f6090bd87807d480341811de458c57b6e808d956242e8751f8630562a",
}

PRIMARY = (
    "event(JointInitAccepted(agent_ml,server_ml,init_hash,classical_init)) && "
    "event(JointProtectedBeacon(agent_ml)) ==> "
    "event(JointInitSigned(agent_ml,server_ml,init_hash,classical_init))",
    "event(JointResponseVerified(server_ml,init_hash,response)) ==> "
    "event(JointResponseSigned(server_ml,init_hash,response))",
    "event(JointBeaconCompleted(agent_ml,server_ml,init_hash,response,root,ad,assigned,initial)) ==> "
    "event(JointServerCommitted(agent_ml,server_ml,init_hash,response,root,ad,assigned,initial))",
    "event(JointRecordReceived(agent_ml,server_ml,init_hash,root,ad,server_to_beacon,seq,sender,receiver,plaintext)) && "
    "event(JointProtectedBeacon(agent_ml)) ==> "
    "event(JointRecordSent(agent_ml,server_ml,init_hash,root,ad,server_to_beacon,seq,sender,receiver,plaintext))",
    "event(JointRecordReceived(agent_ml,server_ml,init_hash,root,ad,beacon_to_server,seq,sender,receiver,plaintext)) && "
    "event(JointProtectedBeacon(agent_ml)) ==> "
    "event(JointRecordSent(agent_ml,server_ml,init_hash,root,ad,beacon_to_server,seq,sender,receiver,plaintext))",
    "not attacker(MLDSA_JOINT_INITIAL[])",
    "not attacker(MLDSA_JOINT_SERVER_RECORD[])",
    "not attacker(MLDSA_JOINT_BEACON_RECORD[])",
    "not event(JointHonestComplete)",
    "not event(JointServerRecordOpened)",
    "not event(JointBeaconRecordOpened)",
    "not event(JointOwnedAccepted)",
    "not event(JointReplayRejected)",
    "not event(JointClassicalRecovered)",
)
VERDICTS = ("true",) * 8 + ("false",) * 6
VARIABLE = re.compile(
    r"\b(?:agent_ml|server_ml|init_hash|classical_init|response|root|ad|assigned|initial|"
    r"seq|sender|receiver|plaintext)(?:_[0-9]+)?\b(?!\s*\()"
)
INIT_VERIFIER = (
    "let verified_init_input = mldsa_verify(candidate_signature,\n"
    "    candidate_ml, mldsa_signing_context()) in"
)
INIT_BYPASS = "let verified_init_input = mldsa_beacon_input(candidate_hash) in"
RESPONSE_VERIFIER = (
    "let verified_response_input = mldsa_verify(response_signature,\n"
    "    server_ml, mldsa_signing_context()) in"
)
RESPONSE_BYPASS = (
    "let verified_response_input = mldsa_server_input(expected_response_hash) in"
)
CONTROLS = (
    (
        "without-init-verifier-origin",
        "mldsa-joint-session.pvl",
        0,
        INIT_VERIFIER,
        INIT_BYPASS,
    ),
    (
        "without-response-verifier-origin",
        "mldsa-joint-session.pvl",
        1,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
    (
        "without-response-verifier-session",
        "mldsa-joint-session.pvl",
        2,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
    (
        "without-init-verifier-secrecy",
        "mldsa-joint-session.pvl",
        5,
        INIT_VERIFIER,
        INIT_BYPASS,
    ),
    (
        "without-response-verifier-secrecy",
        "mldsa-joint-session.pvl",
        7,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
)


def canonical_query(query):
    """Allow bound-variable alpha suffixes while preserving equality patterns."""
    names = {}

    def replace(match):
        name = match.group()
        if name not in names:
            names[name] = "V" + str(len(names))
        return names[name]

    return VARIABLE.sub(replace, query)


def check_output(output, queries, verdicts, traces):
    if (
        not queries
        or len(queries) != len(verdicts)
        or set(verdicts) - {"true", "false"}
        or traces != verdicts.count("false")
    ):
        raise ValueError("invalid exact expectation roster")
    if re.search(r"^\s*(?:Warning|Error|Fatal|Timeout)\b", output, re.M | re.I):
        raise ValueError("verifier warning or error")
    if re.search(
        r"assuming a hypothesis|\bcannot be proved\b|\bunknown\b", output, re.I
    ):
        raise ValueError("unknown verdict or unconfirmed attack trace")
    if output.count("Verification summary:") != 1:
        raise ValueError("missing or duplicate verification summary")
    before, after = output.split("Verification summary:")
    expected = [
        canonical_query(q) + " is " + v + "."
        for q, v in zip(queries, verdicts, strict=True)
    ]
    results = []
    pending_traces = 0
    for line in before.splitlines():
        if line.strip() == "A trace has been found.":
            pending_traces += 1
        if re.match(r"^\s*Query\b", line):
            raise ValueError("summary query before verification summary")
        if re.match(r"^\s*RESULT\b", line):
            position = len(results)
            if not line.startswith("RESULT ") or position >= len(expected):
                raise ValueError("extra or malformed primary result")
            result = canonical_query(line[7:])
            if result != expected[position]:
                raise ValueError(
                    "missing, reordered, duplicated or changed exact query/verdict"
                )
            if pending_traces != int(verdicts[position] == "false"):
                raise ValueError("missing, extra or misplaced reconstructed trace")
            pending_traces = 0
            results.append(result)
    if pending_traces or "A trace has been found." in after:
        raise ValueError("reconstructed trace without its primary verdict")
    summary = []
    for line in after.splitlines():
        if re.match(r"^\s*RESULT\b", line):
            raise ValueError("primary result after verification summary")
        if re.match(r"^\s*Query\b", line):
            if not line.startswith("Query "):
                raise ValueError("malformed summary query")
            summary.append(canonical_query(line[6:]))
    if results != expected or summary != expected:
        raise ValueError(
            "missing, reordered, duplicated or changed exact query/verdict"
        )


def digest(text):
    """Pin executable ProVerif tokens without churning reviewed prose or spacing."""
    return hashlib.sha256(
        re.sub(r"\s+", "", re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)).encode()
    ).hexdigest()


def validate_models(directory=HERE):
    if set(MODEL_SHA256) != set(MODEL_FILES):
        raise ValueError("incomplete reviewed model and library roster")
    for name in MODEL_FILES:
        if digest((directory / name).read_text()) != MODEL_SHA256[name]:
            raise ValueError("review changed joint-session model or library: " + name)


def exact_replace(source, old, new):
    if source.count(old) != 1:
        raise ValueError("missing or ambiguous negative-control anchor")
    return source.replace(old, new)


def run(proverif, model, queries, log, timeout, *, library_overrides=None):
    overrides = library_overrides or {}
    if set(overrides) - set(LIBRARIES):
        raise ValueError("unreviewed library override")
    paths = [overrides.get(name, HERE / name) for name in LIBRARIES] + [model, queries]
    command = [proverif]
    for path in paths[:-1]:
        command += ["-lib", str(path)]
    command.append(str(paths[-1]))
    before = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    try:
        result = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        evidence = error.stdout or b""
        log.write_bytes(evidence.encode() if isinstance(evidence, str) else evidence)
        raise ValueError("verifier timeout: " + str(log)) from error
    log.write_text(result.stdout)
    if result.returncode:
        raise ValueError("verifier failure: " + str(log))
    if before != {
        path: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths
    }:
        raise ValueError("model or library changed while verifier ran")
    return result.stdout


def query_declarations(source):
    """Keep each reviewed query intact when isolating an actual negative control."""
    source = re.sub(r"\(\*.*?\*\)", "", source, flags=re.S)
    parts = re.split(r"\bprocess\b", source)
    if len(parts) != 2:
        raise ValueError("missing or ambiguous query process")
    declarations, process = parts
    declarations = declarations.strip().split("query ")
    if declarations[0] or len(declarations) - 1 != len(PRIMARY):
        raise ValueError("changed query declaration roster")
    return declarations[1:], process


def check(proverif, logdir, timeout):
    validate_models()
    logdir.mkdir(parents=True, exist_ok=True)
    model = HERE / "mldsa-joint-session.pvl"
    queries = HERE / "mldsa-joint-session.pv"
    output = run(proverif, model, queries, logdir / "mldsa-joint-session.log", timeout)
    check_output(output, PRIMARY, VERDICTS, VERDICTS.count("false"))
    declarations, process = query_declarations(queries.read_text())
    for name, filename, position, old, new in CONTROLS:
        if position not in range(len(PRIMARY)) or VERDICTS[position] != "true":
            raise ValueError("negative control must invert a proved security query")
        changed = logdir / (name + ".pvl")
        changed.write_text(exact_replace((HERE / filename).read_text(), old, new))
        control_queries = logdir / (name + ".pv")
        control_queries.write_text(
            "query " + declarations[position] + "\nprocess\n" + process
        )
        overrides = {filename: changed} if filename in LIBRARIES else {}
        output = run(
            proverif,
            model if overrides else changed,
            control_queries,
            logdir / (name + ".log"),
            timeout,
            library_overrides=overrides,
        )
        check_output(output, (PRIMARY[position],), ("false",), 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--logdir", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        check(args.proverif, args.logdir, args.timeout)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + "\n")
    print(
        f"ML-DSA assumed-security joint session: {len(PRIMARY)} exact verdicts and "
        f"{len(CONTROLS)} reconstructed negative controls passed"
    )


if __name__ == "__main__":
    main()
