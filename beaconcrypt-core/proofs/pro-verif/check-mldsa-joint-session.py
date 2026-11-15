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
    "production-transcript-interface.pvl": "b302b3f87e6215f0ed1c3439df6ba3dd1aab6a086e9a7ee3ab6fb98182f1f308",
    "crypto.pvl": "1c56f4c67c8d5c0193acf3fc9d1570aa729b2b1ecc05418cca3e47f0afa1a0ef",
    "extraction/lib.pvl": "9b092c36ee8b8e25fb8a1be6c6934210c243cbd87249acf36d0e2fa2c4417608",
    "environment.pvl": "5b99e3dde14e824f625ff07c30d52ae797048b63d0fe5131391e026b02b57979",
    "mldsa-auth.pvl": "f0327d648099b035b4e374467ee31f038a2a884f51fe980719b90372d18f1f05",
    "quantum-capabilities.pvl": "215da20adfe2ec160ee1793e2a1041f826755126c13f5634eda59bfdf09f88cd",
    "mldsa-joint-session.pvl": "334ed8242f5d693aa10e8dabdca5dd5fb678086b59bd2d15defafc3489ef4fe2",
    "mldsa-joint-session.pv": "d9e910cc562620b0ca2f619400279ec12bfd4a00443b34fd9f8bafd43a8619e2",
}

PRIMARY = (
    "event(JointResponseVerified(server_ml,init_hash,response)) ==> "
    "event(JointResponseSigned(server_ml,init_hash,response))",
    "event(JointBeaconCompleted(request,server_ml,init_hash,response,root,ad,assigned,initial)) ==> "
    "event(JointServerCommitted(request,server_ml,init_hash,response,root,ad,assigned,initial))",
    "event(JointRecordReceived(request,server_ml,init_hash,root,ad,server_to_beacon,seq,sender,receiver,plaintext)) && "
    "event(JointSessionCreated(request)) ==> "
    "event(JointRecordSent(request,server_ml,init_hash,root,ad,server_to_beacon,seq,sender,receiver,plaintext))",
    "event(JointRecordReceived(request,server_ml,init_hash,root,ad,beacon_to_server,seq,sender,receiver,plaintext)) && "
    "event(JointSessionCreated(request)) ==> "
    "event(JointRecordSent(request,server_ml,init_hash,root,ad,beacon_to_server,seq,sender,receiver,plaintext))",
    "not attacker(MLDSA_JOINT_INITIAL[])",
    "not attacker(MLDSA_JOINT_SERVER_RECORD[])",
    "not attacker(MLDSA_JOINT_BEACON_RECORD[])",
    "not event(JointHonestComplete)",
    "not event(JointServerRecordOpened)",
    "not event(JointBeaconRecordOpened)",
    "not event(JointOwnedAccepted)",
    "not event(JointCopiedKemAccepted)",
    "not attacker(MLDSA_JOINT_OWNED_INITIAL[])",
    "not attacker(MLDSA_JOINT_OWNED_RECORD[])",
    "not event(JointReplayRejected)",
    "not event(JointClassicalRecovered)",
)
VERDICTS = ("true",) * 7 + ("false",) * 9
VARIABLE = re.compile(
    r"\b(?:request|server_ml|init_hash|response|root|ad|assigned|initial|"
    r"seq|sender|receiver|plaintext)(?:_[0-9]+)?\b(?!\s*\()"
)
RESPONSE_VERIFIER = (
    "let verified_response_input = mldsa_verify(response_signature,\n"
    "    server_ml, mldsa_signing_context()) in"
)
RESPONSE_BYPASS = (
    "let verified_response_input = mldsa_server_input(expected_response_hash) in"
)
CONTROLS = (
    (
        "without-response-verifier-origin",
        "mldsa-joint-session.pvl",
        0,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
    (
        "without-response-verifier-session",
        "mldsa-joint-session.pvl",
        1,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
    (
        "without-response-verifier-secrecy",
        "mldsa-joint-session.pvl",
        6,
        RESPONSE_VERIFIER,
        RESPONSE_BYPASS,
    ),
    (
        "with-selected-kem-secret-compromise",
        "mldsa-joint-session.pvl",
        4,
        "event JointSessionCreated(selected_init);",
        "event JointSessionCreated(selected_init);\n  out(mldsa_joint_public_keys, pq_secret);",
    ),
    (
        "with-server-signing-key-compromise",
        "mldsa-joint-session.pvl",
        0,
        "let server_ml = mldsa_public(server_ml_secret) in\n  let beacon_ed = ed_public(identity_secret) in",
        "let server_ml = mldsa_public(server_ml_secret) in\n  out(mldsa_joint_public_keys, server_ml_secret);\n  let beacon_ed = ed_public(identity_secret) in",
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
