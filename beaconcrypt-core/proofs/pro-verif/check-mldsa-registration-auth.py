#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check focused authentication consequences of an assumed ideal ML-DSA interface."""

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
)
MODEL_FILES = (
    "mldsa-auth.pvl",
    "mldsa-registration-auth.pvl",
    "mldsa-registration-auth.pv",
)
MODEL_SHA256 = {
    "mldsa-auth.pvl": "09c409113e49aa61f4f7d777d30f3778a743ccab7a47cf9d7c506b146d29e403",
    "mldsa-registration-auth.pvl": "ce5ee0e2e07d642a2c3aa12b2789d981c402bb7ca7f7c5c9466322832656408a",
    "mldsa-registration-auth.pv": "d5ed999eac22acf788d7e4166ac1f233ddede02c916f55fd32fac358e5ad8bcf",
}
PRIMARY = (
    "event(MldsaHonestInitAccepted(agent_ml,server_ml,init_hash,classical_init)) ==> "
    "event(MldsaInitSigned(agent_ml,server_ml,init_hash,classical_init))",
    "event(MldsaResponseAccepted(server_ml,init_hash,response)) ==> "
    "event(MldsaResponseSigned(server_ml,init_hash,response))",
    "not event(MldsaHonestResponseVerified)",
    "not event(MldsaOwnedKeyAccepted)",
    "not event(MldsaCompromisedAgentAccepted)",
    "not event(MldsaCompromisedServerAccepted)",
    "not event(MldsaAdOpened)",
    "not event(MldsaWrongServerAdOpened)",
    "not event(MldsaWrongAgentAdOpened)",
    "not event(MldsaWrongRoleAccepted)",
    "not event(MldsaWrongContextAccepted)",
    "not event(MldsaWrongRequestAccepted)",
)
VERDICTS = (
    "true",
    "true",
    "false",
    "false",
    "false",
    "false",
    "false",
    "true",
    "true",
    "true",
    "true",
    "true",
)
VARIABLE = re.compile(
    r"\b(?:agent_ml|server_ml|init_hash|classical_init|response)(?:_[0-9]+)?\b(?!\s*\()"
)
CONTROLS = (
    (
        "without-init-verifier",
        0,
        "let verified_init_input = mldsa_verify(candidate_signature,\n"
        "        candidate_ml, mldsa_signing_context()) in",
        "let verified_init_input = mldsa_beacon_input(candidate_hash) in",
    ),
    (
        "without-response-verifier",
        1,
        "let verified_response_input = mldsa_verify(response_signature,\n"
        "        server_ml, mldsa_signing_context()) in",
        "let verified_response_input = mldsa_server_input(expected_response_hash) in",
    ),
)


def canonical_query(query):
    """Only bound-variable alpha suffixes may vary; preserve equality patterns."""
    names = {}

    def replace(match):
        name = match.group()
        if name not in names:
            names[name] = "V" + str(len(names))
        return names[name]

    return VARIABLE.sub(replace, query)


def check_output(output, queries, verdicts, traces):
    if len(queries) != len(verdicts) or set(verdicts) - {"true", "false"}:
        raise ValueError("invalid exact expectation roster")
    if re.search(r"^(?:Warning|Error|Fatal|Timeout)\b", output, re.M | re.I):
        raise ValueError("verifier warning or error")
    if "assuming a hypothesis" in output:
        raise ValueError("unconfirmed attack trace")
    if output.count("Verification summary:") != 1:
        raise ValueError("missing or duplicate verification summary")
    before, after = output.split("Verification summary:")
    if (
        output.count("A trace has been found.") != traces
        or "A trace has been found." in after
    ):
        raise ValueError("missing, extra or misplaced reconstructed trace")
    expected = [
        canonical_query(q) + " is " + v + "."
        for q, v in zip(queries, verdicts, strict=True)
    ]
    result = [
        canonical_query(line[7:])
        for line in before.splitlines()
        if line.startswith("RESULT ")
    ]
    summary = [
        canonical_query(line[6:])
        for line in after.splitlines()
        if line.startswith("Query ")
    ]
    if result != expected or summary != expected:
        raise ValueError(
            "missing, reordered, duplicated or changed exact query/verdict"
        )
    if any(line.startswith("RESULT ") for line in after.splitlines()) or any(
        line.startswith("Query ") for line in before.splitlines()
    ):
        raise ValueError("result/summary phase changed")


def digest(text):
    return hashlib.sha256(
        re.sub(r"\s+", "", re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)).encode()
    ).hexdigest()


def validate_models(directory=HERE):
    if set(MODEL_SHA256) != set(MODEL_FILES):
        raise ValueError("incomplete reviewed model roster")
    for name in MODEL_FILES:
        if digest((directory / name).read_text()) != MODEL_SHA256[name]:
            raise ValueError("review changed ML-DSA model: " + name)


def exact_replace(source, old, new):
    if source.count(old) != 1:
        raise ValueError("missing or ambiguous negative-control anchor")
    return source.replace(old, new)


def run(proverif, model, queries, log, timeout):
    paths = [HERE / name for name in LIBRARIES] + [model, queries]
    command = [proverif]
    for path in paths[:-1]:
        command += ["-lib", str(path)]
    command.append(str(paths[-1]))
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    try:
        result = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        log.write_bytes(error.stdout or b"")
        raise ValueError("verifier timeout: " + str(log)) from error
    log.write_text(result.stdout)
    if result.returncode:
        raise ValueError("verifier failure: " + str(log))
    if before != {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}:
        raise ValueError("model changed while verifier ran")
    return result.stdout


def check(proverif, logdir, timeout):
    validate_models()
    logdir.mkdir(parents=True, exist_ok=True)
    model = HERE / "mldsa-registration-auth.pvl"
    queries = HERE / "mldsa-registration-auth.pv"
    output = run(
        proverif, model, queries, logdir / "mldsa-registration-auth.log", timeout
    )
    check_output(output, PRIMARY, VERDICTS, VERDICTS.count("false"))
    source = model.read_text()
    query_source = queries.read_text()
    declarations, process = query_source.split("process\n")
    declarations = (
        re.sub(r"\(\*.*?\*\)", "", declarations, flags=re.S).strip().split("query ")[1:]
    )
    for name, position, old, new in CONTROLS:
        changed = logdir / (name + ".pvl")
        changed.write_text(exact_replace(source, old, new))
        control_queries = logdir / (name + ".pv")
        control_queries.write_text(
            "query " + declarations[position] + "\nprocess\n" + process
        )
        output = run(
            proverif, changed, control_queries, logdir / (name + ".log"), timeout
        )
        check_output(output, (PRIMARY[position],), ("false",), 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--logdir", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    try:
        check(args.proverif, args.logdir, args.timeout)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + "\n")
    print(
        "ML-DSA assumed-interface profile: 12 exact verdicts and 2 reconstructed verifier-bypass controls passed"
    )


if __name__ == "__main__":
    main()
