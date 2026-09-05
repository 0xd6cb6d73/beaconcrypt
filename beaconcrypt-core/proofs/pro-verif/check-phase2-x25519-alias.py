#!/usr/bin/env python3
"""Check the exact registration correspondences with native X25519 aliases."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def without_comments(source: str) -> str:
    return re.sub(r"\(\*.*?\*\)", "", source, flags=re.S)


def compact(source: str) -> str:
    return re.sub(r"\s+", "", without_comments(source))


EXPECTED_X25519 = """
fun x25519_public(bitstring): bitstring.
reduc forall identity_secret: bitstring;
  x25519_public_from_ed(ed_public(identity_secret)) =
  x25519_public(identity_secret).
fun x25519_shared(bitstring, bitstring): bitstring [private].
reduc forall server_secret: bitstring, beacon_secret: bitstring;
  x25519_server_dh(server_secret, x25519_public(beacon_secret)) =
  x25519_shared(server_secret, beacon_secret).
reduc forall beacon_secret: bitstring, server_secret: bitstring;
  x25519_beacon_dh(beacon_secret, x25519_public(server_secret)) =
  x25519_shared(server_secret, beacon_secret).
"""


def selected_queries(directory: Path) -> str:
    source = without_comments(
        (directory / "exact-registration-origin-queries.pvl").read_text()
    )
    queries = re.findall(r"\bquery\b.*?\.", source, flags=re.S)
    selected = [
        query
        for query in queries
        if "inj-event(BeaconCommitted(" in query
        or "inj-event(BeaconRegistrationCompleted(" in query
    ]
    if len(selected) != 3:
        raise ValueError("expected exactly three unchanged registration queries")
    destinations = (
        "inj-event(ServerCommitted(transcript))",
        "inj-event(ServerRegistrationSessionCommitted(main_agreement,main_server_assigned))",
        "inj-event(RegistrationRecordSent(main_agreement,main_sequence,main_payload,main_frame,main_server_assigned))",
    )
    if any(
        destination not in compact(query)
        for query, destination in zip(selected, destinations)
    ):
        raise ValueError(
            "registration correspondence destination changed; review required"
        )
    return "\n\n".join(selected) + "\n"


def alias_crypto(directory: Path) -> str:
    source = (directory / "crypto.pvl").read_text()
    start = source.index("(* X25519.")
    finish = source.index("(* ML-KEM encapsulation", start)
    if compact(source[start:finish]) != compact(EXPECTED_X25519):
        raise ValueError("baseline X25519 boundary changed; review required")
    replacement = (directory / "phase2-x25519-alias-theory.pvl").read_text()
    return source[:start] + replacement + source[finish:]


def selected_projected_queries(directory: Path) -> str:
    source = without_comments((directory / "queries.pvl").read_text())
    queries = re.findall(r"\bquery\b.*?\.", source, flags=re.S)
    selected = [
        query
        for query in queries
        if "inj-event(BeaconAuthenticatedRegistrationCompleted(" in query
    ]
    if len(selected) != 3:
        raise ValueError("expected exactly three projected registration queries")
    destinations = (
        "inj-event(AuthenticatedRegistrationRecordSent(main_agreement,first_sequence(),main_payload,main_frame,main_claimed))",
        "inj-event(ServerAuthenticatedSessionCommitted(main_agreement,main_server_assigned))",
        "inj-event(AuthenticatedRegistrationRecordSent(main_agreement,main_sequence,main_payload,main_frame,main_server_assigned))",
    )
    if any(
        destination not in compact(query)
        for query, destination in zip(selected, destinations)
    ):
        raise ValueError(
            "projected registration correspondence destination changed; review required"
        )
    return "\n\n".join(selected) + "\n"


PROJECTED_RESULTS = (
    "RESULT inj-event(BeaconAuthenticatedRegistrationCompleted(main_agreement,first_sequence,main_payload,main_frame,main_claimed)) ==> inj-event(AuthenticatedRegistrationRecordSent(main_agreement,first_sequence,main_payload,main_frame,main_claimed)) is true.",
    "RESULT inj-event(BeaconAuthenticatedRegistrationCompleted(main_agreement,main_sequence,main_payload,main_frame,main_claimed)) ==> inj-event(ServerAuthenticatedSessionCommitted(main_agreement,main_server_assigned)) is true.",
    "RESULT inj-event(BeaconAuthenticatedRegistrationCompleted(main_agreement,main_sequence,main_payload,main_frame,main_claimed)) ==> inj-event(AuthenticatedRegistrationRecordSent(main_agreement,main_sequence,main_payload,main_frame,main_server_assigned)) is true.",
)


def check_projected_run(output: str) -> None:
    results = tuple(line for line in output.splitlines() if line.startswith("RESULT "))
    if results != PROJECTED_RESULTS:
        raise ValueError(
            f"expected all three exact projected correspondences: {results}"
        )


def check_run(output: str, expected: str) -> None:
    results = [
        line for line in output.splitlines() if line.startswith("RESULT inj-event(")
    ]
    if len(results) != 3 or any(
        not line.endswith(f" is {expected}.") for line in results
    ):
        raise ValueError(
            f"expected exactly three {expected} correspondence results: {results}"
        )
    destinations = (
        "ServerCommitted",
        "ServerRegistrationSessionCommitted",
        "RegistrationRecordSent",
    )
    if any(
        f"==> inj-event({destination}(" not in result
        for destination, result in zip(destinations, results)
    ):
        raise ValueError(
            "missing, duplicated, reordered, or changed correspondence result"
        )
    if expected == "false":
        traces = re.findall(
            r"A more detailed output of the traces.*?A trace has been found\.",
            output,
            flags=re.S,
        )
        if len(traces) != 3:
            raise ValueError(
                "a concrete trace must be reconstructed for each false correspondence"
            )
        if any(
            not any(
                line.startswith("in(c, kex_response(")
                and "x25519_flip_high_bit(" in line
                and "x25519_high_bit_alias(" in line
                for line in trace.splitlines()
            )
            for trace in traces
        ):
            raise ValueError(
                "the reconstructed counterexample must use the public encoding alias"
            )


def self_test() -> None:
    destinations = (
        "ServerCommitted",
        "ServerRegistrationSessionCommitted",
        "RegistrationRecordSent",
    )
    lines = [
        f"RESULT inj-event(BeaconCommitted(t)) ==> inj-event({destination}(t)) is false."
        for destination in destinations
    ]
    evidence = (
        "\nA more detailed output of the traces is available with\n"
        "in(c, kex_response(x25519_flip_high_bit(p))) with p = x25519_high_bit_alias(s)\n"
        "A trace has been found.\n"
    ) * 3
    valid = "\n".join(lines) + evidence
    check_run(valid, "false")
    check_run("\n".join(lines).replace("false.", "true."), "true")
    invalid = (
        "\n".join(lines[:2]) + evidence,
        valid.replace("false.", "true.", 1),
        "\n".join([lines[0], lines[0], lines[2]]) + evidence,
        valid.replace("A trace has been found.", "No reconstructed trace."),
        valid.replace("x25519_flip_high_bit", "not_the_alias_operation"),
    )
    for mutated in invalid:
        try:
            check_run(mutated, "false")
        except ValueError:
            continue
        raise AssertionError("negative result-checker control was accepted")
    print("phase2-x25519-alias checker: five negative controls rejected")
    projected = "\n".join(PROJECTED_RESULTS)
    check_projected_run(projected)
    invalid_projected = (
        "\n".join(PROJECTED_RESULTS[:2]),
        projected.replace("true.", "false.", 1),
        projected.replace("true.", "unknown.", 1),
        "\n".join((PROJECTED_RESULTS[0], PROJECTED_RESULTS[0], PROJECTED_RESULTS[2])),
        projected.replace(
            "main_claimed)) is true.", "main_server_assigned)) is true.", 1
        ),
        projected + "\nRESULT Observational equivalence is true.",
    )
    for mutated in invalid_projected:
        try:
            check_projected_run(mutated)
        except ValueError:
            continue
        raise AssertionError("negative projected-result control was accepted")
    print("projected registration checker: six negative controls rejected")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    self_test()
    directory = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix="beaconcrypt-phase2-alias-") as temporary:
        work = Path(temporary)
        queries = work / "exact-registration-queries.pvl"
        queries.write_text(selected_queries(directory))
        projected_queries = work / "projected-registration-queries.pvl"
        projected_queries.write_text(selected_projected_queries(directory))
        alias = work / "crypto-with-x25519-aliases.pvl"
        alias.write_text(alias_crypto(directory))
        for label, crypto, query_source, expected, projected in (
            ("canonical", directory / "crypto.pvl", queries, "true", False),
            ("alias", alias, queries, "false", False),
            (
                "projected-canonical",
                directory / "crypto.pvl",
                projected_queries,
                "true",
                True,
            ),
            ("projected-alias", alias, projected_queries, "true", True),
        ):
            command = [args.proverif]
            for library in (
                directory / "production-transcript-interface.pvl",
                crypto,
                directory / "extraction/lib.pvl",
                directory / "environment.pvl",
                query_source,
            ):
                command.extend(("-lib", str(library)))
            command.append(str(directory / "phase2-x25519-alias-control.pv"))
            result = subprocess.run(
                command,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=args.timeout,
                check=True,
            )
            if args.output_dir is not None:
                args.output_dir.mkdir(parents=True, exist_ok=True)
                (args.output_dir / f"{label}.log").write_text(result.stdout)
            if projected:
                check_projected_run(result.stdout)
            else:
                check_run(result.stdout, expected)
            print(
                f"phase2-x25519-alias {label}: three checked correspondences {expected}"
            )


if __name__ == "__main__":
    main()
