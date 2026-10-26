#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Build the authentication-only arbitrary-KEM view of the maintained roles.

The resulting process strengthens the adversary; it is not a secrecy model or
an IND-CCA idealization. Original non-KEM code and queried events are retained.
"""

from pathlib import Path
import re

HERE = Path(__file__).resolve().parent

KEM_BOUNDARY = """fun mlkem_public(bitstring): bitstring.
fun mlkem_ciphertext(bitstring, bitstring): bitstring.
fun mlkem_shared_secret(bitstring, bitstring): bitstring.
reduc forall secret_key: bitstring, coins: bitstring;
  mlkem_decapsulate(
    mlkem_ciphertext(mlkem_public(secret_key), coins),
    secret_key
  ) = mlkem_shared_secret(mlkem_public(secret_key), coins)."""


def without_comments(source):
    return re.sub(r"\(\*.*?\*\)", "", source, flags=re.S)


def compact(source):
    return re.sub(r"\s+", "", without_comments(source))


def replace_exact(source, old, new, count):
    if source.count(old) != count:
        raise ValueError(f"expected {count} occurrences of {old!r}")
    return source.replace(old, new)


def crypto(source):
    start = source.index("(* ML-KEM encapsulation")
    end = source.index("(* This constructor is referenced", start)
    if compact(source[start:end]) != compact(KEM_BOUNDARY):
        raise ValueError("ML-KEM boundary changed; review the controller projection")
    result = (
        source[:start]
        + (
            "(* No KEM algebra is available in this authentication-only view.\n"
            "   The controller chooses all KEM byte values and optional replies. *)\n\n"
        )
        + source[end:]
    )
    if re.search(r"\bmlkem_", without_comments(result)):
        raise ValueError("residual ML-KEM equation in authentication view")
    return result


def controlled_call(request, pattern, indent):
    """A failed optional reply terminates this local path after its observation."""
    return (
        f"{indent}event KemControllerRequested({request});\n"
        f"{indent}out(kem_controller, {request});\n"
        f"{indent}in(kem_controller, kem_reply: bitstring) [precise];\n"
        f"{indent}event KemControllerReturned({request}, kem_reply);\n"
        f"{indent}if kem_reply = kem_failure() then\n"
        f"{indent}  event KemControllerRejected({request})\n"
        f"{indent}else let {pattern} = kem_reply in\n"
    )


def environment(source):
    # Rename the fresh symbolic KEM-key binder to an origin handle. The handle
    # is public instrumentation, never a computational secret key encoding.
    source = replace_exact(source, "beacon_pq_secret", "beacon_kem_handle", 9)
    for prefix, count in (("", 2), ("main_", 1)):
        old = f"  let {prefix}beacon_pq = mlkem_public({prefix}beacon_kem_handle) in\n"
        source = replace_exact(
            source,
            old,
            controlled_call(
                f"kem_generate_request({prefix}beacon_kem_handle)",
                f"kem_generate_reply({prefix}beacon_pq: bitstring)",
                "  ",
            ),
            count,
        )
    for prefix, count in (("", 2), ("main_", 1)):
        old = (
            f"  let {prefix}kem_ciphertext = mlkem_ciphertext({prefix}beacon_pq, {prefix}kem_coins) in\n"
            f"  let {prefix}kem_secret = mlkem_shared_secret({prefix}beacon_pq, {prefix}kem_coins) in\n"
        )
        source = replace_exact(
            source,
            old,
            controlled_call(
                f"kem_encapsulation_request({prefix}beacon_pq)",
                f"kem_encapsulation_reply({prefix}kem_ciphertext: bitstring, {prefix}kem_secret: bitstring)",
                "  ",
            ),
            count,
        )
    for prefix in ("", "main_"):
        source = replace_exact(
            source,
            f"    let {prefix}kem_secret = mlkem_decapsulate({prefix}kem_ciphertext, {prefix}beacon_kem_handle) in\n",
            "",
            1,
        )
        # Actual native decapsulation precedes DH and the extracted pin check.
        # This stronger view also permits the request when point admission or
        # the pin would reject; the original pin still gates all target events.
        anchor = (
            f"  if {prefix}response_server_identity = {prefix}server_identity then\n"
        )
        source = replace_exact(
            source,
            anchor,
            controlled_call(
                f"kem_decapsulation_request({prefix}beacon_kem_handle, {prefix}beacon_pq, {prefix}kem_ciphertext)",
                f"kem_decapsulation_reply({prefix}kem_secret: bitstring)",
                "  ",
            )
            + anchor,
            1,
        )
    if re.search(r"\bmlkem_", without_comments(source)):
        raise ValueError("residual ML-KEM operation in authentication roles")
    return source


def authentication_queries(source):
    queries = re.findall(r"\bquery\b.*?\.", without_comments(source), flags=re.S)
    if len(queries) != 14:
        raise ValueError("expected the original fourteen main queries")
    if any(not query.startswith("query attacker(") for query in queries[:5]):
        raise ValueError("main secrecy query prefix changed")
    selected = queries[5:]
    antecedents = (
        "ServerAccepted",
        "ServerBundleAccepted",
        "ServerAccepted",
        "RegistrationConsumed",
        "ServerResponseAborted",
        "BeaconAuthenticatedRegistrationCompleted",
        "MessageReceived",
        "BeaconAuthenticatedRegistrationCompleted",
        "BeaconAuthenticatedRegistrationCompleted",
    )
    consequences = (
        "BeaconInitiated",
        "BeaconBundleInitiated",
        "RegistrationConsumed",
        "BeaconInitiated",
        "RegistrationConsumed",
        "AuthenticatedRegistrationRecordSent",
        "MessageSent",
        "ServerAuthenticatedSessionCommitted",
        "AuthenticatedRegistrationRecordSent",
    )
    for query, before, after in zip(selected, antecedents, consequences):
        events = re.findall(r"inj-event\((\w+)\(", query)
        if events != [before, after]:
            raise ValueError("original authentication event map changed")
    return "\n\n".join(selected) + "\n"


def generate(directory):
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "crypto.pvl").write_text(crypto((HERE / "crypto.pvl").read_text()))
    (directory / "environment.pvl").write_text(
        environment((HERE / "environment.pvl").read_text())
    )
    (directory / "queries.pvl").write_text(
        authentication_queries((HERE / "queries.pvl").read_text())
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    generate(parser.parse_args().directory)
