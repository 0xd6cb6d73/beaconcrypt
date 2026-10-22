#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check arbitrary registration admission and explicit model limitations.

Exact primary and summary results are checked independently. Negative controls
must reconstruct attacks, except the deliberately gated admission controls.
The baseline mutex uniqueness diagnostic is NOT a ProVerif security proof.
"""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
RID = "beaconcrypt_core__pqxdh__RegistrationId"
PAIR = lambda one: (
    f"{RID}(registration_identifier(ed_public(ADV_ID[]),x25519_public({one}[])))"
)
PRIMARY = [
    "event(RegistrationSetReturned(owner_2,attempt_1,rid_1)) ==> event(RegistrationSetConsumed(owner_2,attempt_1,rid_1))",
    "event(RegistrationSetConsumed(owner_2,attempt_1,rid_1)) ==> event(RegistrationSetFresh(owner_2,attempt_1,rid_1))",
    "event(RegistrationSetReplay(owner_2,attempt_1,rid_1)) ==> event(RegistrationSetConsumed(owner_2,prior,rid_1))",
    "event(RegistrationSetHonestAccepted(identity_3,init_1,origin_2)) ==> event(RegistrationSetHonestSigned(identity_3,init_1,origin_2))",
]
REACHABLE = [
    f"not event(RegistrationSetReturned(owner_2,attempt_1,{PAIR('ADV_ONE')}))",
    f"not (event(RegistrationSetConsumed(owner_2,first,{PAIR('ADV_ONE')})) && event(RegistrationSetConsumed(owner_2,second,{PAIR('ADV_OTHER')})))",
    "not event(RegistrationSetReplay(owner_2,attempt_1,rid_1))",
    "not event(RegistrationSetFailed(owner_2,attempt_1))",
    f"not (event(RegistrationSetFreshFailed(owner_2,failed,{PAIR('ADV_ONE')})) && event(RegistrationSetReturned(owner_2,attempt_1,{PAIR('ADV_ONE')})))",
]
UNIQUE = "event(RegistrationSetConsumed(owner_2,first,rid_1)) && event(RegistrationSetConsumed(owner_2,second,rid_1)) ==> first = second"
UNIQUE_QUERY = """set preciseActions = true.
query owner:bitstring, first:bitstring, second:bitstring, rid:beaconcrypt_core__pqxdh__t_RegistrationId;
 event(RegistrationSetConsumed(owner,first,rid)) && event(RegistrationSetConsumed(owner,second,rid)) ==> first = second.
"""


def exact_replace(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"negative-control anchor changed: {old!r}")
    return text.replace(old, new)


def check_output(output, queries, verdicts, traces):
    expected = [
        query
        + (f" is {verdict}." if verdict in {"true", "false"} else " cannot be proved.")
        for query, verdict in zip(queries, verdicts, strict=True)
    ]
    if output.count("Verification summary:") != 1:
        raise ValueError("missing or duplicated verification summary")
    primary, summary = output.split("Verification summary:")
    results = re.findall(r"^RESULT (.+)$", primary, re.M)
    reported = re.findall(r"^Query (.+)$", summary, re.M)
    if results != expected or reported != expected:
        raise ValueError(
            f"exact query/verdict mismatch\nexpected={expected!r}\nprimary={results!r}\nsummary={reported!r}"
        )
    if primary.count("A trace has been found.") != traces:
        raise ValueError("negative-control reconstructed trace count changed")
    if re.search(r"^Error:|^Warning:", output, re.M):
        raise ValueError("ProVerif reported an error or warning")


def check_source_order():
    """A drift check for the reviewed mapping, not a Rust/applied-pi compiler."""
    source = (HERE.parents[2] / "beaconcrypt/src/server.rs").read_text()
    start = source.index(
        "fn get_shared_secret(&mut self,",
        source.index("impl ProviderServer for Server {"),
    )
    end = source.index("fn build_registration_response(", start)
    body = source[start:end]
    tokens = [
        "let registration = decode_init(buffer)?;",
        "crypto_sign::PublicKey::from_bytes",
        "crypto_sign::verify(registration.pq_key,",
        "crypto_sign::verify(registration.pre_key,",
        "crypto_sign::verify(registration.one_time_key,",
        "verified_pqxdh::validate_init_kex(init_kex)",
        "verified_pqxdh::registration_id(&verified_registration)",
        "self.consumed_registrations.contains(&registration_id)",
        "verified_pqxdh::validate_registration_status(registration_status)",
        "self.consumed_registrations.try_reserve(1)",
        "verified_registration.beacon_prekey_public_key()",
        "verified_registration.beacon_one_time_public_key()",
        "crypto_kx::KeyPair::generate()",
        "crypto_kem::mlkem768::PublicKey::from_bytes(",
        "crypto_kem::mlkem768::encapsulate(&pq_pub)",
        "crypto_sign::ed25519_pk_to_curve25519(&remote_id)",
        "crypto_sign::ed25519_sk_to_curve25519(self.identity_sk())",
        "let dh1:",
        "let dh2:",
        "let dh3:",
        "let dh4:",
        "let mut secrets = shared_secrets(",
        "let accepted = verified_pqxdh::server_accept(",
        "zeroize_shared_secrets(&mut secrets)",
        "let (unchanged, mut pending) = accepted.ok()?;",
        "derive_root_key_input(pending.root_key_input_mut())?",
        "self.consumed_registrations.insert(registration_id)",
        "Some(RegistrationOutput {",
    ]
    positions = []
    for token in tokens:
        if token not in body:
            raise ValueError(f"native admission token changed: {token}")
        positions.append(body.index(token))
    if positions != sorted(positions) or len(set(positions)) != len(positions):
        raise ValueError("reviewed native admission order changed")
    if body.count("self.consumed_registrations.insert(") != 1:
        raise ValueError("native admission insertion count changed")


def run(proverif, model, queries, output, timeout):
    command = [proverif]
    for lib in [
        HERE / "production-transcript-interface.pvl",
        HERE / "crypto.pvl",
        HERE / "extraction/lib.pvl",
        HERE / "environment.pvl",
        model,
        queries,
    ]:
        command.extend(["-lib", str(lib)])
    command.append(str(HERE / "registration-set-admission.pv"))
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    output.write_text(completed.stdout)
    if completed.returncode:
        raise ValueError(f"ProVerif exited {completed.returncode}: {output}")
    return completed.stdout


def check(proverif, logdir, timeout):
    check_source_order()
    source = (HERE / "registration-set-admission.pvl").read_text()
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-registration-set-"
    ) as directory:
        scratch = Path(directory)
        gated = scratch / "gated.pvl"
        gated.write_text(
            exact_replace(
                source,
                "    let rid = beaconcrypt_core__pqxdh__registration_id(verified) in",
                "    get registration_set_origin(=identity, admission_origin:bitstring) in\n"
                "    let rid = beaconcrypt_core__pqxdh__registration_id(verified) in",
            )
        )
        unlocked = scratch / "unlocked.pvl"
        unlocked.write_text(
            exact_replace(source, "  in(mutex, =registration_set_mutex());\n", "")
        )
        unique = scratch / "unique.pvl"
        unique.write_text(UNIQUE_QUERY)
        model = HERE / "registration-set-admission.pvl"
        scenarios = [
            (
                "correspondences",
                model,
                HERE / "registration-set-admission-queries.pvl",
                PRIMARY,
                ["true"] * 4,
                0,
            ),
            (
                "reachability",
                model,
                HERE / "registration-set-admission-reachability.pvl",
                REACHABLE,
                ["false"] * 5,
                5,
            ),
            (
                "origin-gated-control",
                gated,
                HERE / "registration-set-admission-reachability.pvl",
                REACHABLE,
                ["true", "true", "false", "false", "true"],
                2,
            ),
            ("unlocked-control", unlocked, unique, [UNIQUE], ["false"], 1),
            ("mutex-inconclusive-diagnostic", model, unique, [UNIQUE], ["unknown"], 0),
        ]
        for name, library, queryfile, expected, verdicts, traces in scenarios:
            output = run(
                proverif, library, queryfile, logdir / (name + ".log"), timeout
            )
            check_output(output, expected, verdicts, traces)
            print(
                f"{name}: {len(expected)} exact results, {traces} reconstructed traces",
                flush=True,
            )
    print(
        "Registration admission: 9 baseline results, 6 negative-control results; mutex uniqueness remains explicitly inconclusive in ProVerif (native Lean proof supplies it)."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        check(args.proverif, args.log_dir, args.timeout)
    else:
        with tempfile.TemporaryDirectory(
            prefix="beaconcrypt-registration-set-logs-"
        ) as directory:
            check(args.proverif, Path(directory), args.timeout)


if __name__ == "__main__":
    main()
