#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact unbounded response queries, supplied-root tail controls and limits.

maxHyp is a sound Horn overapproximation, not a finite schedule restriction.
Sensitivity controls expecting unknown are NOT reconstructed attacks.
"""

import argparse
import importlib.util
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "registration_set_checker", HERE / "check-registration-set.py"
)
ADMISSION = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADMISSION)
PRIMARY = [
    "event(RegistrationResponseConsumed(owner_3,token_1)) ==> event(RegistrationSetConsumed(owner_3,token_1,rid_2))",
    "event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> next_1 = before_1 + 1",
    "event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> event(RegistrationResponseInnerWritten(owner_3,token_1,assigned_2,plaintext_1,frame_1))",
    "event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> assigned_2 = registration_response_identifier(next_1)",
    "event(RegistrationResponseCompleted(owner_3,token_1,before_1,after,false)) ==> after = before_1",
    "event(RegistrationResponseCompleted(owner_3,token_1,before_1,after,true)) ==> after = before_1 + 1",
    "event(RegistrationResponseInstalled(owner_3,token_1,assigned_2,ad,send,receive)) ==> event(RegistrationResponsePrepared(owner_3,token_1,next_1,root_3,hkdf_first_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)),hkdf_second_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)))) && assigned_2 = registration_response_identifier(next_1) && send = hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain)),symmetric_ratchet_domain)) && receive = hkdf_second_32(hkdf_sha512_no_salt(root_3,symmetric_ratchet_domain))",
    "event(RegistrationResponsePublished(owner_3,token_1,before_1,next_1,assigned_2,plaintext_1,frame_1,response_1)) ==> plaintext_1 = registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(assigned_2)),registration_response_nonempty(suffix))",
]

TAIL = [
    "not event(RegistrationResponsePublished(owner_2,token_2,before_1,next_1,assigned_1,plaintext_1,frame_1,response_1))",
    "not event(RegistrationResponseInnerWritten(owner_2,token_2,assigned_1,plaintext_1,frame_1))",
    "not event(RegistrationResponseCompleted(owner_2,token_2,before_1,after,false))",
]
REACHABLE = "not " + PRIMARY[1].split(" ==> ")[0]


def check_source_order():
    """Reviewed textual drift check only; this is not a Rust/applied-pi compiler."""
    ADMISSION.check_source_order()
    source = (HERE.parents[2] / "beaconcrypt/src/server.rs").read_text()
    start = source.index(
        "fn build_registration_response(",
        source.index("impl ProviderServer for Server {"),
    )
    body = source[start : source.index("\n\t}", start)]
    tokens = [
        "let RegistrationOutput {",
        "verified_pqxdh::server_next_key_id(control)",
        "self.known_ids.contains_key(&next_key_id)",
        "verified_pqxdh::server_prepare_commit(",
        "crypto_sign::PublicKey::from_bytes(candidate.beacon_identity_public_key())",
        "self.known_ids.try_reserve(1)",
        "start_server_candidate_ratchet_kdf(",
        "RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
        "data.unwrap_or(REGISTRATION_WITNESS)",
        "if plaintext.is_empty()",
        "REGISTRATION_KEY_ID_BINDING_SIZE.checked_add(plaintext.len())",
        ".try_reserve_exact(authenticated_len)",
        "candidate.key_id_binding().as_bytes()",
        "authenticated_plaintext.extend_from_slice(plaintext)",
        "encrypt_message_with_ratchet(",
        "authenticated_plaintext.zeroize()",
        "let encrypted = encrypted?;",
        "bundle.set_key_id(remote_kid)",
        "bundle.set_ephemeral_key(candidate.ephemeral_public_key())",
        "bundle.set_identity_key(candidate.server_identity_public_key())",
        "bundle.set_kem_cipher_text(candidate.kem_ciphertext())",
        "bundle.set_app_cipher_text(&encrypted.ciphertext)",
        "capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner())",
        "verified_pqxdh::server_commit(candidate)",
        ".insert(remote_kid, EstablishedRemote::new(public_key, ratchet))",
        "self.control = next_control",
        "Some(RegResponse {",
    ]
    positions = [body.index(token) for token in tokens]
    if positions != sorted(positions) or len(set(positions)) != len(positions):
        raise ValueError("reviewed native response order changed")
    model = (HERE / "registration-set-response.pvl").read_text()
    controls = [
        "in(mutex, =registration_set_mutex());",
        "in(counter, before: nat);",
        "get registration_set_pending(=owner, =token,",
        "get registration_response_used(=owner, =token)",
        "insert registration_response_used(owner, token);",
        "if before < limit then",
        "let next = before + 1 in",
        "get registration_response_peers(=owner, =assigned,",
    ]
    positions = [
        model.index(token, model.index("let RegistrationResponseBuilder"))
        for token in controls
    ]
    if positions != sorted(positions):
        raise ValueError("reviewed pending/counter admission order changed")
    if "new assigned" in model or "registration_set_origin" in model:
        raise ValueError("response IDs/origins incorrectly control admission")
    if "registration_response_nonempty(registration_response_witness())" not in model:
        raise ValueError("default and supplied witness byte aliases were separated")


def run(proverif, model, queries, process, log, timeout):
    command = [proverif]
    for library in [
        "production-transcript-interface.pvl",
        "crypto.pvl",
        "extraction/lib.pvl",
        "environment.pvl",
        "registration-set-admission.pvl",
    ]:
        command += ["-lib", str(HERE / library)]
    command += ["-lib", str(model), "-lib", str(queries), str(process)]
    completed = subprocess.run(
        command,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    log.write_text(completed.stdout)
    if completed.returncode:
        raise ValueError(f"ProVerif exited {completed.returncode}: {log}")
    return completed.stdout


def check(proverif, logdir, timeout):
    check_source_order()
    model = HERE / "registration-set-response.pvl"
    queries = HERE / "registration-set-response-queries.pvl"
    process = HERE / "registration-set-response.pv"
    output = run(
        proverif, model, queries, process, logdir / "correspondences.log", timeout
    )
    ADMISSION.check_output(output, PRIMARY, ["true"] * 8, 0)
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-registration-response-"
    ) as directory:
        scratch = Path(directory)
        source = model.read_text()
        mutations = [
            (
                "counter-jump",
                "let next = before + 1 in",
                "let next = before + 2 in",
                [1, 5],
            ),
            (
                "wrong-chain",
                "let advanced = ratchet_next(send_chain) in",
                "let advanced = receive_chain in",
                [6],
            ),
            (
                "wrong-binding",
                "RegistrationKeyIdBinding(key_id_encoding(assigned))",
                "RegistrationKeyIdBinding(key_id_encoding(server_id))",
                [7],
            ),
            (
                "failure-counter",
                "mutex, counter, before, before,\n    false",
                "mutex, counter, before, before + 1,\n    false",
                [4],
            ),
        ]
        for name, old, new, unknown in mutations:
            changed = scratch / (name + ".pvl")
            changed.write_text(ADMISSION.exact_replace(source, old, new))
            expected = PRIMARY
            if name == "failure-counter":
                expected = [
                    query.replace(",after,", ",after_13,").replace(
                        "after =", "after_13 ="
                    )
                    for query in PRIMARY
                ]
            output = run(
                proverif, changed, queries, process, logdir / (name + ".log"), timeout
            )
            ADMISSION.check_output(
                output,
                expected,
                ["unknown" if i in unknown else "true" for i in range(8)],
                0,
            )
        tail = (HERE / "registration-set-response-tail.pv").read_text()
        cases = [
            ("success", "registration_response_nonempty(CONTROL_PAYLOAD)", 0),
            ("default", "registration_response_default_payload()", 0),
            ("empty", "registration_response_empty()", 0),
            ("malformed", "CONTROL_PAYLOAD", 0),
        ]
        cases += [
            (
                f"failure-{stage}",
                "registration_response_nonempty(CONTROL_PAYLOAD)",
                stage,
            )
            for stage in range(1, 8)
        ]
        for name, data, stage in cases:
            fixture = scratch / (name + ".pv")
            fixture.write_text(
                ADMISSION.exact_replace(
                    tail,
                    "registration_response_nonempty(CONTROL_PAYLOAD),0)",
                    f"{data},{stage})",
                )
            )
            if name in {"success", "default"}:
                verdicts, traces = ["false", "false", "true"], 2
            elif stage == 7:
                verdicts, traces = ["true", "false", "false"], 2
            else:
                verdicts, traces = ["true", "true", "false"], 1
            output = run(
                proverif,
                model,
                HERE / "registration-set-response-tail-queries.pvl",
                fixture,
                logdir / ("tail-" + name + ".log"),
                timeout,
            )
            ADMISSION.check_output(output, TAIL, verdicts, traces)
        diagnostic = scratch / "reachability.pvl"
        diagnostic.write_text(
            "set preciseActions=false.\nset maxHyp=2.\nquery owner:bitstring, token:bitstring, before:nat, next:nat, assigned:key_id, plaintext:bitstring, frame:bitstring, response:bitstring;\n event(RegistrationResponsePublished(owner,token,before,next,assigned,plaintext,frame,response)).\n"
        )
        output = run(
            proverif,
            model,
            diagnostic,
            process,
            logdir / "reachability-inconclusive.log",
            timeout,
        )
        ADMISSION.check_output(output, [REACHABLE], ["unknown"], 0)
    print(
        "Response boundary: eight unbounded-process correspondences; 33 finite tail-control results with 14 reconstructed traces; 32 sensitivity results (five explicitly unknown); full-process publication reachability remains explicitly inconclusive."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        check(args.proverif, args.log_dir, args.timeout)
    else:
        with tempfile.TemporaryDirectory(
            prefix="beaconcrypt-response-logs-"
        ) as directory:
            check(args.proverif, Path(directory), args.timeout)


if __name__ == "__main__":
    main()
