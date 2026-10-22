#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check local replicated Beacon correspondences and concrete active-tail controls.

The private-token prior-attempt diagnostic remains unknown. Finite tail traces
are separate from the unbounded correspondences and are not authentication.
"""

import argparse
import importlib.util
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "registration_set_checker", HERE / "check-registration-set.py"
)
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
PRIMARY = [
    "event(RegistrationBeaconReturned(owner_2,attempt_2,payload)) ==> event(RegistrationBeaconAttempt(owner_2,attempt_2,raw_1))",
    "event(RegistrationBeaconCommitted(owner_2,attempt_2,raw_1,assigned_1,ad,payload,send_1,receive_1,cache)) ==> event(RegistrationBeaconOpened(owner_2,attempt_2,first_sequence,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(assigned_1)),registration_response_nonempty(payload)),frame_1))",
    "event(RegistrationBeaconCommitted(owner_2,attempt_2,raw_1,assigned_1,ad,payload,send_1,receive_1,cache)) ==> event(RegistrationBeaconPrepared(owner_2,attempt_2,root_1,send_1,initial)) && event(RegistrationBeaconRawPlan(owner_2,attempt_2,first_sequence,material_52,receive_1,cache)) && cache = receive_cache_empty",
    "event(RegistrationBeaconFailed(owner_2,attempt_2)) ==> event(RegistrationBeaconAttempt(owner_2,attempt_2,raw_1))",
    "event(RegistrationBeaconDhComplete(owner_2,attempt_2,server)) ==> event(RegistrationBeaconDecapsulated(owner_2,attempt_2,ciphertext_1))",
    "event(RegistrationBeaconOpened(owner_2,attempt_2,target_2,opened_52,frame_1)) ==> event(RegistrationBeaconRawPlan(owner_2,attempt_2,target_2,material_52,next_52,skipped_1327))",
    "event(RegistrationBeaconClosedRejected(owner_2,attempt_2)) ==> event(RegistrationBeaconAttempt(owner_2,prior,raw_1))",
    "event(RegistrationBeaconPinRejected(owner_2,attempt_2,server)) ==> event(RegistrationBeaconDhComplete(owner_2,attempt_2,server)) && event(RegistrationBeaconSharedCleared(owner_2,attempt_2))",
    "event(RegistrationBeaconCommitted(owner_2,attempt_2,raw_1,assigned_1,ad,payload,send_1,receive_1,cache)) ==> event(RegistrationBeaconPrepared(owner_2,attempt_2,root_1,send_1,hkdf_first_32(hkdf_sha512_no_salt(root_1,symmetric_ratchet_domain)))) && send_1 = hkdf_second_32(hkdf_sha512_no_salt(root_1,symmetric_ratchet_domain)) && receive_1 = hkdf_second_32(hkdf_sha512_no_salt(hkdf_first_32(hkdf_sha512_no_salt(root_1,symmetric_ratchet_domain)),symmetric_ratchet_domain)) && cache = receive_cache_empty",
]
VERDICTS = ["true"] * 6 + ["unknown", "true", "true"]
TAIL = [
    "not event(RegistrationBeaconControlFirstSuccess)",
    "not event(RegistrationBeaconControlFirstFailure)",
    "not event(RegistrationBeaconControlRetrySuccess)",
    "not event(RegistrationBeaconControlRetryFailure)",
    "not event(RegistrationBeaconOpened(owner,attempt,target,opened,frame))",
    "not event(RegistrationBeaconPinRejected(owner,attempt,server))",
    "not event(RegistrationBeaconDhComplete(owner,attempt,server))",
    "not event(RegistrationBeaconSharedCleared(owner,attempt))",
]
VARIABLE = re.compile(
    r"\b(?:owner|attempt|payload|raw|assigned|ad|send|receive|cache|frame|root|initial|material|server|ciphertext|target|opened|next|skipped|prior)(?:_[0-9]+)?\b(?!\s*\()"
)


def canonical_query(query):
    """Ignore only bound-variable alpha names, preserving equality/distinctness."""
    names = {}

    def replace(match):
        token = match.group()
        if token not in names:
            names[token] = "V" + str(len(names))
        return names[token]

    return VARIABLE.sub(replace, query)


def check_output(output, queries, verdicts, traces):
    # Reconstructed traces belong before the summary, never after it.
    if output.count("A trace has been found.") != traces:
        raise ValueError("unexpected reconstructed trace outside the result phase")
    # Normalize only query lines, never constants, verdicts or trace receipts.
    normalized = re.sub(
        r"^(RESULT |Query )(.+)$",
        lambda m: m[1] + canonical_query(m[2]),
        output,
        flags=re.M,
    )
    BASE.check_output(
        normalized, [canonical_query(q) for q in queries], verdicts, traces
    )


def ordered(text, tokens, label):
    positions = [text.index(token) for token in tokens]
    if positions != sorted(positions) or len(set(positions)) != len(positions):
        raise ValueError("reviewed " + label + " order changed")


def check_source_order():
    """Reviewed drift check, not a Rust/applied-pi compiler."""
    source = (HERE.parents[2] / "beaconcrypt/src/beacon.rs").read_text()
    begin = source.index(
        "fn finish_registration(&mut self, bytes: &[u8])",
        source.index("impl ProviderBeacon for Beacon {"),
    )
    body = source[begin : source.index("\n\t}\n}", begin)]
    ordered(
        body,
        [
            "let control = match &self.state",
            "let response = decode_response(bytes)?;",
            "response.kem_cipher_text",
            "response.ephemeral_key",
            "response.identity_key",
            "ed25519_pk_to_curve25519",
            "ed25519_sk_to_curve25519",
            "mlkem768::decapsulate",
            "let dh1:",
            "let dh2:",
            "let dh3:",
            "let dh4:",
            "response.key_id",
            "beacon_prepare_finish",
            "zeroize_shared_secrets",
            "derive_root_key_input",
            "start_beacon_candidate_ratchet_kdf",
            "finish_initial_ratchet_kdf",
            "decrypt_registration_message_with_ratchet(",
            "response.app_cipher_text",
            "if decrypted.seq != 1",
            "authenticated_plaintext.len() <=",
            "authenticated_plaintext.split_off",
            "authenticate_registration_key_id_binding",
            "let Some((authenticated",
            "if self.server_kid()",
            "if self.server_id.as_bytes()",
            "self.identity_key_kid =",
            "self.state = BeaconState::Established",
            "Some(plaintext)",
        ],
        "Beacon source",
    )
    if body.count("self.abort_registration(control)") != 3:
        raise ValueError("active source failure/outer-pin abort changed")
    model = (HERE / "registration-beacon-admission.pvl").read_text()
    owner = model[model.index("let RegistrationBeaconOwner(") :]
    ordered(
        owner,
        [
            "new identity_secret",
            "new prekey_secret",
            "new pq_secret",
            "new one_time_secret",
            "sign(tag_x25519_prekey",
            "sign(tag_x25519_one_time",
            "sign(tag_mlkem768",
            "in(owner,",
            "in(token,",
            "event RegistrationBeaconAttempt",
            "RegistrationBeaconPrepare",
        ],
        "Beacon owner",
    )
    prepare = model[
        model.index("let RegistrationBeaconPrepare(") : model.index(
            "let RegistrationBeaconOwner("
        )
    ]
    ordered(
        prepare,
        [
            "x25519_public_from_ed",
            "mlkem_decapsulate",
            "let dh1",
            "let dh2",
            "let dh3",
            "let dh4",
            "RegistrationBeaconDhComplete",
            "RegistrationBeaconSharedCleared",
            "if server_identity = pinned_identity",
            "build_root_key_input",
            "let root = pqxdh_root",
            "RegistrationBeaconAfterRoot",
        ],
        "Beacon preparation",
    )
    opening = model[
        model.index("let RegistrationBeaconOpen(") : model.index(
            "let RegistrationBeaconAfterRoot("
        )
    ]
    ordered(
        opening,
        [
            "RegistrationBeaconRawPlan",
            "open_frame(",
            "RegistrationBeaconOpened",
            "if admitted then",
            "let registration_payload(=binding",
            "registration_beacon_established",
            "RegistrationBeaconCommitted",
            "RegistrationBeaconReturned",
        ],
        "raw opening/commit",
    )
    for stage in range(1, 16):
        if model.count(f"if failure_stage <> {stage} then") != 1:
            raise ValueError("optional failure routing changed")
    for token in [
        "general_prefix_1(receive)",
        "general_initial_plan(target, receive)",
        "material, next, skipped, true, failure_stage)",
        "material, next, skipped, false, failure_stage)",
        "out(token, registration_beacon_aborted())",
    ]:
        if model.count(token) != 1:
            raise ValueError("source plan/abort anchor changed: " + token)
    if "get registration_set_origin" in model or "new assigned" in model:
        raise ValueError("origin or fresh-ID admission added")
    subprocess.run(
        ["python3", str(HERE / "generate-general-registration.py"), "--check"],
        check=True,
        capture_output=True,
        text=True,
    )


def run(proverif, model, queries, process, log, timeout):
    command = [proverif]
    for name in [
        "production-transcript-interface.pvl",
        "crypto.pvl",
        "extraction/lib.pvl",
        "environment.pvl",
        "general-registration-cache.pvl",
        "general-registration-continuation.pvl",
        "general-registration-admission.pvl",
        "registration-set-admission.pvl",
        "registration-set-response.pvl",
    ]:
        command += ["-lib", str(HERE / name)]
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


def sequence(n):
    if n == 0:
        return "general_zero_sequence()"
    return "next_sequence(" * (n - 1) + "first_sequence()" + ")" * (n - 1)


def control_cases():
    success = ["false", "true", "true", "false", "false", "true", "false", "false"]
    rejected = ["true", "false", "true", "false", "true", "true", "false", "false"]
    cases = [("success", [], success)]
    for target in [0, 2, 51, 52]:
        edits = [("let target = first_sequence()", "let target = " + sequence(target))]
        if target in [2, 51]:
            edits += [("general_prefix_1(chain)", f"general_prefix_{target}(chain)")]
        verdicts = rejected.copy()
        if target in [2, 51]:
            verdicts[4] = "false"
        cases.append((f"sequence-{target}", edits, verdicts))
    for name, replacement in [
        (
            "wrong-prefix",
            "registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(registration_response_identifier(2))), registration_response_nonempty(BEACON_CONTROL_PAYLOAD))",
        ),
        (
            "empty-suffix",
            "registration_payload(binding, registration_response_empty())",
        ),
        ("unframed-plaintext", "BEACON_CONTROL_PAYLOAD"),
    ]:
        verdicts = rejected.copy()
        verdicts[4] = "false"
        cases.append(
            (
                name,
                [
                    (
                        "let plaintext = correct_plaintext",
                        "let plaintext = " + replacement,
                    )
                ],
                verdicts,
            )
        )
    cases.append(
        (
            "unframed-record",
            [
                (
                    "let first_frame = seal_frame(material, associated_data, target, server_id, plaintext)",
                    "let first_frame = BEACON_CONTROL_PAYLOAD",
                )
            ],
            rejected.copy(),
        )
    )
    no_prefix = ["true", "false", "true", "false", "true", "true", "true", "true"]
    cases.append(
        (
            "malformed-response",
            [
                (
                    "let first_raw = kex_response(server, x25519_public(ephemeral_secret), ciphertext, first_frame, assigned)",
                    "let first_raw = BEACON_CONTROL_PAYLOAD",
                )
            ],
            no_prefix,
        )
    )
    verdicts = rejected.copy()
    verdicts[5] = "false"
    cases.append(
        (
            "wrong-pin",
            [("let pinned = server", "let pinned = ed_public(BEACON_CONTROL_OTHER)")],
            verdicts,
        )
    )
    for stage in range(1, 16):
        verdicts = no_prefix.copy() if stage <= 10 else rejected.copy()
        cases.append(
            (
                f"failure-{stage}",
                [
                    (
                        "one_time_secret, pq_secret, 0)\n  | in(first_reply",
                        f"one_time_secret, pq_secret, {stage})\n  | in(first_reply",
                    )
                ],
                verdicts,
            )
        )
    return cases


def single_preparation(text):
    """Restrict only the concrete edge fixture to one real source preparation."""
    call = (
        "RegistrationBeaconControlRetry(owner, token, retry_reply, retry_raw, pinned,\n"
        "        server_id, identity_secret, prekey_secret, pq_secret, one_time_secret)"
    )
    if text.count(call) != 2:
        raise ValueError("finite control retry anchors changed")
    return text.replace(call, "0")


def check(proverif, logdir, timeout):
    check_source_order()
    model = HERE / "registration-beacon-admission.pvl"
    output = run(
        proverif,
        model,
        HERE / "registration-beacon-admission-queries.pvl",
        HERE / "registration-beacon-admission.pv",
        logdir / "correspondences.log",
        timeout,
    )
    check_output(output, PRIMARY, VERDICTS, 0)
    print(
        "replicated correspondence results: eight true, one explicit unknown",
        flush=True,
    )
    check_controls(proverif, logdir, timeout)


def check_controls(proverif, logdir, timeout):
    """Recheck the concrete controls separately after a fixture-only edit."""
    model = HERE / "registration-beacon-admission.pvl"
    tail = (HERE / "registration-beacon-control.pv").read_text()
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-beacon-controls-"
    ) as directory:
        scratch = Path(directory)
        for name, edits, verdicts in control_cases():
            fixture = scratch / (name + ".pv")
            text = tail
            for old, new in edits:
                text = BASE.exact_replace(text, old, new)
            queries = HERE / "registration-beacon-control-queries.pvl"
            expected = TAIL
            if name == "sequence-51":
                # Keep the real preparation but omit the second finite call at
                # this long-chain edge. Other controls check actual retries.
                text = single_preparation(text)
                queries = scratch / "boundary-queries.pvl"
                query_text = (
                    HERE / "registration-beacon-control-queries.pvl"
                ).read_text()
                for event in [
                    "RegistrationBeaconControlRetrySuccess",
                    "RegistrationBeaconControlRetryFailure",
                ]:
                    query_text = BASE.exact_replace(
                        query_text, f"query event({event}()).\n", ""
                    )
                queries.write_text(query_text)
                positions = [0, 1, 4, 5, 6, 7]
                expected = [TAIL[i] for i in positions]
                verdicts = [verdicts[i] for i in positions]
            fixture.write_text(text)
            output = run(
                proverif, model, queries, fixture, logdir / (name + ".log"), timeout
            )
            check_output(output, expected, verdicts, verdicts.count("false"))
            print("active-tail control " + name + " passed", flush=True)
        sensitivity = [
            (
                "omit-sequence",
                "if admitted then (",
                "if true then (",
                "sequence-2",
                ["false", "true", "true", "false", "false", "true", "false", "false"],
            ),
            (
                "omit-binding",
                "let registration_payload(=binding,",
                "let registration_payload(unchecked_binding,",
                "wrong-prefix",
                ["false", "true", "true", "false", "false", "true", "false", "false"],
            ),
            (
                "retain-init",
                "out(token, registration_beacon_aborted())",
                "out(token, registration_beacon_init_sent())",
                "failure-1",
                ["true", "false", "false", "true", "false", "true", "false", "false"],
            ),
        ]
        for name, old, new, case, verdicts in sensitivity:
            changed = scratch / (name + ".pvl")
            changed.write_text(BASE.exact_replace(model.read_text(), old, new))
            output = run(
                proverif,
                changed,
                HERE / "registration-beacon-control-queries.pvl",
                scratch / (case + ".pv"),
                logdir / (name + ".log"),
                timeout,
            )
            check_output(output, TAIL, verdicts, verdicts.count("false"))
            print("sensitivity " + name + " passed", flush=True)
    print(
        "Beacon boundary: 9 replicated results, 25 retry tails, 1 single-preparation edge, 3 reconstructed sensitivity controls",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--logdir", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    args.logdir.mkdir(parents=True, exist_ok=True)
    check(args.proverif, args.logdir, args.timeout)


if __name__ == "__main__":
    main()
