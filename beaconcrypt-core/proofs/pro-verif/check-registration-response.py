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
    root = HERE.parents[2]
    ADMISSION.source_order(
        root,
        "beaconcrypt/src/server.rs",
        "fn build_registration_response(",
        [
            "let control = self.control;",
            "let application = beaconcrypt_core::transport::normalize_registration_application(data);",
            "let plaintext = registration_application_bytes(&application);",
            "let RegistrationOutput { registration } = reg_out;",
            "beaconcrypt_core::peer::begin_completion_lookup(control, self.authentication_pin()?, registration, plaintext,)",
            "let next_key_id = lookup.request();",
            "registration_response_len(plaintext.len(), next_key_id)?;",
            "lookup.resume(self.known_ids.contains_key(&next_key_id))",
            "self.known_ids.try_reserve(1)",
            "crate::ratchet::initial_ratchet_hkdf(pending.request())",
            "let pending = pending.resume(Some(response)).ok()?; let response = crate::ratchet::ratchet_hkdf(pending.request()); let pending = pending.resume(Some(response)).ok()?;",
            "let detached = crate::ratchet::execute_seal_request(pending.request());",
            "let detached_view = detached.as_ref().map(|(body, tag)| (body.as_slice(), *tag));",
            "let mut pending = pending.resume(detached_view).ok()?;",
            "let commitment = crate::ratchet::execute_commitment_hash(pending.transcript_mut());",
            "let pending = pending.resume(commitment).ok()?;",
            "let ciphertext = crate::ratchet::execute_write_request(pending.request());",
            "let pending = pending.resume(ciphertext.as_deref()).ok()?;",
            "auth::execute_hash(&pending.request())",
            "pending.resume(hash).ok()?",
            "self.mldsa_identity.sign_requested(&pending.request())",
            "pending.resume(signature.as_deref()).ok()?",
            "let message = ready.message();",
            "crate::wire::encode_response(KexResponse { identity_key: message.identity_key, ephemeral_key: message.ephemeral_key, kem_cipher_text: message.kem_cipher_text, key_id: message.key_id, app_cipher_text: message.application_ciphertext, signature: message.signature, })",
            "beaconcrypt_core::peer::begin_peer_insert(control, ready.publish(buffer).ok()?).ok()?;",
            "let remote_kid = pending.request();",
            "crypto_sign::PublicKey::from_bytes(peer.binding().beacon_identity_public_key())",
            "self.known_ids.entry(remote_kid)",
            "std::collections::hash_map::Entry::Vacant(entry)",
            "entry.insert(EstablishedRemote::from_peer(public_key, peer));",
            "std::collections::hash_map::Entry::Occupied(_) => false",
            "finish.finish(inserted).ok()?.into_parts()",
            "self.control = next_control;",
            "Some(RegResponse { serialized: buffer, kid: remote_kid, })",
        ],
        "impl ProviderServer for Server {",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn begin_server_completion",
        [
            "let rejected = control;",
            "if application.is_empty() || !agreement.binding.matches_server(current_pin)",
            "return Err(rejected);",
            "crate::pqxdh::server_prepare_commit(control, agreement.pending, current_pin.binding(), availability,)",
            "crate::pqxdh::start_server_candidate_ratchet_kdf(&candidate, agreement.root.as_bytes())",
            "Ok(ServerInitialKdf",
        ],
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume(",
        [
            "None => return Err(rejected)",
            "crate::pqxdh::resume_initial_ratchet_kdf(self.pending, response)",
            "records::SealFrameContext::registration(self.application, self.candidate.key_id(), self.candidate.server_identity_key_id(), self.binding.associated_data(),)",
            "records::begin_record_send(kernel, context)",
            "records::RecordSendStart::Rejected(_) => return Err(rejected)",
            "state: ServerRecordState { candidate: self.candidate, binding: self.binding, application: self.application, }, pending,",
        ],
        "impl<'a> ServerInitialKdf<'a>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume(",
        [
            "None => return Err(crate::pqxdh::server_abort_candidate(&self.state.candidate))",
            "state: self.state, pending: self.pending.resume(response)",
        ],
        "impl<'a> ServerInitialSeal<'a>",
    )
    for scope, reply, rejected, accepted in [
        (
            "impl<'a> ServerRecordAead<'a>",
            "detached",
            "SealAfterAead::Rejected",
            "SealAfterAead::CommitmentRequested",
        ),
        (
            "impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>",
            "commitment",
            "SealAfterCommitment::Rejected",
            "SealAfterCommitment::WriteRequested",
        ),
    ]:
        ADMISSION.source_order(
            root,
            "beaconcrypt-core/src/registration.rs",
            "pub fn resume",
            [
                f"self.pending.resume({reply})",
                rejected,
                "Err(crate::pqxdh::server_abort_candidate(&self.state.candidate))",
                accepted,
                "state: self.state, pending,",
            ],
            scope,
        )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume<'output>(",
        [
            "let rejected = crate::pqxdh::server_abort_candidate(&self.state.candidate);",
            "let (kernel, sealed) = self.pending.finish(ciphertext);",
            "Some(sealed) => sealed.ciphertext, None => return Err(rejected)",
            "8usize.checked_add(self.state.application.len())",
            "bound_length.checked_add(crate::record::MESSAGE_OVERHEAD)",
            "if ciphertext.len() != length { return Err(rejected); }",
            "build_response_prefix(self.state.binding.init_hash(), self.state.candidate.server_identity_public_key(), self.state.candidate.ephemeral_public_key(), self.state.candidate.kem_ciphertext(),",
            "let assigned_id = encode_u64_le(self.state.candidate.key_id());",
            "Ok(ServerResponseHash { candidate: self.state.candidate, binding: self.state.binding, kernel, ciphertext, prefix, assigned_id, })",
        ],
        "impl ServerRecordWrite<'_, '_>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn request(&self)",
        [
            "HashRequest::Triple([&self.prefix, self.ciphertext, &self.assigned_id])",
        ],
        "impl<'a> ServerResponseHash<'a>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume(",
        [
            "let rejected = crate::pqxdh::server_abort_candidate(&self.candidate);",
            "build_signature_input(AuthRole::Server,",
            "Some(digest) => digest, None => return Err(rejected),",
        ],
        "impl<'a> ServerResponseHash<'a>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn request(&self)",
        [
            "role: AuthRole::Server",
            "public_key: self.binding.server_pin().public_key()",
            "input: &self.input",
            "context: SIGNING_CONTEXT",
        ],
        "impl<'a> ServerResponseSigning<'a>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn message(&self)",
        [
            "identity_key: self.candidate.server_identity_public_key()",
            "ephemeral_key: self.candidate.ephemeral_public_key()",
            "kem_cipher_text: self.candidate.kem_ciphertext()",
            "key_id: self.candidate.key_id()",
            "application_ciphertext: self.ciphertext",
            "signature: &self.signature",
        ],
        "impl ServerResponseReady<'_>",
    )
    ADMISSION.source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn publish<Encoded>(",
        [
            "let encoded = match encoded { Some(encoded) => encoded, None => return Err(rejected), };",
            "self.binding.finish(self.candidate.key_id())",
            "crate::pqxdh::server_commit(self.candidate)",
            "Ok(PublishedServerResponse",
        ],
        "impl ServerResponseReady<'_>",
    )
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
