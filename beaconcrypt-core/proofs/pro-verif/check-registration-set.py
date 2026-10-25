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


def rust_body(root, relative, anchor, scope=""):
    """Locate a reviewed Rust item; this textual check does not parse Rust semantics."""
    source = (root / relative).read_text()
    start = source.index(anchor, source.index(scope) if scope else 0)
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth and end < len(source):
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    if depth:
        raise ValueError("unterminated reviewed Rust item: " + anchor)
    return "".join(source[start:end].split())


def source_order(root, relative, anchor, tokens, scope=""):
    body = rust_body(root, relative, anchor, scope)
    positions = []
    for token in tokens:
        token = "".join(token.split())
        if body.count(token) != 1:
            raise ValueError(
                f"reviewed source anchor changed: {relative}: {anchor}: {token}"
            )
        positions.append(body.index(token))
    if positions != sorted(positions):
        raise ValueError(f"reviewed source order changed: {relative}: {anchor}")
    return body


def check_source_order():
    """Reviewed interpreter/core drift checks for the retained classical projection."""
    root = HERE.parents[2]
    source_order(
        root,
        "beaconcrypt/src/server.rs",
        "fn get_shared_secret(",
        [
            "let control = self.control;",
            "let registration = decode_init(buffer)?;",
            "InitPacket::from_slices(registration.identity_key, registration.pre_key, registration.one_time_key, registration.pq_key, registration.mldsa_public_key, registration.signature,)",
            "auth::authenticate_init(self.authentication_pin()?, packet)?",
            "let registration_id = *authenticated.registration_id().as_bytes();",
            "let status = if self.consumed_registrations.contains(&registration_id) { verified_pqxdh::RegistrationStatus::Consumed } else { verified_pqxdh::RegistrationStatus::Fresh };",
            "verified_pqxdh::validate_registration_status(status).ok()?;",
            "self.consumed_registrations.try_reserve(1)",
            "crate::pqxdh::execute_agreement(agreement::begin_server_agreement(control, status, authenticated), crate::pqxdh::RegistrationKeys { identity_secret: self.identity_sk(), beacon_prekey: None, beacon_one_time: None, beacon_kem: None, },)",
            "AgreementEffect::ServerComplete(agreement) => agreement,",
            "self.consumed_registrations.insert(registration_id)",
            "Some(RegistrationOutput { agreement })",
        ],
        "impl ProviderServer for Server {",
    )
    source_order(
        root,
        "beaconcrypt/src/auth.rs",
        "pub(crate) fn authenticate_init(",
        [
            "registration::begin_init_authentication(pin, packet)",
            "InitAuthentication::Rejected => return None,",
            "InitAuthentication::Accepted(authenticated) => return Some(authenticated),",
            "InitAuthentication::HashRequested(pending)",
            "let hash = execute_hash(&pending.request()); pending.resume(hash)",
            "InitAuthentication::MldsaVerificationRequested(pending)",
            "let verified = verify_requested(&pending.request()); pending.resume(verified)",
            "InitAuthentication::Ed25519VerificationRequested(pending)",
            "crypto_sign::PublicKey::from_bytes(request.public_key)",
            "crypto_sign::verify(request.signed, &public_key)",
            "pending.resume(opened.as_deref())",
            "InitAuthentication::ServerFingerprintRequested(pending)",
            "InitAuthentication::BeaconFingerprintRequested(pending)",
        ],
    )
    source_order(
        root,
        "beaconcrypt/src/auth.rs",
        "pub(crate) fn execute_hash(",
        [
            "HashRequest::Single(input) => state.update(input)",
            "HashRequest::Triple(parts) => { for part in parts { state.update(part); } }",
            "finish_hash(state)",
        ],
    )
    source_order(
        root,
        "beaconcrypt/src/auth.rs",
        "pub(crate) fn verify_requested(",
        [
            "EncodedVerifyingKey<MlDsa65>>::try_from(request.public_key.as_slice())",
            "Signature::<MlDsa65>::try_from(request.signature.as_slice())",
            "VerifyingKey::decode(encoded_key).verify_with_context(request.input, &request.context, &signature,)",
        ],
    )
    source_order(
        root,
        "beaconcrypt/src/auth.rs",
        "pub(crate) fn sign_requested(",
        [
            "if self.public_key() != *request.public_key { return None; }",
            "sign_deterministic(request.input, &request.context)",
        ],
    )
    source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume(self, verified: bool)",
        [
            "if !verified || self.state.packet.identity_key[0] != SIGN_TYPE_ED25519",
            "InitAuthentication::Rejected",
            "stage: SignedKeyStage::PqKey",
        ],
        "impl<'a> InitMldsaVerification<'a>",
    )
    scope = "impl<'a> InitEd25519Verification<'a>"
    source_order(
        root,
        "beaconcrypt-core/src/registration.rs",
        "pub fn resume(mut self, opened:",
        [
            "opened != &self.request().signed[64..]",
            "SignedKeyStage::PreKey =>",
            "self.pre_key = pre_key; self.stage = SignedKeyStage::OneTimeKey;",
            "SignedKeyStage::OneTimeKey =>",
            "InitKex::from_encoded(*self.state.packet.identity_key, self.pre_key, one_time_key, self.pq_key,)",
            "validate_init_kex(message)",
            "InitAuthentication::ServerFingerprintRequested",
            "SignedKeyStage::PqKey =>",
            "self.pq_key = pq_key; self.stage = SignedKeyStage::PreKey;",
        ],
        scope,
    )
    source_order(
        root,
        "beaconcrypt-core/src/agreement.rs",
        "pub fn begin_server_agreement(",
        [
            "validate_registration_status(status)",
            "authenticated.into_parts()",
            "AgreementEffect::GenerateEphemeral",
        ],
    )
    source_order(
        root,
        "beaconcrypt-core/src/agreement.rs",
        "fn finish_dh(",
        [
            "let secrets = PqxdhSharedSecrets",
            "AgreementInput::Server",
            "pqxdh::server_accept(",
            "AgreementCandidate::Server",
            "AgreementInput::Beacon",
            "pqxdh::beacon_prepare_finish(control, &inputs)",
            "AgreementCandidate::Beacon",
            "AgreementEffect::RootKdf",
        ],
    )
    source_order(
        root,
        "beaconcrypt/src/pqxdh.rs",
        "pub(crate) fn execute_agreement",
        [
            "AgreementEffect::ConvertPublic(pending)",
            "crypto_sign::PublicKey::from_bytes(pending.public_key())",
            "crypto_sign::ed25519_pk_to_curve25519(&key)",
            "AgreementEffect::ConvertSecret(pending)",
            "crypto_sign::ed25519_sk_to_curve25519(keys.identity_secret)",
            "AgreementEffect::GenerateEphemeral(pending)",
            "server_ephemeral = crypto_kx::KeyPair::generate().ok();",
            "AgreementEffect::Encapsulate(pending)",
            "crypto_kem::mlkem768::encapsulate(&key)",
            "AgreementEffect::Decapsulate(pending)",
            "crypto_kem::mlkem768::decapsulate(&ciphertext, keys.beacon_kem?)",
            "AgreementEffect::Dh(pending)",
            "DhSecretRole::LocalIdentity => { local_identity.as_ref().map(|key| key.as_slice()) }",
            "DhSecretRole::ServerEphemeral => server_ephemeral.as_ref().map(|key| key.secret_key.as_bytes())",
            "DhSecretRole::BeaconPrekey => keys.beacon_prekey.map(|key| key.as_bytes())",
            "DhSecretRole::BeaconOneTime => keys.beacon_one_time.map(|key| key.as_bytes())",
            "crypto_scalarmult::scalarmult(secret, request.public_key)",
            "AgreementEffect::RootKdf(pending)",
            "crypto_kdf::hkdf::sha512::extract(None, request.input)",
            "crypto_kdf::hkdf::sha512::expand(32, Some(request.info), &prk)",
            "expanded.as_slice().try_into().ok()",
            "pending.resume(root)",
        ],
    )
    source_order(
        root,
        "beaconcrypt-core/src/agreement.rs",
        "pub fn resume(mut self, root:",
        [
            "let Some(root) = root else",
            "pending.root_key_input_mut().clear()",
            "candidate.root_key_input_mut().clear()",
            "RatchetChain::from_bytes(root)",
            "AgreementEffect::ServerComplete",
            "AgreementEffect::BeaconComplete",
        ],
        "impl<'a> RootKdfPending<'a>",
    )


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
