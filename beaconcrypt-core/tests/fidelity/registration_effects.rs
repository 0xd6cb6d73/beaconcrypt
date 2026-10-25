// SPDX-License-Identifier: 0BSD

//! Reviewed source correspondence for the extracted registration phases and their primitive drivers.
//! These checks do not establish primitive authenticity or a Rust-to-ProVerif compiler.

use super::{Snapshot, compact, require_once, require_ordered_once, rust_body, uncommented_rust};

fn source<'a>(snapshot: &'a Snapshot, name: &str) -> &'a str {
	match name {
		"registration" => &snapshot.core_registration,
		"records" => &snapshot.core_record_effects,
		"ratchet" => &snapshot.adapter_ratchet,
		"core-pqxdh" => &snapshot.core_pqxdh,
		"agreement" => &snapshot.core_agreement,
		"auth" => &snapshot.adapter_auth,
		"pqxdh" => &snapshot.adapter_pqxdh,
		"beacon" => &snapshot.adapter_beacon,
		"server" => &snapshot.adapter_server,
		_ => panic!("unknown registration source: {name}"),
	}
}

pub(super) fn body(
	snapshot: &Snapshot,
	name: &str,
	scope: &str,
	function: &str,
) -> Result<String, String> {
	let source = source(snapshot, name);
	let source = if scope.is_empty() {
		source
	} else {
		source
			.split_once(scope)
			.ok_or_else(|| format!("missing registration scope: {scope}"))?
			.1
	};
	rust_body(source, function)
}

fn check(
	snapshot: &Snapshot,
	name: &str,
	scope: &str,
	function: &str,
	wanted: &str,
	label: &str,
) -> Result<(), String> {
	require_once(
		&body(snapshot, name, scope, function)?,
		&compact(wanted),
		label,
	)
}

const DH_REQUESTS: &[&str] = &[
	"(AgreementInput::Server{registration,..},DhPosition::First)=>DhRequest{secret_role:DhSecretRole::LocalIdentity,public_key:registration.beacon_prekey_public_key(),}",
	"(AgreementInput::Server{..},DhPosition::Second)=>DhRequest{secret_role:DhSecretRole::ServerEphemeral,public_key:&self.state.remote_identity,}",
	"(AgreementInput::Server{registration,..},DhPosition::Third)=>DhRequest{secret_role:DhSecretRole::ServerEphemeral,public_key:registration.beacon_prekey_public_key(),}",
	"(AgreementInput::Server{registration,..},DhPosition::Fourth)=>DhRequest{secret_role:DhSecretRole::ServerEphemeral,public_key:registration.beacon_one_time_public_key(),}",
	"(AgreementInput::Beacon{..},DhPosition::First)=>DhRequest{secret_role:DhSecretRole::BeaconPrekey,public_key:&self.state.remote_identity,}",
	"(AgreementInput::Beacon{response,..},DhPosition::Second)=>DhRequest{secret_role:DhSecretRole::LocalIdentity,public_key:&response.ephemeral_key,}",
	"(AgreementInput::Beacon{response,..},DhPosition::Third)=>DhRequest{secret_role:DhSecretRole::BeaconPrekey,public_key:&response.ephemeral_key,}",
	"(AgreementInput::Beacon{response,..},DhPosition::Fourth)=>DhRequest{secret_role:DhSecretRole::BeaconOneTime,public_key:&response.ephemeral_key,}",
];

const NATIVE_AGREEMENT: &[&str] = &[
	"crypto_kem::mlkem768::PublicKey::from_bytes(pending.public_key()?)",
	"crypto_kem::mlkem768::Ciphertext::from_bytes(pending.ciphertext()?)",
	"crypto_kem::mlkem768::decapsulate(&ciphertext,keys.beacon_kem?)",
	"crypto_scalarmult::scalarmult(secret,request.public_key)",
	"crypto_kdf::hkdf::sha512::extract(None,request.input)",
	"crypto_kdf::hkdf::sha512::expand(32,Some(request.info),&prk)",
	"pending.resume(root)",
];

const ADDITIONAL: &[(&str, &str, &str, &str, &str)] = &[
	(
		"core-pqxdh",
		"impl RootKeyInput",
		"clear",
		"*self=Self{bytes:[0;192]};",
		"registration consumed root transcript is cleared",
	),
	(
		"server",
		"",
		"get_shared_secret",
		"verified_pqxdh::validate_registration_status(status).ok()?;",
		"registration Server replay-status gate",
	),
	(
		"server",
		"",
		"get_shared_secret",
		"self.consumed_registrations.try_reserve(1).ok()?;",
		"registration Server consumed-set reservation",
	),
	(
		"beacon",
		"",
		"finish_registration",
		"ResponsePacket::from_slices(response.identity_key,response.ephemeral_key,response.kem_cipher_text,response.key_id,response.app_cipher_text,response.signature,)",
		"registration complete fixed-width authenticated response mapping",
	),
	(
		"beacon",
		"",
		"finish_registration",
		"InitialRatchetKdfResponse::from_bytes(crate::ratchet::initial_ratchet_hkdf(pending.request()),)",
		"initial ratchet Beacon exact native 64-byte response",
	),
	(
		"server",
		"",
		"build_registration_response",
		"InitialRatchetKdfResponse::from_bytes(crate::ratchet::initial_ratchet_hkdf(pending.request()),)",
		"initial ratchet Server exact native 64-byte response",
	),
	(
		"registration",
		"impl PinFingerprint",
		"request",
		"HashRequest::Single(&self.public_key)",
		"registration exact server-pin fingerprint request",
	),
	(
		"registration",
		"impl<'a> InitMldsaVerification",
		"resume",
		"letpublic_key=core::array::from_fn(|index|self.state.packet.identity_key[index+1]);",
		"Phase-1 Server identity decoder",
	),
	(
		"registration",
		"impl<'a> InitEd25519Verification",
		"resume",
		"self.pre_key=pre_key;self.stage=SignedKeyStage::OneTimeKey;InitAuthentication::Ed25519VerificationRequested(self)",
		"Phase-1 Server prekey-to-one-time continuation",
	),
	(
		"registration",
		"impl<'a> InitEd25519Verification",
		"resume",
		"self.pq_key=pq_key;self.stage=SignedKeyStage::PreKey;InitAuthentication::Ed25519VerificationRequested(self)",
		"Phase-1 Server PQ-to-prekey continuation",
	),
	(
		"registration",
		"impl<'a> InitServerFingerprint",
		"request",
		"HashRequest::Single(self.state.server_pin.public_key())",
		"registration exact selected server fingerprint",
	),
	(
		"registration",
		"impl<'a> InitServerFingerprint",
		"resume",
		"ServerAuthenticationPin::new(self.state.server_pin.binding(),*self.state.server_pin.public_key(),fingerprint,)",
		"registration exact reconstructed server fingerprint binding",
	),
	(
		"registration",
		"impl AuthenticatedInit",
		"into_parts",
		"(self.registration,self.binding)",
		"registration authenticated request decomposition",
	),
	(
		"registration",
		"impl<'a> AuthenticatedResponse",
		"into_parts",
		"(self.pending.control,self.pending.binding,self.packet.public,self.packet.application,)",
		"registration authenticated response decomposition",
	),
	(
		"registration",
		"",
		"begin_response_authentication",
		"letassigned_id=encode_u64_le(packet.public.key_id);",
		"MLDSA authenticated response assigned-ID encoding",
	),
	(
		"registration",
		"impl BeaconFingerprint",
		"request",
		"HashRequest::Single(&self.state.beacon_mldsa)",
		"MLDSA exact beacon fingerprint request",
	),
	(
		"registration",
		"impl BeaconInitHash",
		"request",
		"HashRequest::Single(&self.input)",
		"MLDSA exact beacon transcript hash request",
	),
	(
		"registration",
		"",
		"begin_beacon_init",
		"letstarted=crate::pqxdh::beacon_start(control,inputs,coins);",
		"registration core Fresh-to-InitSent delegation",
	),
	(
		"registration",
		"impl<'a> BeaconInitialKdf",
		"request",
		"self.pending.request()",
		"initial ratchet Beacon exact request accessor",
	),
	(
		"registration",
		"impl<'a> BeaconInitialKdf",
		"resume",
		"crate::pqxdh::resume_initial_ratchet_kdf(self.pending,response)",
		"initial ratchet Beacon same pending and response",
	),
	(
		"registration",
		"impl<'a> ServerInitialKdf",
		"request",
		"self.pending.request()",
		"initial ratchet Server exact request accessor",
	),
	(
		"registration",
		"impl<'a> ServerInitialKdf",
		"resume",
		"crate::pqxdh::resume_initial_ratchet_kdf(self.pending,response)",
		"initial ratchet Server same pending and response",
	),
	(
		"registration",
		"impl<'a> CompletedBeacon",
		"into_parts",
		"(self.control,self.binding,self.kernel,self.application)",
		"registration completed Beacon exact result parts",
	),
	(
		"registration",
		"impl<'a> ServerResponseHash",
		"resume",
		"input:build_signature_input(AuthRole::Server,&matchdigest{Some(digest)=>digest,None=>returnErr(rejected),},)",
		"MLDSA exact response signature input",
	),
	(
		"registration",
		"impl<Encoded> PublishedServerResponse",
		"into_parts",
		"(self.control,self.binding,self.kernel,self.encoded)",
		"registration published Server exact result parts",
	),
	(
		"agreement",
		"",
		"begin_server_agreement",
		"ifpqxdh::validate_registration_status(status).is_err(){returnAgreementEffect::Rejected(None);}",
		"registration core replay status gate",
	),
	(
		"agreement",
		"impl<'a> PublicConversionPending",
		"public_key",
		"AgreementInput::Beacon{response,..}=>&response.identity_key,",
		"registration authenticated server conversion operand",
	),
	(
		"agreement",
		"impl<'a> PublicConversionPending",
		"resume",
		"self.state.remote_identity=converted;AgreementEffect::ConvertSecret(SecretConversionPending{state:self.state})",
		"registration public conversion result continuation",
	),
	(
		"agreement",
		"impl<'a> SecretConversionPending",
		"resume",
		"if!converted{returnself.state.reject();}",
		"registration secret conversion failure",
	),
	(
		"agreement",
		"impl<'a> EphemeralPending",
		"resume",
		"self.state.ephemeral_public_key=public_key;AgreementEffect::Encapsulate(EncapsulationPending{state:self.state})",
		"registration ephemeral result continuation",
	),
	(
		"agreement",
		"impl<'a> EncapsulationPending",
		"resume",
		"self.state.kem_ciphertext=ciphertext;self.state.kem=RatchetChain::from_bytes(shared);AgreementEffect::ConvertPublic(PublicConversionPending{state:self.state})",
		"registration encapsulation result continuation",
	),
	(
		"agreement",
		"impl<'a> DecapsulationPending",
		"resume",
		"self.state.kem=RatchetChain::from_bytes(shared);AgreementEffect::Dh(DhPending{state:self.state,position:DhPosition::First,})",
		"registration decapsulation result continuation",
	),
	(
		"agreement",
		"impl<'a> RootKdfPending",
		"request",
		"AgreementCandidate::Server{pending,..}=>pending.root_key_input().as_bytes(),AgreementCandidate::Beacon{candidate,..}=>candidate.root_key_input().as_bytes(),",
		"registration root input belongs to retained candidate",
	),
	(
		"agreement",
		"impl<'a> RootKdfPending",
		"resume",
		"AgreementCandidate::Server{pending,..}=>pending.root_key_input_mut().clear(),AgreementCandidate::Beacon{candidate,..}=>candidate.root_key_input_mut().clear(),",
		"registration immediate root transcript erasure",
	),
	(
		"agreement",
		"impl<'a> RootKdfPending",
		"resume",
		"AgreementEffect::ServerComplete(ServerAgreement{pending,binding,root,})",
		"registration Server retains matching root and pending candidate",
	),
	(
		"agreement",
		"impl<'a> RootKdfPending",
		"resume",
		"AgreementEffect::BeaconComplete(BeaconAgreement{candidate,binding,root,application_ciphertext,})",
		"registration Beacon retains matching root candidate and ciphertext",
	),
	(
		"auth",
		"",
		"execute_hash",
		"HashRequest::Single(input)=>state.update(input)",
		"MLDSA adapter exact single hash request",
	),
	(
		"auth",
		"",
		"authenticate_init",
		"libsodium_rs::crypto_sign::PublicKey::from_bytes(request.public_key)",
		"Phase-1 actual requested Ed25519 verifier identity",
	),
	(
		"auth",
		"",
		"authenticate_init",
		"libsodium_rs::crypto_sign::verify(request.signed,&public_key)",
		"Phase-1 actual requested Ed25519 signature verification",
	),
	(
		"auth",
		"",
		"authenticate_init",
		"pending.resume(opened.as_deref())",
		"Phase-1 actual Ed25519 opened-message continuation",
	),
	(
		"auth",
		"",
		"authenticate_response",
		"begin_response_authentication(pending,packet)?;letdigest=execute_hash(&pending.request());letpending=pending.resume(digest)?;letverified=verify_requested(&pending.request());pending.resume(verified)",
		"MLDSA native response hash-before-verification order",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"crypto_sign::PublicKey::from_bytes(pending.public_key())",
		"registration exact Ed25519 conversion input",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		".and_then(|key|crypto_sign::ed25519_pk_to_curve25519(&key).ok());pending.resume(converted)",
		"registration actual public conversion response",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"crypto_sign::ed25519_sk_to_curve25519(keys.identity_secret).ok().map(Zeroizing::new);pending.resume(local_identity.is_some())",
		"registration actual secret conversion response",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"server_ephemeral=crypto_kx::KeyPair::generate().ok();",
		"registration actual fresh ephemeral generation",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"Some((*ciphertext.as_bytes(),*shared.as_bytes()))",
		"registration actual encapsulation result parts",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"DhSecretRole::LocalIdentity=>{local_identity.as_ref().map(|key|key.as_slice())}",
		"registration local identity secret-role interpretation",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"DhSecretRole::ServerEphemeral=>server_ephemeral.as_ref().map(|key|key.secret_key.as_bytes()),",
		"registration generated ephemeral secret-role interpretation",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"DhSecretRole::BeaconPrekey=>keys.beacon_prekey.map(|key|key.as_bytes()),",
		"registration beacon prekey secret-role interpretation",
	),
	(
		"pqxdh",
		"",
		"execute_agreement",
		"DhSecretRole::BeaconOneTime=>keys.beacon_one_time.map(|key|key.as_bytes()),",
		"registration beacon one-time secret-role interpretation",
	),
	(
		"beacon",
		"",
		"finish_registration",
		"RegistrationKeys{identity_secret:self.identity_sk(),beacon_prekey:Some(&prekey.secret_key),beacon_one_time:Some(&onetime_key.secret_key),beacon_kem:Some(&pq_key.secret_key),}",
		"registration Beacon secret handles belong to pending request",
	),
	(
		"server",
		"",
		"get_shared_secret",
		"InitPacket::from_slices(registration.identity_key,registration.pre_key,registration.one_time_key,registration.pq_key,registration.mldsa_public_key,registration.signature,)",
		"registration complete fixed-width init parser mapping",
	),
	(
		"server",
		"",
		"get_shared_secret",
		"RegistrationKeys{identity_secret:self.identity_sk(),beacon_prekey:None,beacon_one_time:None,beacon_kem:None,}",
		"registration Server local secret handles",
	),
	(
		"server",
		"",
		"build_registration_response",
		"KexResponse{identity_key:message.identity_key,ephemeral_key:message.ephemeral_key,kem_cipher_text:message.kem_cipher_text,key_id:message.key_id,app_cipher_text:message.application_ciphertext,signature:message.signature,}",
		"Phase-2 complete signed serializer mapping",
	),
	(
		"server",
		"",
		"build_registration_response",
		"letremote_kid=binding.assigned_key_id();",
		"registration assigned target comes from published binding",
	),
	(
		"server",
		"",
		"build_registration_response",
		"crypto_sign::PublicKey::from_bytes(binding.beacon_identity_public_key()).ok()?",
		"registration established peer identity comes from binding",
	),
	(
		"server",
		"",
		"build_registration_response",
		"self.known_ids.insert(remote_kid,EstablishedRemote::new(public_key,RatchetManager::from_kernel(kernel),binding),)",
		"registration established peer retains exact identity kernel and binding",
	),
	(
		"server",
		"",
		"build_registration_response",
		"Some(RegResponse{serialized:buffer,kid:remote_kid,})",
		"registration returned target and serialized payload",
	),
];

const AUTHENTICATION: &[(&str, &str, &str, &str)] = &[
	(
		"impl<'a> InitPacket",
		"fields",
		"InitFields{identity_key:self.identity_key,pre_key:self.pre_key,one_time_key:self.one_time_key,pq_key:self.pq_key,mldsa_public_key:self.mldsa_public_key,}",
		"MLDSA request transcript field order and pins",
	),
	(
		"",
		"begin_init_authentication",
		"build_init_transcript(packet.fields(),server.identity_key_id,&server.identity_public_key,server_pin.public_key(),)",
		"MLDSA request transcript field order and pins",
	),
	(
		"impl<'a> InitHash",
		"request",
		"HashRequest::Single(&self.input)",
		"MLDSA exact init hash request",
	),
	(
		"impl<'a> InitHash",
		"resume",
		"input:build_signature_input(AuthRole::Beacon,&init_hash)",
		"MLDSA request verification precedes classical and stateful work",
	),
	(
		"impl<'a> InitMldsaVerification",
		"request",
		"MldsaVerificationRequest{public_key:self.state.packet.mldsa_public_key,input:&self.input,context:SIGNING_CONTEXT,signature:self.state.packet.signature,}",
		"MLDSA request verification precedes classical and stateful work",
	),
	(
		"impl<'a> InitMldsaVerification",
		"resume",
		"if!verified||self.state.packet.identity_key[0]!=SIGN_TYPE_ED25519{returnInitAuthentication::Rejected;}",
		"MLDSA request verification precedes classical and stateful work",
	),
	(
		"impl<'a> InitMldsaVerification",
		"resume",
		"stage:SignedKeyStage::PqKey",
		"Phase-1 Server source evaluation order",
	),
	(
		"impl<'a> InitEd25519Verification",
		"request",
		"SignedKeyStage::PreKey=>self.state.packet.pre_key,SignedKeyStage::OneTimeKey=>self.state.packet.one_time_key,SignedKeyStage::PqKey=>self.state.packet.pq_key,",
		"Phase-1 Server signature request mapping",
	),
	(
		"impl<'a> InitEd25519Verification",
		"request",
		"Ed25519VerificationRequest{public_key:&self.public_key,signed,}",
		"Phase-1 Server identity decoder",
	),
	(
		"impl<'a> InitEd25519Verification",
		"resume",
		"letSome(opened)=openedelse{returnInitAuthentication::Rejected;};",
		"Phase-1 Server signature failure",
	),
	(
		"impl<'a> InitEd25519Verification",
		"resume",
		"ifopened!=&self.request().signed[64..]{returnInitAuthentication::Rejected;}",
		"Phase-1 Server exact attached message",
	),
	(
		"impl<'a> InitEd25519Verification",
		"resume",
		"InitKex::from_encoded(*self.state.packet.identity_key,self.pre_key,one_time_key,self.pq_key,)",
		"Phase-1 Server from_encoded mapping",
	),
	(
		"impl<'a> InitEd25519Verification",
		"resume",
		"letOk(registration)=validate_init_kex(message)else{returnInitAuthentication::Rejected;};",
		"Phase-1 Server typed tag validation",
	),
	(
		"impl<'a> InitBeaconFingerprint",
		"request",
		"HashRequest::Single(self.state.packet.mldsa_public_key)",
		"MLDSA public-key fingerprint",
	),
	(
		"impl<'a> InitBeaconFingerprint",
		"resume",
		"RegistrationBinding::new(self.server_pin,self.state.init_hash,*self.registration.beacon_identity_public_key(),fingerprint,)",
		"MLDSA private accepted-token context",
	),
	(
		"",
		"begin_response_authentication",
		"build_response_prefix(pending.binding.init_hash(),&packet.public.identity_key,&packet.public.ephemeral_key,&packet.public.kem_cipher_text,application_len,)",
		"MLDSA complete response transcript",
	),
	(
		"impl<'a> ResponseHash",
		"request",
		"HashRequest::Triple([&self.prefix,self.packet.application,&self.assigned_id])",
		"MLDSA complete response transcript",
	),
	(
		"impl<'a> ResponseHash",
		"resume",
		"input:build_signature_input(AuthRole::Server,&digest)",
		"MLDSA pinned response verification before KEM, DH and installation",
	),
	(
		"impl<'a> ResponseMldsaVerification",
		"request",
		"MldsaVerificationRequest{public_key:self.pending.binding.server_pin().public_key(),input:&self.input,context:SIGNING_CONTEXT,signature:self.packet.signature,}",
		"MLDSA pinned response verification before KEM, DH and installation",
	),
	(
		"impl<'a> ResponseMldsaVerification",
		"resume",
		"if!verified{returnErr(self.pending.abort());}",
		"MLDSA pinned response verification before KEM, DH and installation",
	),
	(
		"impl BeaconInitState",
		"fields",
		"InitFields{identity_key:self.started.message.identity_key(),pre_key:&self.pre_key,one_time_key:&self.one_time_key,pq_key:&self.pq_key,mldsa_public_key:&self.beacon_mldsa,}",
		"Phase-1 Beacon field mapping",
	),
	(
		"impl BeaconEd25519Signing",
		"request",
		"SignedKeyStage::PreKey=>self.state.started.message.prekey(),SignedKeyStage::OneTimeKey=>self.state.started.message.one_time_key(),SignedKeyStage::PqKey=>self.state.started.message.pq_key(),",
		"Phase-1 Beacon attached-signature inputs",
	),
	(
		"impl BeaconEd25519Signing",
		"request",
		"public_key:&self.state.beacon_identity,role:AuthRole::Beacon,message,",
		"Phase-1 Beacon attached-signature identity",
	),
	(
		"impl BeaconEd25519Signing",
		"resume",
		"ifsigned.get(64..)!=Some(self.request().message){returnBeaconInitEffect::Rejected(self.state.original_control);}",
		"Phase-1 Beacon exact signed message",
	),
	(
		"impl BeaconFingerprint",
		"resume",
		"build_init_transcript(self.state.fields(),server.identity_key_id,&server.identity_public_key,self.state.server_pin.public_key(),)",
		"MLDSA request transcript field order and pins",
	),
	(
		"impl BeaconInitHash",
		"resume",
		"input:build_signature_input(AuthRole::Beacon,&init_hash)",
		"MLDSA request signing and retained hash before publication",
	),
	(
		"impl BeaconMldsaSigning",
		"request",
		"role:AuthRole::Beacon,public_key:&self.state.beacon_mldsa,input:&self.input,context:SIGNING_CONTEXT,",
		"MLDSA request signing and retained hash before publication",
	),
	(
		"impl BeaconMldsaSigning",
		"resume",
		"RegistrationBinding::new(self.state.server_pin,self.init_hash,self.state.beacon_identity,self.fingerprint,)",
		"MLDSA request signing and retained hash before publication",
	),
	(
		"impl BeaconInitReady",
		"publish",
		"letencoded=matchencoded{Some(encoded)=>encoded,None=>returnErr(self.state.original_control),};",
		"registration serialization-to-InitSent order",
	),
	(
		"impl BeaconInitReady",
		"publish",
		"pending:BeaconPending{control:self.state.started.state,binding:self.binding,},encoded,",
		"registration Fresh success transition and restoration",
	),
];

const NATIVE_AUTHENTICATION: &[(&str, &str, &str)] = &[
	(
		"execute_hash",
		"forpartinparts{state.update(part);}",
		"MLDSA adapter exact hash request interpretation",
	),
	(
		"verify_requested",
		"VerifyingKey::decode(encoded_key).verify_with_context(request.input,&request.context,&signature,)",
		"MLDSA canonical parsing and verification context",
	),
	(
		"verify_requested",
		"Signature::<MlDsa65>::try_from(request.signature.as_slice())",
		"MLDSA canonical parsing and verification context",
	),
	(
		"verify_requested",
		"<&EncodedVerifyingKey<MlDsa65>>::try_from(request.public_key.as_slice())",
		"MLDSA canonical parsing and verification context",
	),
	(
		"sign_requested",
		"ifself.public_key()!=*request.public_key{returnNone;}",
		"MLDSA signing identity selection",
	),
	(
		"sign_requested",
		".sign_deterministic(request.input,&request.context)",
		"MLDSA signing context and input",
	),
	(
		"authenticate_init",
		"letverified=verify_requested(&pending.request());pending.resume(verified)",
		"MLDSA actual init verifier response",
	),
	(
		"authenticate_response",
		"letverified=verify_requested(&pending.request());pending.resume(verified)",
		"MLDSA actual response verifier response",
	),
];

const AGREEMENT: &[(&str, &str, &str, &str)] = &[
	(
		"",
		"begin_server_agreement",
		"let(registration,binding)=authenticated.into_parts();",
		"registration Server accepted registration/status mapping",
	),
	(
		"",
		"begin_beacon_agreement",
		"let(control,binding,response,application_ciphertext)=authenticated.into_parts();",
		"initial ratchet Beacon candidate provenance",
	),
	(
		"impl<'a> EncapsulationPending",
		"public_key",
		"AgreementInput::Server{registration,..}=>{Some(registration.beacon_pq_public_key())}",
		"registration Server selected ML-KEM key",
	),
	(
		"impl<'a> DecapsulationPending",
		"ciphertext",
		"AgreementInput::Beacon{response,..}=>Some(&response.kem_cipher_text)",
		"Phase-2 beacon KEM-ciphertext mapping",
	),
	(
		"",
		"finish_dh",
		"PqxdhSharedSecrets{dh1:*state.dh1.as_bytes(),dh2:*state.dh2.as_bytes(),dh3:*state.dh3.as_bytes(),dh4:*state.dh4.as_bytes(),kem_shared_secret:*state.kem.as_bytes(),}",
		"registration ordered DH/KEM root input",
	),
	(
		"",
		"finish_dh",
		"pqxdh::server_accept(control,registration,status,binding.server_pin().binding(),ServerCoins{ephemeral_public_key:state.ephemeral_public_key,kem_ciphertext:state.kem_ciphertext,},&secrets,)",
		"registration Server accepted registration/status mapping",
	),
	(
		"",
		"finish_dh",
		"response_server_identity:response.identity_key,assigned_key_id:response.key_id,shared_secrets:secrets,",
		"later-registration Beacon finish inputs",
	),
	(
		"impl<'a> RootKdfPending",
		"request",
		"RootKdfRequest{input,info:pqxdh::PQXDH_INFO,}",
		"initial ratchet root KDF domain",
	),
];

const COMPLETION: &[(&str, &str, &str, &str)] = &[
	(
		"",
		"begin_beacon_completion",
		"start_beacon_candidate_ratchet_kdf(&agreement.candidate,agreement.root.as_bytes(),)",
		"initial ratchet Beacon root and candidate handoff",
	),
	(
		"",
		"begin_server_completion",
		"ifapplication.is_empty()||!agreement.binding.matches_server(current_pin){returnErr(rejected);}",
		"MLDSA token binding and signed publication precede commit",
	),
	(
		"",
		"begin_server_completion",
		"server_prepare_commit(control,agreement.pending,current_pin.binding(),availability,)",
		"registration Server candidate preparation",
	),
	(
		"",
		"begin_server_completion",
		"start_server_candidate_ratchet_kdf(&candidate,agreement.root.as_bytes())",
		"initial ratchet Server root and candidate handoff",
	),
	(
		"impl<'a> ServerResponseHash",
		"request",
		"HashRequest::Triple([&self.prefix,self.ciphertext,&self.assigned_id])",
		"MLDSA complete response transcript",
	),
	(
		"impl<'a> ServerResponseSigning",
		"request",
		"role:AuthRole::Server,public_key:self.binding.server_pin().public_key(),input:&self.input,context:SIGNING_CONTEXT,",
		"MLDSA token binding and signed publication precede commit",
	),
	(
		"impl ServerResponseReady",
		"message",
		"SignedResponseView{identity_key:self.candidate.server_identity_public_key(),ephemeral_key:self.candidate.ephemeral_public_key(),kem_cipher_text:self.candidate.kem_ciphertext(),key_id:self.candidate.key_id(),application_ciphertext:self.ciphertext,signature:&self.signature,}",
		"Phase-2 signed response field mapping",
	),
	(
		"impl ServerResponseReady",
		"publish",
		"letencoded=matchencoded{Some(encoded)=>encoded,None=>returnErr(rejected),};",
		"MLDSA token binding and signed publication precede commit",
	),
	(
		"impl ServerResponseReady",
		"publish",
		"letbinding=self.binding.finish(self.candidate.key_id());let(control,_)=crate::pqxdh::server_commit(self.candidate);",
		"MLDSA token binding and signed publication precede commit",
	),
];

const BEACON_LIFECYCLE: &[(&str, &str, &str)] = &[
	(
		"try_new",
		"server_pin:auth::fingerprint_pin(server_binding,server_public_key).ok_or(crate::KeyGenError)?",
		"MLDSA Beacon retains complete selected server pin",
	),
	(
		"get_registration_bundle",
		"letmutgenerated_onetime=ifmatches!(&self.state,BeaconState::Fresh{..}){Some(crypto_kx::KeyPair::generate().ok()?)}else{None};",
		"registration Fresh one-time generation",
	),
	(
		"get_registration_bundle",
		"BeaconState::Fresh{control,prekey,pq_key,}=>(*control,prekey.public_key.as_bytes().try_into().ok()?,*pq_key.public_key.as_bytes(),generated_onetime.as_ref()?.public_key.as_bytes().try_into().ok()?,)",
		"registration Fresh material selection",
	),
	(
		"get_registration_bundle",
		"BeaconState::FreshWithCoins{control,prekey,onetime_key,pq_key,}=>(*control,prekey.public_key.as_bytes().try_into().ok()?,*pq_key.public_key.as_bytes(),onetime_key.public_key.as_bytes().try_into().ok()?,)",
		"registration FreshWithCoins material selection",
	),
	(
		"get_registration_bundle",
		"_=>returnNone,",
		"registration ineligible-state rejection",
	),
	(
		"get_registration_bundle",
		"registration::begin_beacon_init(control,verified_pqxdh::BeaconStartInputs{identity_public_key:*self.identity_pk().as_bytes(),prekey_public_key:prekey_public,pq_public_key:pq_public,},verified_pqxdh::BeaconCoins{one_time_public_key:onetime_public,},self.authentication.server_pin,self.mldsa_public_key(),)",
		"registration Beacon-start input mapping",
	),
	(
		"get_registration_bundle",
		"crypto_sign::sign(request.message,self.identity_sk()).ok()",
		"Phase-1 Beacon actual requested signature",
	),
	(
		"get_registration_bundle",
		"ifself.identity_pk().as_bytes()==request.public_key",
		"Phase-1 Beacon actual requested identity",
	),
	(
		"get_registration_bundle",
		"pending.resume(signed.as_deref())",
		"Phase-1 Beacon actual signature continuation",
	),
	(
		"get_registration_bundle",
		"InitKex{identity_key:message.fields.identity_key,pre_key:message.fields.pre_key,one_time_key:message.fields.one_time_key,pq_key:message.fields.pq_key,mldsa_public_key:message.fields.mldsa_public_key,signature:message.signature,}",
		"Phase-1 Beacon complete serializer mapping",
	),
	(
		"get_registration_bundle",
		"let(pending,buffer)=ready.publish(buffer).ok()?.into_parts();",
		"registration completed InitKex serialization",
	),
	(
		"get_registration_bundle",
		"BeaconState::Fresh{prekey,pq_key,..}=>{letSome(onetime_key)=generated_onetime.take()else{self.state=BeaconState::Fresh{control,prekey,pq_key,};returnNone;};self.state=BeaconState::InitSent{pending,prekey,onetime_key,pq_key,};}",
		"registration Fresh success transition and restoration",
	),
	(
		"get_registration_bundle",
		"BeaconState::FreshWithCoins{prekey,onetime_key,pq_key,..}=>{self.state=BeaconState::InitSent{pending,prekey,onetime_key,pq_key,};}",
		"registration FreshWithCoins success transition",
	),
	(
		"get_registration_bundle",
		"Some(buffer)",
		"registration serialized bundle return",
	),
	(
		"new_onetime_keypair",
		"letcontrol=match&self.state{BeaconState::Fresh{control,..}=>*control,_=>returnNone,};",
		"registration post-Init one-time regeneration rejection",
	),
	(
		"delete_onetime_keypair",
		"BeaconState::InitSent{pending,..}=>BeaconState::Aborted{control:pending.abort(),}",
		"registration InitSent one-time deletion transition",
	),
	(
		"delete_pq_keypair",
		"BeaconState::InitSent{pending,..}=>Some(pending.aborted_state())",
		"registration InitSent PQ deletion transition",
	),
	(
		"delete_pq_keypair",
		"self.state=BeaconState::Aborted{control};",
		"registration PQ deletion terminal state",
	),
	(
		"finish_registration",
		"letaborted=match&self.state{BeaconState::InitSent{pending,..}=>pending.aborted_state(),_=>returnNone,};",
		"registration finish InitSent gate",
	),
];

const SERVER_LIFECYCLE: &[(&str, &str)] = &[
	(
		"pubstructRegistrationOutput{agreement:beaconcrypt_core::agreement::ServerAgreement,}",
		"initial ratchet RegistrationOutput storage",
	),
	(
		"fnget_shared_secret(&mutself,buffer:&[u8])->Option<RegistrationOutput>{",
		"initial ratchet Server RegistrationOutput return signature",
	),
	(
		"fnbuild_registration_response(&mutself,reg_out:RegistrationOutput,data:Option<&[u8]>,)->Option<RegResponse>{",
		"initial ratchet Server RegistrationOutput by-value consumer signature",
	),
	(
		"known_ids:HashMap<u64,EstablishedRemote<crypto_sign::PublicKey>>",
		"registration numeric peer map",
	),
	(
		"consumed_registrations:HashSet<[u8;verified_pqxdh::REGISTRATION_ID_SIZE]>",
		"registration consumed-ID set",
	),
];

pub(super) fn authentication(snapshot: &Snapshot) -> Result<(), String> {
	for &(scope, function, wanted, label) in AUTHENTICATION {
		check(snapshot, "registration", scope, function, wanted, label)?;
	}
	for &(function, wanted, label) in NATIVE_AUTHENTICATION {
		check(snapshot, "auth", "", function, wanted, label)?;
	}
	let hash = body(snapshot, "auth", "", "execute_hash")?;
	let expected = "letmutstate=hash_state()?;matchrequest{beaconcrypt_core::registration::HashRequest::Single(input)=>state.update(input),beaconcrypt_core::registration::HashRequest::Triple(parts)=>{forpartinparts{state.update(part);}}}finish_hash(state)";
	if hash != expected {
		return Err(
			"MLDSA adapter hashes exactly the requested bytes once before finalizing".into(),
		);
	}
	Ok(())
}

pub(super) fn agreement(snapshot: &Snapshot) -> Result<(), String> {
	for &(scope, function, wanted, label) in AGREEMENT {
		check(snapshot, "agreement", scope, function, wanted, label)?;
	}
	let dh = body(snapshot, "agreement", "impl<'a> DhPending", "request")?;
	for &wanted in DH_REQUESTS {
		require_once(&dh, wanted, "registration exact role-selected DH request")?;
	}
	let driver = body(snapshot, "pqxdh", "", "execute_agreement")?;
	for &wanted in NATIVE_AGREEMENT {
		require_once(
			&driver,
			wanted,
			"registration exact native agreement request interpretation",
		)?;
	}
	Ok(())
}

pub(super) fn completion(snapshot: &Snapshot) -> Result<(), String> {
	for &(scope, function, wanted, label) in COMPLETION {
		check(snapshot, "registration", scope, function, wanted, label)?;
	}
	Ok(())
}

pub(super) fn runtime(snapshot: &Snapshot) -> Result<(), String> {
	authentication(snapshot)?;
	for &(name, scope, function, wanted, label) in ADDITIONAL {
		check(snapshot, name, scope, function, wanted, label)?;
	}
	agreement(snapshot)?;
	completion(snapshot)?;
	let accept = body(snapshot, "server", "", "get_shared_secret")?;
	require_ordered_once(
		&accept,
		&[
			"letregistration=decode_init(buffer)?;",
			"letpacket=InitPacket::from_slices(",
			"auth::authenticate_init(self.authentication_pin()?,packet)?;",
			"letregistration_id=*authenticated.registration_id().as_bytes();",
			"validate_registration_status(status)",
			"self.consumed_registrations.try_reserve(1)",
			"agreement::begin_server_agreement(control,status,authenticated)",
			"AgreementEffect::ServerComplete(agreement)=>agreement",
			"self.consumed_registrations.insert(registration_id)",
			"Some(RegistrationOutput{agreement})",
		],
		"registration Server validate-reserve-derive-consume order",
	)?;
	let finish = body(snapshot, "beacon", "", "finish_registration")?;
	require_ordered_once(
		&finish,
		&[
			"std::mem::replace(&mutself.state,BeaconState::Aborted{control:aborted})",
			"decode_response(bytes)",
			"auth::authenticate_response(pending,packet)",
			"agreement::begin_beacon_agreement(authenticated)",
			"registration::begin_beacon_completion(agreement)",
			"letmuteffect=matchpending.resume(Some(response))",
			"registration::BeaconInitialOpen::KdfRequested(pending)",
			"registration::BeaconInitialOpen::CommitmentRequested(mutpending)",
			"registration::BeaconInitialOpen::AeadRequested(pending)",
			"pending.finish(plaintext.as_deref())",
			"completed.into_parts()",
			"self.identity_key_kid=binding.assigned_key_id();",
			"self.state=BeaconState::Established{control,binding,ratchet:RatchetManager::from_kernel(kernel),};",
		],
		"registration Beacon authenticated completion and terminal failure order",
	)?;
	let publish = body(snapshot, "server", "", "build_registration_response")?;
	require_ordered_once(
		&publish,
		&[
			"registration_response_len(plaintext.len(),next_key_id)?;",
			"letRegistrationOutput{agreement}=reg_out;",
			"registration::begin_server_completion(",
			"letresponse=crate::ratchet::ratchet_hkdf(pending.request());",
			"execute_seal_request(pending.request())",
			"pending.resume(detached_view)",
			"execute_commitment_hash(pending.transcript_mut())",
			"execute_write_request(pending.request())",
			"pending.resume(ciphertext.as_deref())",
			"auth::execute_hash(&pending.request())",
			"self.mldsa_identity.sign_requested(&pending.request())",
			"crate::wire::encode_response(KexResponse{",
			"ready.publish(buffer).ok()?.into_parts()",
			"self.known_ids.insert(",
			"self.control=next_control;",
		],
		"MLDSA token binding and signed publication precede commit",
	)?;
	let initial = body(
		snapshot,
		"registration",
		"impl<'a> BeaconInitialKdf",
		"resume",
	)?;
	require_once(
		&initial,
		"records::begin_record_receive(kernel,1,self.agreement.application_ciphertext,self.agreement.binding.associated_data(),self.agreement.candidate.server_key_id(),)",
		"registration core implicit sequence and pinned sender",
	)?;
	let opened = body(snapshot, "registration", "impl BeaconRecordAead", "finish")?;
	require_ordered_once(
		&opened,
		&[
			"let(kernel,opened)=self.pending.finish(plaintext);",
			"letopened=matchopened",
			"ifopened.plaintext.len()<=crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE",
			".split_at(crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE)",
			"authenticate_registration_key_id_binding(",
			".finish(authenticated.assigned_key_id())",
			"crate::pqxdh::beacon_commit(authenticated)",
		],
		"registration initial open authentication before commit",
	)?;
	let seal = body(snapshot, "registration", "impl ServerRecordWrite", "resume")?;
	require_ordered_once(
		&seal,
		&[
			"let(kernel,sealed)=self.pending.finish(ciphertext);",
			"letciphertext=matchsealed",
			"ifciphertext.len()!=length",
			"build_response_prefix(",
			"letassigned_id=encode_u64_le(self.state.candidate.key_id());",
			"Ok(ServerResponseHash{",
		],
		"registration exact seal output before response authentication",
	)?;
	let root = body(snapshot, "agreement", "impl<'a> RootKdfPending", "resume")?;
	require_ordered_once(
		&root,
		&[
			"letSome(root)=rootelse",
			"match&mutself.candidate",
			"letroot=RatchetChain::from_bytes(root);",
			"matchself.candidate{AgreementCandidate::Server{pending,binding}",
		],
		"registration root KDF result and erasure before completion",
	)?;
	let root_input = compact(&uncommented_rust(&snapshot.core_pqxdh)?);
	require_once(
		&root_input,
		"#[cfg_attr(not(hax_compilation),derive(zeroize::Zeroize,zeroize::ZeroizeOnDrop))]pubstructRootKeyInput{bytes:[u8;ROOT_KEY_INPUT_SIZE],}",
		"registration native root transcript ownership and erasure contract",
	)?;
	let registration = compact(&uncommented_rust(&snapshot.core_registration)?);
	for wanted in [
		"pubstructAuthenticatedInit{registration:VerifiedInitKex,binding:RegistrationBinding,}",
		"pubstructAuthenticatedResponse<'a>{pending:BeaconPending,packet:ResponsePacket<'a>,}",
		"pubstructBeaconPending{control:crate::pqxdh::BeaconInitSent,binding:RegistrationBinding,}",
	] {
		require_once(
			&registration,
			wanted,
			"registration private provenance capabilities",
		)?;
	}
	Ok(())
}

pub(super) fn lifecycle(snapshot: &Snapshot) -> Result<(), String> {
	runtime(snapshot)?;
	for &(function, wanted, label) in BEACON_LIFECYCLE {
		check(snapshot, "beacon", "", function, wanted, label)?;
	}
	let bundle = body(snapshot, "beacon", "", "get_registration_bundle")?;
	require_ordered_once(
		&bundle,
		&[
			"crate::wire::encode_init(InitKex{",
			"ready.publish(buffer).ok()?.into_parts()",
			"letprevious=std::mem::replace(&mutself.state,fallback);",
			"Some(buffer)",
		],
		"registration serialization-to-InitSent order",
	)?;
	let (before, after) = bundle
		.split_once("letprevious=std::mem::replace(&mutself.state,fallback);")
		.ok_or("registration missing state replacement")?;
	if before.contains("self.state=BeaconState::") {
		return Err("registration Beacon state changed before successful serialization".into());
	}
	if after.contains('?') {
		return Err("registration fallible work moved after state replacement".into());
	}
	let beacon = compact(&uncommented_rust(&snapshot.adapter_beacon)?);
	for (constructor, expected) in [
		("self.state=BeaconState::Fresh{", 1),
		("self.state=BeaconState::FreshWithCoins{", 1),
		("self.state=BeaconState::InitSent{", 2),
		("self.state=BeaconState::Established{", 1),
	] {
		if super::count(&beacon, constructor) != expected {
			return Err(format!(
				"registration Beacon eligible-state publication graph changed: {constructor}"
			));
		}
	}
	let server = compact(&uncommented_rust(&snapshot.adapter_server)?);
	for &(wanted, label) in SERVER_LIFECYCLE {
		require_once(&server, wanted, label)?;
	}
	check(
		snapshot,
		"server",
		"",
		"get_shared_secret",
		"letstatus=ifself.consumed_registrations.contains(&registration_id){verified_pqxdh::RegistrationStatus::Consumed}else{verified_pqxdh::RegistrationStatus::Fresh};",
		"registration Server replay-status polarity",
	)?;
	let accept = body(snapshot, "server", "", "get_shared_secret")?;
	let (_, after) = accept
		.split_once("letinserted=self.consumed_registrations.insert(registration_id);")
		.ok_or("registration missing consumption insertion")?;
	if super::count(&accept, "self.consumed_registrations.insert(") != 1 {
		return Err("registration Server consumed-ID insertion family count changed".into());
	}
	if after.contains('?') {
		return Err("registration fallible work moved after consumption insertion".into());
	}
	if after.contains("returnNone") {
		return Err("registration explicit failure moved after consumption insertion".into());
	}
	if body(snapshot, "server", "", "build_registration_response")?
		.contains("consumed_registrations")
	{
		return Err("registration replay-set mutation during later response construction".into());
	}
	super::record_effects::validate(snapshot)?;
	Ok(())
}

fn source_mut<'a>(snapshot: &'a mut Snapshot, name: &str) -> &'a mut String {
	match name {
		"registration" => &mut snapshot.core_registration,
		"records" => &mut snapshot.core_record_effects,
		"ratchet" => &mut snapshot.adapter_ratchet,
		"core-pqxdh" => &mut snapshot.core_pqxdh,
		"agreement" => &mut snapshot.core_agreement,
		"auth" => &mut snapshot.adapter_auth,
		"pqxdh" => &mut snapshot.adapter_pqxdh,
		"beacon" => &mut snapshot.adapter_beacon,
		"server" => &mut snapshot.adapter_server,
		_ => panic!("unknown registration mutation source {name}"),
	}
}

/// Find reviewed operands without depending on rustfmt's choice of line breaks.
pub(super) fn replace_contract(
	snapshot: &mut Snapshot,
	name: &str,
	scope: &str,
	function: &str,
	from: &str,
	to: &str,
) {
	let source = source_mut(snapshot, name);
	*source = uncommented_rust(source).unwrap();
	let scope_start = if scope.is_empty() {
		0
	} else {
		source.find(scope).expect("missing mutation scope")
	};
	let marker = format!("fn {function}");
	let mut search_start = scope_start;
	let function_start = loop {
		let start = search_start
			+ source[search_start..]
				.find(&marker)
				.expect("missing mutation function");
		let mut parentheses = 0usize;
		let mut brackets = 0usize;
		let mut declaration = false;
		for byte in source[start..].bytes() {
			match byte {
				b'(' => parentheses += 1,
				b')' => parentheses = parentheses.saturating_sub(1),
				b'[' => brackets += 1,
				b']' => brackets = brackets.saturating_sub(1),
				b'{' if parentheses == 0 && brackets == 0 => break,
				b';' if parentheses == 0 && brackets == 0 => {
					declaration = true;
					break;
				}
				_ => {}
			}
		}
		if !declaration {
			break start;
		}
		search_start = start + marker.len();
	};
	let positions: Vec<_> = source[function_start..]
		.char_indices()
		.filter(|(_, c)| !c.is_whitespace())
		.map(|(i, _)| function_start + i)
		.collect();
	let text = compact(&source[function_start..]);
	let from = compact(from);
	let offset = text.find(&from).unwrap_or_else(|| {
		panic!("missing registration mutation operand {name}::{scope}::{function}: {from}")
	});
	let start = positions[offset];
	let end = positions[offset + from.len() - 1] + 1;
	source.replace_range(start..end, to);
}

#[test]
fn extracted_registration_operand_and_continuation_mutations_are_rejected() {
	let baseline = Snapshot::production();
	lifecycle(&baseline).unwrap();
	let mut contracts = Vec::new();
	for &(scope, function, wanted, label) in AUTHENTICATION.iter().chain(COMPLETION) {
		contracts.push(("registration", scope, function, wanted, label));
	}
	for &(scope, function, wanted, label) in AGREEMENT {
		contracts.push(("agreement", scope, function, wanted, label));
	}
	for &(function, wanted, label) in NATIVE_AUTHENTICATION {
		contracts.push(("auth", "", function, wanted, label));
	}
	for &(function, wanted, label) in BEACON_LIFECYCLE {
		contracts.push(("beacon", "", function, wanted, label));
	}
	contracts.extend_from_slice(ADDITIONAL);
	for &wanted in DH_REQUESTS {
		contracts.push((
			"agreement",
			"impl<'a> DhPending",
			"request",
			wanted,
			"registration exact role-selected DH request",
		));
	}
	for &wanted in NATIVE_AGREEMENT {
		contracts.push((
			"pqxdh",
			"",
			"execute_agreement",
			wanted,
			"registration exact native agreement interpretation",
		));
	}
	let mut count = 0;
	// Every retained request, rejection and publication anchor rejects both omission and duplication.
	// Operand substitutions below exercise the failure, role, identity, field and response wiring.
	for &(name, scope, function, wanted, label) in &contracts {
		for (mutation, replacement) in [
			("omitted", "reviewed_mutation_omitted()".to_owned()),
			("duplicated", format!("{wanted}{wanted}")),
		] {
			let mut changed = baseline.clone();
			replace_contract(&mut changed, name, scope, function, wanted, &replacement);
			assert!(
				lifecycle(&changed).is_err(),
				"{mutation} {name}::{scope}::{function}: {label}"
			);
			count += 1;
		}
		for (from, to) in [
			("self.pre_key", "self.one_time_key"),
			(
				"DhSecretRole::LocalIdentity",
				"DhSecretRole::ServerEphemeral",
			),
			(
				"DhSecretRole::ServerEphemeral",
				"DhSecretRole::LocalIdentity",
			),
			("DhSecretRole::BeaconPrekey", "DhSecretRole::BeaconOneTime"),
			("DhSecretRole::BeaconOneTime", "DhSecretRole::BeaconPrekey"),
			(
				"registration.beacon_prekey_public_key()",
				"registration.beacon_one_time_public_key()",
			),
			(
				"registration.beacon_one_time_public_key()",
				"registration.beacon_prekey_public_key()",
			),
			("self.state.remote_identity", "replacement_identity"),
			("response.ephemeral_key", "replacement_ephemeral"),
			("keys.beacon_prekey", "keys.beacon_one_time"),
			("keys.beacon_one_time", "keys.beacon_prekey"),
			("keys.beacon_kem?", "replacement_kem_secret"),
			("request.public_key", "replacement_public_key"),
			("pending.public_key()?", "replacement_kem_key"),
			("pending.ciphertext()?", "replacement_ciphertext"),
			("None,request.input", "Some(replacement_salt),request.input"),
			("expand(32,", "expand(64,"),
			("Some(request.info)", "Some(replacement_info)"),
			("self.pending,response", "replacement_pending,response"),
			("resume(verified)", "resume(false)"),
			("public_key[index+1]", "public_key[index]"),
			("identity_key[index+1]", "identity_key[index]"),
			("key_id_binding()", "replacement_binding()"),
			("self.kernel.take()", "Some(replacement_kernel)"),
			("self.kernel.is_some()", "false"),
			("ciphertext.len()!=length", "false"),
			(
				"plaintext:&opened.plaintext",
				"plaintext:replacement_plaintext",
			),
			("sequence:opened.seq", "sequence:1"),
			(
				"sender_key_id:opened.key_id",
				"sender_key_id:request.sender_key_id",
			),
			("kernel,application", "replacement_kernel,application"),
			("kernel,self.encoded", "replacement_kernel,self.encoded"),
			("root_key_input_mut().clear()", "replacement_clear()"),
			("message.identity_key", "message.ephemeral_key"),
			("message.ephemeral_key", "message.identity_key"),
			("message.application_ciphertext", "replacement_ciphertext"),
			("binding.assigned_key_id()", "self.identity_key_kid"),
			(
				"binding.beacon_identity_public_key()",
				"self.identity_pk().as_bytes()",
			),
			(
				"remote_kid,EstablishedRemote",
				"self.identity_key_kid,EstablishedRemote",
			),
			(
				"RatchetManager::from_kernel(kernel)",
				"RatchetManager::default()",
			),
			("self.one_time_key", "self.pre_key"),
			("self.pq_key", "self.pre_key"),
			("self.identity_key", "self.pre_key"),
			("packet.fields()", "replacement_fields"),
			("binding.identity_key_id", "0"),
			("binding.identity_public_key", "replacement_identity"),
			("server_pin.public_key()", "replacement_pin"),
			("self.input", "replacement_input"),
			("self.state.packet.mldsa_public_key", "replacement_key"),
			("self.state.packet.signature", "replacement_signature"),
			("SIGNING_CONTEXT", "[0;32]"),
			("AuthRole::Beacon", "AuthRole::Server"),
			("AuthRole::Server", "AuthRole::Beacon"),
			("!verified", "false"),
			("!=SIGN_TYPE_ED25519", "==SIGN_TYPE_ED25519"),
			("SignedKeyStage::PqKey", "SignedKeyStage::PreKey"),
			("SignedKeyStage::PreKey", "SignedKeyStage::OneTimeKey"),
			(
				"self.state.packet.pre_key",
				"self.state.packet.one_time_key",
			),
			(
				"self.state.packet.one_time_key",
				"self.state.packet.pre_key",
			),
			("self.public_key", "replacement_public_key"),
			("opened!=", "opened=="),
			("signed[64..]", "signed[0..]"),
			("self.server_pin", "replacement_pin"),
			("self.state.init_hash", "replacement_hash"),
			("fingerprint,", "[0;64],"),
			("pending.binding.init_hash()", "&[0;64]"),
			("packet.public.identity_key", "packet.public.ephemeral_key"),
			("packet.public.ephemeral_key", "packet.public.identity_key"),
			("packet.public.kem_cipher_text", "replacement_kem"),
			("self.packet.application", "replacement_application"),
			("self.assigned_id", "replacement_id"),
			(
				"self.pending.binding.server_pin().public_key()",
				"replacement_key",
			),
			("self.packet.signature", "replacement_signature"),
			(
				"self.started.message.identity_key()",
				"replacement_identity",
			),
			("self.beacon_mldsa", "replacement_mldsa"),
			(
				"self.state.started.message.prekey()",
				"self.state.started.message.one_time_key()",
			),
			(
				"self.state.started.message.one_time_key()",
				"self.state.started.message.prekey()",
			),
			(
				"self.state.started.message.pq_key()",
				"self.state.started.message.prekey()",
			),
			("self.state.beacon_identity", "replacement_identity"),
			("signed.get(64..)", "signed.get(0..)"),
			(
				"!=Some(self.request().message)",
				"==Some(self.request().message)",
			),
			("self.state.original_control", "replacement_control"),
			("self.state.started.state", "replacement_control"),
			("self.binding", "replacement_binding"),
			("authenticated.into_parts()", "replacement_parts"),
			("registration.beacon_pq_public_key()", "replacement_kem_key"),
			("response.kem_cipher_text", "replacement_ciphertext"),
			("state.dh1.as_bytes()", "state.dh2.as_bytes()"),
			("state.dh2.as_bytes()", "state.dh1.as_bytes()"),
			("state.dh3.as_bytes()", "state.dh4.as_bytes()"),
			("state.dh4.as_bytes()", "state.dh3.as_bytes()"),
			("state.kem.as_bytes()", "state.dh4.as_bytes()"),
			("binding.server_pin().binding()", "replacement_binding"),
			("state.ephemeral_public_key", "replacement_ephemeral"),
			("state.kem_ciphertext", "replacement_kem"),
			("response.identity_key", "replacement_identity"),
			("response.key_id", "0"),
			(
				"shared_secrets:secrets",
				"shared_secrets:replacement_secrets",
			),
			("info:pqxdh::PQXDH_INFO", "info:replacement_info"),
			("agreement.root.as_bytes()", "&[0;32]"),
			("&agreement.candidate", "&replacement_candidate"),
			("&candidate", "&replacement_candidate"),
			("application.is_empty()", "false"),
			("!agreement.binding.matches_server(current_pin)", "false"),
			("agreement.pending", "replacement_pending"),
			("current_pin.binding()", "replacement_binding"),
			("availability,", "replacement_availability,"),
			(
				"self.agreement.application_ciphertext",
				"replacement_ciphertext",
			),
			("self.agreement.binding.associated_data()", "&[0;281]"),
			("sequence:1", "sequence:3"),
			("self.agreement.candidate.server_key_id()", "0"),
			("send_sequence()!=0", "send_sequence()!=1"),
			("receive_sequence()!=1", "receive_sequence()!=3"),
			("receive_cache_len()!=0", "false"),
			("opened.sequence!=1", "opened.sequence!=3"),
			("opened.plaintext.len()<=", "opened.plaintext.len()<"),
			(
				"split_at(crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE)",
				"split_at(0)",
			),
			(
				"opened.sender_key_id",
				"self.agreement.candidate.server_key_id()",
			),
			("prefix,", "replacement_prefix,"),
			(
				"self.prefix,self.application",
				"self.application,&self.prefix",
			),
			("self.binding.associated_data()", "&[0;281]"),
			(
				"self.candidate.server_identity_key_id()",
				"self.candidate.key_id()",
			),
			("self.candidate.key_id()", "0"),
			("send_sequence()!=1", "send_sequence()!=0"),
			("receive_sequence()!=0", "receive_sequence()!=1"),
			("self.binding.init_hash()", "&[0;64]"),
			(
				"self.candidate.server_identity_public_key()",
				"replacement_identity",
			),
			(
				"self.candidate.ephemeral_public_key()",
				"replacement_ephemeral",
			),
			("self.candidate.kem_ciphertext()", "replacement_kem"),
			("self.ciphertext", "replacement_ciphertext"),
			("self.binding.server_pin().public_key()", "replacement_key"),
			("self.signature", "replacement_signature"),
			("request.input", "replacement_input"),
			("&request.context", "&[]"),
			("request.signature.as_slice()", "replacement_signature"),
			("request.public_key.as_slice()", "replacement_public_key"),
			("self.public_key()!=*request.public_key", "false"),
			("pending.resume(verified)", "pending.resume(true)"),
			("forpartinparts", "forpartinparts.iter().rev()"),
			(
				"matches!(&self.state,BeaconState::Fresh{..})",
				"matches!(&self.state,BeaconState::InitSent{..})",
			),
			("Some(crypto_kx::KeyPair::generate().ok()?)", "None"),
			("_=>returnNone", "_=>unreachable!()"),
			(
				"identity_public_key:*self.identity_pk().as_bytes()",
				"identity_public_key:*self.server_id().as_bytes()",
			),
			(
				"prekey_public_key:prekey_public",
				"prekey_public_key:onetime_public",
			),
			("pq_public_key:pq_public", "pq_public_key:replacement_pq"),
			(
				"one_time_public_key:onetime_public",
				"one_time_public_key:prekey_public",
			),
			(
				"request.message,self.identity_sk()",
				"replacement_message,self.identity_sk()",
			),
			("self.identity_pk().as_bytes()==request.public_key", "true"),
			("pending.resume(signed.as_deref())", "pending.resume(None)"),
			("message.fields.identity_key", "message.fields.pre_key"),
			("message.fields.pre_key", "message.fields.one_time_key"),
			("message.fields.one_time_key", "message.fields.pre_key"),
			("message.fields.pq_key", "message.fields.pre_key"),
			("message.fields.mldsa_public_key", "replacement_public_key"),
			("message.signature", "replacement_signature"),
			(
				"ready.publish(buffer)",
				"ready.publish(Some(replacement_bytes))",
			),
			("pending.abort()", "replacement_abort"),
			("pending.aborted_state()", "replacement_abort"),
			(
				"BeaconState::InitSent{pending,..}",
				"BeaconState::Fresh{pending,..}",
			),
		] {
			if wanted.contains(from) {
				let mut changed = baseline.clone();
				let replacement = wanted.replacen(from, to, 1);
				replace_contract(&mut changed, name, scope, function, wanted, &replacement);
				assert!(
					lifecycle(&changed).is_err(),
					"operand {from} in {name}::{scope}::{function}: {label}"
				);
				count += 1;
			}
		}
	}
	eprintln!("extracted registration source mutations: {count}");
	assert_eq!(
		count, 511,
		"reviewed registration coverage unexpectedly changed"
	);
}

#[test]
fn registration_failure_bypass_and_publication_order_controls_are_rejected() {
	let baseline = Snapshot::production();
	lifecycle(&baseline).unwrap();
	let mut count = 0;
	for (target, scope, function, from, to) in [
		(
			"server",
			"",
			"get_shared_secret",
			"letstatus=ifself.consumed_registrations.contains(&registration_id)",
			"letstatus=ifself.known_ids.contains_key(&self.identity_key_kid)",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"RegistrationStatus::Consumed}else{verified_pqxdh::RegistrationStatus::Fresh",
			"RegistrationStatus::Fresh}else{verified_pqxdh::RegistrationStatus::Consumed",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"validate_registration_status(status).ok()?;",
			"validate_registration_status(status).ok();",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"self.consumed_registrations.try_reserve(1).ok()?;",
			"let _ = self.consumed_registrations.capacity();",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"self.consumed_registrations.insert(registration_id)",
			"self.consumed_registrations.insert([0;64])",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"debug_assert!(inserted);",
			"debug_assert!(inserted); let _late = Some(())?;",
		),
		(
			"server",
			"",
			"get_shared_secret",
			"debug_assert!(inserted);",
			"debug_assert!(inserted); if !inserted { return None; }",
		),
		(
			"server",
			"",
			"build_registration_response",
			"letcontrol=self.control;",
			"self.consumed_registrations.clear(); let control = self.control;",
		),
		(
			"beacon",
			"",
			"get_registration_bundle",
			"letbuffer=crate::wire::encode_init(InitKex{",
			"self.state = BeaconState::Aborted { control: verified_pqxdh::beacon_abort_fresh(control) }; let buffer = crate::wire::encode_init(InitKex {",
		),
		(
			"beacon",
			"",
			"get_registration_bundle",
			"letprevious=std::mem::replace(&mutself.state,fallback);",
			"let previous = std::mem::replace(&mut self.state,fallback); let _late = Some(())?;",
		),
		(
			"beacon",
			"",
			"finish_registration",
			"std::mem::replace(&mutself.state,BeaconState::Aborted{control:aborted})",
			"std::mem::replace(&mut self.state, replacement_state)",
		),
		(
			"pqxdh",
			"",
			"execute_agreement",
			"pending.resume(root)",
			"pending.resume(Some([0;32]))",
		),
		(
			"auth",
			"",
			"execute_hash",
			"finish_hash(state)",
			"state.update(&[0]); finish_hash(state)",
		),
		(
			"auth",
			"",
			"execute_hash",
			"forpartinparts{state.update(part);}",
			"for part in parts { state.update(part); state.update(part); }",
		),
		(
			"registration",
			"impl<'a> InitEd25519Verification",
			"resume",
			"self.pre_key,one_time_key,self.pq_key,",
			"one_time_key,self.pre_key,self.pq_key,",
		),
		(
			"registration",
			"impl<'a> InitEd25519Verification",
			"resume",
			"self.pre_key,one_time_key,self.pq_key,",
			"self.pre_key,self.pre_key,self.pq_key,",
		),
		(
			"registration",
			"impl<'a> InitMldsaVerification",
			"resume",
			"if!verified||self.state.packet.identity_key[0]!=SIGN_TYPE_ED25519",
			"if false",
		),
		(
			"registration",
			"impl<'a> InitMldsaVerification",
			"resume",
			"if!verified||self.state.packet.identity_key[0]!=SIGN_TYPE_ED25519",
			"if !verified && self.state.packet.identity_key[0]!=SIGN_TYPE_ED25519",
		),
		(
			"registration",
			"impl<'a> BeaconInitialKdf",
			"resume",
			"records::begin_record_receive(kernel,1,",
			"records::begin_record_receive(kernel,2,",
		),
		(
			"registration",
			"impl<'a> BeaconInitialKdf",
			"resume",
			"records::begin_record_receive(kernel,1,",
			"records::begin_record_receive(kernel,0,",
		),
		(
			"registration",
			"impl<'a> BeaconInitialKdf",
			"resume",
			"records::begin_record_receive(kernel,1,",
			"records::begin_record_receive(kernel,self.agreement.candidate.server_key_id(),",
		),
		(
			"registration",
			"impl<'a> BeaconInitialKdf",
			"resume",
			"records::begin_record_receive(kernel,1,",
			"records::begin_record_receive(kernel,u64::MAX,",
		),
		(
			"registration",
			"impl BeaconRecordAead",
			"finish",
			"opened.plaintext.len()<=crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE",
			"false",
		),
		(
			"records",
			"impl<'a> SealAead",
			"resume",
			"self.seal.sequence(),",
			"0,",
		),
		(
			"records",
			"impl<'a> SealAead",
			"resume",
			"self.seal.sequence(),",
			"2,",
		),
		(
			"registration",
			"impl ServerRecordWrite",
			"resume",
			"ifciphertext.len()!=length",
			"if false",
		),
	] {
		let mut changed = baseline.clone();
		replace_contract(&mut changed, target, scope, function, from, to);
		assert!(
			lifecycle(&changed).is_err(),
			"bypass {target}::{scope}::{function}: {from}"
		);
		count += 1;
	}
	// A gate can remain textually present while moving after the operation it guards.
	for (target, scope, function, moved, before) in [
		(
			"registration",
			"impl BeaconRecordAead",
			"finish",
			"ifopened.plaintext.len()<=crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE{returnErr(rejected);}",
			"letbinding=self.agreement.binding.finish(authenticated.assigned_key_id());",
		),
		(
			"server",
			"",
			"build_registration_response",
			"self.control=next_control;",
			"letold=self.known_ids.insert(",
		),
	] {
		let mut changed = baseline.clone();
		replace_contract(&mut changed, target, scope, function, moved, "");
		replace_contract(
			&mut changed,
			target,
			scope,
			function,
			before,
			&format!("{moved}{before}"),
		);
		assert!(
			lifecycle(&changed).is_err(),
			"order {target}::{function}: {moved}"
		);
		count += 1;
	}
	assert_eq!(count, 28);
}

#[test]
fn registration_capabilities_keep_private_provenance_and_native_erasure() {
	let baseline = Snapshot::production();
	lifecycle(&baseline).unwrap();
	for (target, scope, from, to) in [
		(
			"registration",
			"pub struct AuthenticatedInit",
			"registration: VerifiedInitKex,",
			"pub registration: VerifiedInitKex,",
		),
		(
			"registration",
			"pub struct AuthenticatedResponse",
			"pending: BeaconPending,",
			"pub pending: BeaconPending,",
		),
		(
			"registration",
			"pub struct BeaconPending",
			"control: crate::pqxdh::BeaconInitSent,",
			"pub control: crate::pqxdh::BeaconInitSent,",
		),
		(
			"core-pqxdh",
			"",
			"#[cfg_attr(not(hax_compilation), derive(zeroize::Zeroize, zeroize::ZeroizeOnDrop))]\npub struct RootKeyInput",
			"#[cfg_attr(not(hax_compilation), derive(zeroize::Zeroize))]\npub struct RootKeyInput",
		),
	] {
		let mut changed = baseline.clone();
		super::replace_once_after(source_mut(&mut changed, target), scope, from, to);
		assert!(
			lifecycle(&changed).is_err(),
			"private capability or erasure mutation: {target}::{from}"
		);
	}
}

#[test]
fn registration_wire_fields_and_attached_signature_roles_cannot_be_substituted() {
	let baseline = Snapshot::production();
	lifecycle(&baseline).unwrap();
	let mut checked = 0;
	for (target, scope, function, values) in [
		(
			"server",
			"",
			"get_shared_secret",
			&[
				"registration.identity_key",
				"registration.pre_key",
				"registration.one_time_key",
				"registration.pq_key",
			][..],
		),
		(
			"beacon",
			"",
			"get_registration_bundle",
			&[
				"message.fields.identity_key",
				"message.fields.pre_key",
				"message.fields.one_time_key",
				"message.fields.pq_key",
			][..],
		),
		(
			"server",
			"",
			"build_registration_response",
			&[
				"message.identity_key",
				"message.ephemeral_key",
				"message.kem_cipher_text",
				"message.application_ciphertext",
			][..],
		),
		(
			"beacon",
			"",
			"finish_registration",
			&[
				"response.identity_key",
				"response.ephemeral_key",
				"response.kem_cipher_text",
				"response.app_cipher_text",
			][..],
		),
		(
			"registration",
			"impl BeaconEd25519Signing",
			"request",
			&[
				"self.state.started.message.prekey()",
				"self.state.started.message.one_time_key()",
				"self.state.started.message.pq_key()",
			][..],
		),
	] {
		for (i, from) in values.iter().enumerate() {
			for (j, to) in values.iter().enumerate() {
				if i == j {
					continue;
				}
				let mut changed = baseline.clone();
				replace_contract(&mut changed, target, scope, function, from, to);
				assert!(
					lifecycle(&changed).is_err(),
					"same-typed substitution {target}::{function}: {from} -> {to}"
				);
				checked += 1;
			}
		}
	}
	assert_eq!(checked, 54);
}
