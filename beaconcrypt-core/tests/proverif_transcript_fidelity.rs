// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::commitment::{
	AEAD_KEY_SIZE, AEAD_NONCE_SIZE, AEAD_TAG_SIZE, COMMITMENT_TRANSCRIPT_SIZE,
	build_commitment_transcript,
};
use beaconcrypt_core::pqxdh::{
	self, BeaconCoins, BeaconFresh, BeaconStartInputs, InitialRatchetKdfResponse,
	PqxdhSharedSecrets, ServerBinding,
};
use beaconcrypt_core::{
	RATCHET_KDF_OUTPUT_SIZE, SYM_RATCHET_INFO, SendStart, begin_send, split_ratchet_kdf_output,
};

const INTERFACE: &str = include_str!("../proofs/pro-verif/production-transcript-interface.pvl");
const CRYPTO_MODEL: &str = include_str!("../proofs/pro-verif/crypto.pvl");
const ENVIRONMENT_MODEL: &str = include_str!("../proofs/pro-verif/environment.pvl");
const ACTIVE_QUANTUM_WITNESS: &str = include_str!("../proofs/pro-verif/active-quantum-witness.pvl");
const EXTRACTION_MODEL: &str = include_str!("../proofs/pro-verif/extraction/lib.pvl");
const CORE_MAKEFILE: &str = include_str!("../Makefile");
const FORMAL_WORKFLOW: &str = include_str!("../../.github/workflows/formal-verification.yml");
const ADAPTER_PQXDH: &str = include_str!("../../beaconcrypt/src/pqxdh.rs");
const ADAPTER_RATCHET: &str = include_str!("../../beaconcrypt/src/ratchet.rs");
const ADAPTER_SHARED: &str = include_str!("../../beaconcrypt/src/shared.rs");
const ADAPTER_SERVER: &str = include_str!("../../beaconcrypt/src/server.rs");
const ADAPTER_BEACON: &str = include_str!("../../beaconcrypt/src/beacon.rs");
const PHASE2_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/phase2.capnp");

const FACT_PREFIX: &str = "(* @beaconcrypt-fidelity-v1 ";
const FACT_SUFFIX: &str = " *)";
const EXPECTED_FACTS: &[&str] = &[
	"schema=1",
	"domain.count=2",
	"domain.pqxdh.hex=426561636f6e637279707450717864685f435552564532353531395f5348412d3531325f4d4c2d4b454d2d373638",
	"domain.pqxdh.length=46",
	"domain.symmetric.hex=53796d526174636865745f484b44465f5348412d3531325f43484143484132305f504f4c5931333035",
	"domain.symmetric.length=41",
	"domain.distinct=true",
	"labels.absent=aead,ctx,direction,sequence,session,phase",
	"hkdf.hash=sha512",
	"hkdf.salt=none",
	"hkdf.output_length_domain=absent",
	"hkdf.root.domain=pqxdh",
	"hkdf.root.output=32",
	"hkdf.initial.domain=symmetric",
	"hkdf.initial.output=64",
	"hkdf.initial.left=0..32",
	"hkdf.initial.right=32..64",
	"hkdf.initial.server=send:left,receive:right",
	"hkdf.initial.beacon=send:right,receive:left",
	"hkdf.step.domain=symmetric",
	"hkdf.step.output=76",
	"hkdf.step.key=0..32",
	"hkdf.step.next_chain=32..64",
	"hkdf.step.nonce=64..76",
	"hkdf.symmetric.prefix=initial[0..64]=step[0..64]",
	"root.padding.byte=ff",
	"root.padding.length=32",
	"root.fields=padding,dh1,dh2,dh3,dh4,kem_shared_secret",
	"root.field_lengths=32,32,32,32,32,32",
	"root.length=192",
	"encoding.ed25519=01,pk",
	"encoding.mlkem768=03,pk",
	"encoding.x25519_prekey=04,80,pk",
	"encoding.x25519_one_time=04,81,pk",
	"associated_data.fields=tag_ed25519(server_identity),tag_ed25519(beacon_identity),pqxdh_domain,symmetric_ratchet_domain",
	"associated_data.offsets=0..33,33..66,66..112,112..153",
	"associated_data.length=153",
	"associated_data.domains=hkdf_domain_values",
	"aead.primitive=chacha20poly1305_ietf",
	"aead.fields=key,nonce,associated_data,plaintext",
	"aead.key_length=32",
	"aead.nonce_length=12",
	"aead.tag_length=16",
	"aead.tag=detached",
	"aead.sequence=absent",
	"aead.sender_id=absent",
	"aead.label=none",
	"ctx.hash=blake2b512",
	"ctx.fields=key,nonce,associated_data,retained_aead_tag,le64(sequence),le64(sender_id)",
	"ctx.offsets=0..32,32..44,44..197,197..213,213..221,221..229",
	"ctx.length=229",
	"ctx.sequence_encoding=le64",
	"ctx.sender_id_encoding=le64",
	"ctx.label=none",
	"phase2.response.constructor=kex_response",
	"phase2.response.field_count=5",
	"phase2.response.field.0=identityKey@0:server_identity",
	"phase2.response.field.1=ephemeralKey@1:server_ephemeral",
	"phase2.response.field.2=kemCipherText@2:kem_ciphertext",
	"phase2.response.field.3=appCipherText@3:initial_frame",
	"phase2.response.field.4=keyId@4:assigned_key_id",
	"phase2.response.server_writes=candidate.server_identity_public_key,candidate.ephemeral_public_key,candidate.kem_ciphertext,initial_encrypted_frame,candidate.key_id",
	"phase2.response.beacon_reads=response_server_identity,server_ephemeral,kem_ciphertext,initial_frame,assigned_key_id",
	"agreement.constructor=establishment_transcript",
	"agreement.field_count=18",
	"agreement.fields=server_identity,beacon_identity,authenticated_init_kex,registration_id,prekey,one_time_x25519,selected_mlkem_public_key,server_ephemeral,kem_ciphertext,initial_frame,response,root_input,root,associated_data,assigned_beacon_key_id,pinned_server_key_id,session_id,registration_origin",
];

#[derive(Clone)]
struct Snapshot {
	interface: String,
	crypto: String,
	environment: String,
	active_quantum_witness: String,
	makefile: String,
	phase2_schema: String,
	adapter_server: String,
	adapter_beacon: String,
}

impl Snapshot {
	fn production() -> Self {
		Self {
			interface: INTERFACE.to_owned(),
			crypto: CRYPTO_MODEL.to_owned(),
			environment: ENVIRONMENT_MODEL.to_owned(),
			active_quantum_witness: ACTIVE_QUANTUM_WITNESS.to_owned(),
			makefile: CORE_MAKEFILE.to_owned(),
			phase2_schema: PHASE2_SCHEMA.to_owned(),
			adapter_server: ADAPTER_SERVER.to_owned(),
			adapter_beacon: ADAPTER_BEACON.to_owned(),
		}
	}
}

fn parse_facts(source: &str) -> Result<Vec<String>, String> {
	let mut facts = Vec::new();
	for (line_number, line) in source.lines().enumerate() {
		if !line.contains("@beaconcrypt-fidelity-v1") {
			continue;
		}
		let trimmed = line.trim();
		let Some(payload) = trimmed
			.strip_prefix(FACT_PREFIX)
			.and_then(|line| line.strip_suffix(FACT_SUFFIX))
		else {
			return Err(format!(
				"malformed fidelity fact on line {}",
				line_number + 1
			));
		};
		let Some((key, value)) = payload.split_once('=') else {
			return Err(format!("fidelity fact lacks '=': {payload}"));
		};
		if key.is_empty() || value.is_empty() || key.contains(char::is_whitespace) {
			return Err(format!("invalid fidelity fact: {payload}"));
		}
		if facts
			.iter()
			.any(|fact: &String| fact.split_once('=').is_some_and(|(seen, _)| seen == key))
		{
			return Err(format!("duplicate fidelity fact: {key}"));
		}
		facts.push(payload.to_owned());
	}
	Ok(facts)
}

fn validate_manifest(source: &str) -> Result<(), String> {
	let facts = parse_facts(source)?;
	if facts.len() != EXPECTED_FACTS.len() {
		return Err(format!(
			"expected {} fidelity facts, found {}",
			EXPECTED_FACTS.len(),
			facts.len()
		));
	}
	for (index, (actual, expected)) in facts.iter().zip(EXPECTED_FACTS).enumerate() {
		if actual != expected {
			let key = expected.split_once('=').unwrap().0;
			return Err(format!(
				"fidelity fact {index} ({key}) changed: expected {expected}, found {actual}"
			));
		}
	}
	Ok(())
}

fn fact_value<'a>(facts: &'a [String], key: &str) -> &'a str {
	facts
		.iter()
		.find_map(|fact| {
			let (candidate, value) = fact.split_once('=').unwrap();
			(candidate == key).then_some(value)
		})
		.unwrap_or_else(|| panic!("missing fidelity fact: {key}"))
}

fn decode_hex(value: &str) -> Vec<u8> {
	assert_eq!(value.len() % 2, 0);
	value
		.as_bytes()
		.chunks_exact(2)
		.map(|pair| u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap())
		.collect()
}

fn remove_comments(source: &str, open: &str, close: &str) -> Result<String, String> {
	let mut result = source.to_owned();
	while let Some(start) = result.find(open) {
		let Some(relative_end) = result[start + open.len()..].find(close) else {
			return Err(format!("unterminated {open} comment"));
		};
		let end = start + open.len() + relative_end + close.len();
		result.replace_range(start..end, "");
	}
	Ok(result)
}

fn uncommented_pv(source: &str) -> Result<String, String> {
	remove_comments(source, "(*", "*)")
}

fn uncommented_rust(source: &str) -> Result<String, String> {
	let source = remove_comments(source, "/*", "*/")?;
	Ok(source
		.lines()
		.map(|line| line.split_once("//").map_or(line, |(code, _)| code))
		.collect::<Vec<_>>()
		.join("\n"))
}

fn uncommented_capnp(source: &str) -> String {
	source
		.lines()
		.map(|line| line.split_once('#').map_or(line, |(code, _)| code))
		.collect::<Vec<_>>()
		.join("\n")
}

fn compact(source: &str) -> String {
	source
		.chars()
		.filter(|character| !character.is_whitespace())
		.collect()
}

fn require(source: &str, wanted: &str, label: &str) -> Result<(), String> {
	if source.contains(wanted) {
		Ok(())
	} else {
		Err(format!("missing exact {label}: {wanted}"))
	}
}

fn forbid(source: &str, unwanted: &str, label: &str) -> Result<(), String> {
	if source.contains(unwanted) {
		Err(format!("unexpected {label}: {unwanted}"))
	} else {
		Ok(())
	}
}

fn count(source: &str, needle: &str) -> usize {
	source.match_indices(needle).count()
}

fn parse_call(source: &str, open: usize) -> Result<(Vec<String>, usize), String> {
	if source.as_bytes().get(open) != Some(&b'(') {
		return Err("call parser did not start at '('".to_owned());
	}
	let bytes = source.as_bytes();
	let mut nesting = 1usize;
	let mut start = open + 1;
	let mut arguments = Vec::new();
	let mut index = open + 1;
	while index < bytes.len() {
		match bytes[index] {
			b'(' | b'[' | b'{' => nesting += 1,
			b')' => {
				nesting -= 1;
				if nesting == 0 {
					arguments.push(source[start..index].to_owned());
					return Ok((arguments, index + 1));
				}
			}
			b']' | b'}' => nesting -= 1,
			b',' if nesting == 1 => {
				arguments.push(source[start..index].to_owned());
				start = index + 1;
			}
			_ => {}
		}
		index += 1;
	}
	Err("unterminated call".to_owned())
}

fn arguments_after(source: &str, marker: &str) -> Result<Vec<String>, String> {
	let Some(start) = source.find(marker) else {
		return Err(format!("missing call marker: {marker}"));
	};
	parse_call(source, start + marker.len() - 1).map(|(arguments, _)| arguments)
}

fn all_arguments(source: &str, function: &str) -> Result<Vec<Vec<String>>, String> {
	let marker = format!("{function}(");
	let mut calls = Vec::new();
	let mut offset = 0;
	while let Some(relative) = source[offset..].find(&marker) {
		let start = offset + relative;
		let (arguments, end) = parse_call(source, start + marker.len() - 1)?;
		calls.push(arguments);
		offset = end;
	}
	Ok(calls)
}

fn rust_body(source: &str, name: &str) -> Result<String, String> {
	let source = uncommented_rust(source)?;
	let marker = format!("fn {name}");
	let mut search_start = 0;
	let open = loop {
		let Some(relative_start) = source[search_start..].find(&marker) else {
			return Err(format!("missing Rust function body: {name}"));
		};
		let start = search_start + relative_start;
		let tail = &source[start..];
		let mut parentheses = 0usize;
		let mut brackets = 0usize;
		let mut relative_open = None;
		let mut declaration = false;
		for (offset, byte) in tail.bytes().enumerate() {
			match byte {
				b'(' => parentheses += 1,
				b')' => parentheses = parentheses.saturating_sub(1),
				b'[' => brackets += 1,
				b']' => brackets = brackets.saturating_sub(1),
				b'{' if parentheses == 0 && brackets == 0 => {
					relative_open = Some(offset);
					break;
				}
				b';' if parentheses == 0 && brackets == 0 => {
					declaration = true;
					break;
				}
				_ => {}
			}
		}
		if let Some(relative_open) = relative_open {
			break start + relative_open;
		}
		if declaration {
			search_start = start + marker.len();
			continue;
		}
		return Err(format!("missing body for Rust function: {name}"));
	};
	let bytes = source.as_bytes();
	let mut nesting = 1usize;
	let mut index = open + 1;
	while index < bytes.len() {
		match bytes[index] {
			b'{' => nesting += 1,
			b'}' => {
				nesting -= 1;
				if nesting == 0 {
					return Ok(compact(&source[open + 1..index]));
				}
			}
			_ => {}
		}
		index += 1;
	}
	Err(format!("unterminated Rust function: {name}"))
}

fn require_one_call(
	source: &str,
	function: &str,
	expected: &[&str],
	label: &str,
) -> Result<(), String> {
	let calls = all_arguments(source, function)?;
	let expected = expected
		.iter()
		.map(|argument| (*argument).to_owned())
		.collect::<Vec<_>>();
	if calls == [expected.clone()] {
		Ok(())
	} else {
		Err(format!(
			"{label} changed: expected one {function} call with {expected:?}, found {calls:?}"
		))
	}
}

fn require_once(source: &str, wanted: &str, label: &str) -> Result<(), String> {
	let occurrences = count(source, wanted);
	if occurrences == 1 {
		Ok(())
	} else {
		Err(format!(
			"{label} changed: expected one exact occurrence of {wanted}, found {occurrences}"
		))
	}
}

fn validate_phase2_source(snapshot: &Snapshot) -> Result<(), String> {
	let schema = compact(&uncommented_capnp(&snapshot.phase2_schema));
	require(
		&schema,
		"structKexResponse{identityKey@0:Data;ephemeralKey@1:Data;kemCipherText@2:Data;appCipherText@3:Data;keyId@4:UInt64;}",
		"Phase-2 response schema",
	)?;

	let server = rust_body(&snapshot.adapter_server, "build_registration_response")?;
	require(
		&server,
		"letremote_kid=candidate.key_id();",
		"Phase-2 assigned key-ID source",
	)?;
	for (function, expected, label) in [
		(
			"bundle.set_identity_key",
			"candidate.server_identity_public_key()",
			"Phase-2 server identity mapping",
		),
		(
			"bundle.set_ephemeral_key",
			"candidate.ephemeral_public_key()",
			"Phase-2 server ephemeral mapping",
		),
		(
			"bundle.set_kem_cipher_text",
			"candidate.kem_ciphertext()",
			"Phase-2 server KEM-ciphertext mapping",
		),
		(
			"bundle.set_app_cipher_text",
			"&encrypted.ciphertext",
			"Phase-2 server initial-frame mapping",
		),
		(
			"bundle.set_key_id",
			"remote_kid",
			"Phase-2 server assigned-ID mapping",
		),
	] {
		require_one_call(&server, function, &[expected], label)?;
	}

	let beacon = rust_body(&snapshot.adapter_beacon, "finish_registration")?;
	for (wanted, label) in [
		(
			"crypto_sign::PublicKey::from_bytes(response.get_identity_key().ok()?).ok()?",
			"Phase-2 beacon identity mapping",
		),
		(
			"crypto_kx::PublicKey::from_bytes(response.get_ephemeral_key().ok()?).ok()?",
			"Phase-2 beacon ephemeral mapping",
		),
		(
			"crypto_kem::mlkem768::Ciphertext::from_bytes(response.get_kem_cipher_text().ok()?).ok()?",
			"Phase-2 beacon KEM-ciphertext mapping",
		),
		(
			"decrypt_message_with_ratchet(response.get_app_cipher_text().ok()?,candidate.server_key_id(),&associated_data,&mutratchet,)?",
			"Phase-2 beacon initial-frame mapping",
		),
		(
			"assigned_key_id:response.get_key_id(),",
			"Phase-2 beacon assigned-ID mapping",
		),
	] {
		require_once(&beacon, wanted, label)?;
	}
	Ok(())
}

fn validate_pv(snapshot: &Snapshot) -> Result<(), String> {
	let interface = compact(&uncommented_pv(&snapshot.interface)?);
	let crypto = compact(&uncommented_pv(&snapshot.crypto)?);
	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	let active_quantum_witness = compact(&uncommented_pv(&snapshot.active_quantum_witness)?);
	for declaration in [
		"typekey_id.",
		"typesequence.",
		"funsequence_le64(sequence):bitstring[data].",
		"funsender_id_le64(key_id):bitstring[data].",
		"funtag_ed25519(bitstring):bitstring[data].",
		"funtag_x25519_prekey(bitstring):bitstring[data].",
		"funtag_x25519_one_time(bitstring):bitstring[data].",
		"funtag_mlkem768(bitstring):bitstring[data].",
		"funpqxdh_ff32_padding():bitstring[data].",
		"funhkdf_sha512_no_salt(bitstring,kdf_domain):hkdf_stream.",
		"funbeaconcrypt_associated_data(bitstring,bitstring,kdf_domain,kdf_domain):bitstring[data].",
		"funaead_cipher(bitstring,bitstring,bitstring,bitstring):bitstring.",
		"funaead_tag(bitstring,bitstring,bitstring,bitstring):bitstring.",
		"functx_preimage(bitstring,bitstring,bitstring,bitstring,bitstring,bitstring):bitstring[data].",
		"typeestablishment_transcript_t.",
	] {
		require(&interface, declaration, "interface declaration")?;
		forbid(&crypto, declaration, "duplicate crypto declaration")?;
	}
	if count(&interface, "):kdf_domain[data].") != 2
		|| count(&interface, "funpqxdh_domain():kdf_domain[data].") != 1
		|| count(
			&interface,
			"funsymmetric_ratchet_domain():kdf_domain[data].",
		) != 1
	{
		return Err("interface must declare exactly two production domains".to_owned());
	}
	forbid(&crypto, "kdf_domain", "extra crypto-domain declaration")?;
	if count(&crypto, "hkdf_sha512_no_salt(") != 6 {
		return Err("crypto model must contain exactly six production HKDF calls".to_owned());
	}
	require(
		&crypto,
		"letfunpqxdh_root(input:bitstring)=hkdf_first_32(hkdf_sha512_no_salt(input,pqxdh_domain())).",
		"PQXDH root domain",
	)?;
	require(
		&crypto,
		"letfunserver_to_beacon_chain(root:bitstring)=hkdf_first_32(hkdf_sha512_no_salt(root,symmetric_ratchet_domain())).",
		"initial left projection",
	)?;
	require(
		&crypto,
		"letfunbeacon_to_server_chain(root:bitstring)=hkdf_second_32(hkdf_sha512_no_salt(root,symmetric_ratchet_domain())).",
		"initial right projection",
	)?;
	require(
		&crypto,
		"letfunratchet_next(chain:bitstring)=hkdf_second_32(hkdf_sha512_no_salt(chain,symmetric_ratchet_domain())).",
		"step next-chain projection",
	)?;
	require(
		&crypto,
		"letfunratchet_material(chain:bitstring)=ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt(chain,symmetric_ratchet_domain())),hkdf_final_12(hkdf_sha512_no_salt(chain,symmetric_ratchet_domain()))).",
		"step key/nonce projections",
	)?;

	let ctx = arguments_after(&interface, "blake2b512(ctx_preimage(")?;
	let expected_ctx = [
		"key",
		"nonce",
		"associated_data",
		"retained_aead_tag",
		"sequence_le64(message_sequence)",
		"sender_id_le64(sender_id)",
	];
	if ctx != expected_ctx {
		return Err(format!("CTX preimage field order changed: {ctx:?}"));
	}
	for label in [
		"funaead_label",
		"functx_label",
		"fundirection_label",
		"funsequence_label",
		"funsession_label",
		"funphase_label",
		"funoutput_length_domain",
	] {
		forbid(&interface, label, "invented production label")?;
		forbid(&crypto, label, "invented production label")?;
	}
	require(
		&crypto,
		"aead_cipher(material_key(material),material_nonce(material),associated_data,plaintext)",
		"seal AEAD input",
	)?;
	require(
		&crypto,
		"ctx_commitment(material_key(material),material_nonce(material),associated_data,aead_tag(material_key(material),material_nonce(material),associated_data,plaintext),message_sequence,sender_id)",
		"seal CTX input",
	)?;
	require(
		&crypto,
		"ctx_preimage(key,nonce,associated_data,aead_tag(key,nonce,associated_data,plaintext),sequence_le64(message_sequence),sender_id_le64(sender_id))",
		"open CTX input",
	)?;
	require(
		&environment,
		"funkex_response(bitstring,bitstring,bitstring,bitstring,key_id):bitstring[data].",
		"Phase-2 response constructor",
	)?;
	require(
		&environment,
		"letkex_response(response_server_identity,server_ephemeral,kem_ciphertext,initial_frame,assigned_key_id)=responsein",
		"Phase-2 response destructuring order",
	)?;
	let response_construction = "letresponse=kex_response(server_identity,server_ephemeral,kem_ciphertext,initial_frame,assigned_key_id)in";
	if count(&environment, response_construction) != 2 {
		return Err(format!(
			"Phase-2 response construction order changed: expected two exact constructions, found {}",
			count(&environment, response_construction)
		));
	}
	require(
		&active_quantum_witness,
		"letkex_response(response_server_identity,server_ephemeral,kem_ciphertext,initial_frame,assigned_key_id)=responsein",
		"active-quantum Phase-2 response destructuring order",
	)?;

	let constructor = "funestablishment_transcript(bitstring,bitstring,beaconcrypt_core__pqxdh__t_InitKex,beaconcrypt_core__pqxdh__t_RegistrationId,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring,beaconcrypt_core__pqxdh__t_RootKeyInput,bitstring,bitstring,key_id,key_id,bitstring,bitstring):establishment_transcript_t[data].";
	require(
		&environment,
		constructor,
		"18-field establishment constructor",
	)?;
	let expected = [
		"server_identity",
		"beacon_identity",
		"core_init",
		"registration_id",
		"beacon_prekey",
		"beacon_one_time",
		"beacon_pq",
		"server_ephemeral",
		"kem_ciphertext",
		"initial_frame",
		"response",
		"root_input",
		"root",
		"associated_data",
		"assigned_key_id",
		"SERVER_KEY_ID",
		"session",
		"registration_session",
	];
	for (marker, label) in [
		(
			"letbeacon_establishment=establishment_transcript(",
			"beacon establishment emitter",
		),
		(
			"letserver_establishment=establishment_transcript(",
			"server establishment emitter",
		),
		(
			"letmalicious_establishment=establishment_transcript(",
			"malicious establishment emitter",
		),
	] {
		let arguments = arguments_after(&environment, marker)?;
		if arguments != expected {
			return Err(format!("{label} fields changed: {arguments:?}"));
		}
	}
	let ad_calls = all_arguments(
		&environment,
		"beaconcrypt_core__pqxdh__build_associated_data",
	)?;
	if ad_calls.len() != 3
		|| ad_calls
			.iter()
			.any(|arguments| arguments != &["server_identity", "beacon_identity"])
	{
		return Err(format!(
			"associated-data identity order changed: {ad_calls:?}"
		));
	}

	let extraction = compact(&uncommented_pv(EXTRACTION_MODEL)?);
	for reduction in [
		"reducforallidentity:bitstring,prekey:bitstring,one_time:bitstring,pq:bitstring;beaconcrypt_core__pqxdh__registration_id(beaconcrypt_core__pqxdh__VerifiedInitKex(identity,prekey,one_time,pq))=beaconcrypt_core__pqxdh__RegistrationId(registration_identifier(identity,one_time)).",
		"reducforalldh1:bitstring,dh2:bitstring,dh3:bitstring,dh4:bitstring,kem:bitstring;beaconcrypt_core__pqxdh__build_root_key_input(beaconcrypt_core__pqxdh__PqxdhSharedSecrets(dh1,dh2,dh3,dh4,kem))=beaconcrypt_core__pqxdh__RootKeyInput(pqxdh_root_input(pqxdh_ff32_padding(),dh1,dh2,dh3,dh4,kem)).",
		"reducforallserver_identity:bitstring,beacon_identity:bitstring;beaconcrypt_core__pqxdh__build_associated_data(server_identity,beacon_identity)=beaconcrypt_associated_data(tag_ed25519(server_identity),tag_ed25519(beacon_identity),pqxdh_domain(),symmetric_ratchet_domain()).",
	] {
		require(&extraction, reduction, "checked extraction replacement")?;
	}
	Ok(())
}

fn scenario_names(makefile: &str) -> Result<Vec<String>, String> {
	let start = makefile
		.find("PROVERIF_SCENARIOS :=")
		.ok_or_else(|| "missing PROVERIF_SCENARIOS".to_owned())?;
	let tail = &makefile[start..];
	let end = tail
		.find("\nPROVERIF_CHECK_TARGETS :=")
		.ok_or_else(|| "unterminated PROVERIF_SCENARIOS".to_owned())?;
	Ok(tail[..end]
		.lines()
		.skip(1)
		.map(|line| line.trim().trim_end_matches('\\').trim())
		.filter(|line| !line.is_empty())
		.map(str::to_owned)
		.collect())
}

fn validate_makefile(makefile: &str) -> Result<(), String> {
	if count(makefile, "-lib $(PROVERIF_INTERFACE)") != 1
		|| count(makefile, "-lib $(PROVERIF_DIR)/crypto.pvl") != 1
	{
		return Err("interface and crypto must each load once in PROVERIF_CRYPTO_LIBS".to_owned());
	}
	require(
		makefile,
		"$(PROVERIF_CHECK_TARGETS): check-proverif-transcript-fidelity",
		"per-scenario fidelity prerequisite",
	)?;
	require(
		makefile,
		"check-proverif-passive-reachability check-proverif-quantum-capabilities: check-proverif-transcript-fidelity",
		"auxiliary ProVerif fidelity prerequisite",
	)?;
	let scenarios = scenario_names(makefile)?;
	if scenarios.len() != 26 {
		return Err(format!(
			"expected 26 ProVerif scenarios, found {}",
			scenarios.len()
		));
	}
	for scenario in scenarios {
		let marker = format!("check-proverif-{scenario}:");
		let start = makefile
			.find(&marker)
			.ok_or_else(|| format!("missing scenario target: {scenario}"))?;
		let tail = &makefile[start..];
		let block = &tail[..tail.find("\n\n").unwrap_or(tail.len())];
		let loaders = [
			"$(PROVERIF_COMMON_LIBS)",
			"$(PROVERIF_QUANTUM_LIBS)",
			"$(PROVERIF_AEAD_CONTROL_LIBS)",
			"$(PROVERIF_CRYPTO_LIBS)",
		];
		if loaders
			.iter()
			.filter(|loader| block.contains(**loader))
			.count() != 1
		{
			return Err(format!(
				"scenario {scenario} does not load the interface exactly once"
			));
		}
	}
	let workflow = compact(FORMAL_WORKFLOW);
	require(
		&workflow,
		"-name:ProVeriftranscriptfidelitytarget:check-proverif-transcript-fidelity",
		"dedicated transcript-fidelity CI entry",
	)?;
	Ok(())
}

fn validate_adapters() -> Result<(), String> {
	let pqxdh = rust_body(ADAPTER_PQXDH, "derive_root_key_input")?;
	require(
		&pqxdh,
		"crypto_kdf::hkdf::sha512::extract(None,input.as_bytes())",
		"no-salt PQXDH extract",
	)?;
	require(
		&pqxdh,
		"crypto_kdf::hkdf::sha512::expand(KEX_KDF_OUT_LEN,Some(PQXDH_INFO),&prk)",
		"PQXDH label/output request",
	)?;
	let shared = compact(&uncommented_rust(ADAPTER_SHARED)?);
	require(
		&shared,
		"pubconstKEX_KDF_OUT_LEN:usize=32usize;",
		"32-byte root output",
	)?;
	let symmetric = rust_body(ADAPTER_RATCHET, "symmetric_ratchet_hkdf")?;
	require(
		&symmetric,
		"crypto_kdf::hkdf::sha512::extract(None,request.input())",
		"no-salt symmetric extract",
	)?;
	require(
		&symmetric,
		"crypto_kdf::hkdf::sha512::expand(OUTPUT_SIZE,Some(request.info()),&prk)",
		"symmetric label/output request",
	)?;
	let record_executor = rust_body(ADAPTER_RATCHET, "ratchet_hkdf")?;
	require(
		&record_executor,
		"RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))",
		"record-step shared HKDF executor",
	)?;
	let initial_executor = rust_body(ADAPTER_RATCHET, "initial_ratchet_hkdf")?;
	require(
		&initial_executor,
		"symmetric_ratchet_hkdf(request)",
		"initial shared HKDF executor",
	)?;
	let ratchet = compact(&uncommented_rust(ADAPTER_RATCHET)?);
	require(
		&ratchet,
		"pubconstCOMMITMENT_SIZE:usize=64;",
		"64-byte production commitment output",
	)?;
	let seal = rust_body(ADAPTER_RATCHET, "seal_frame")?;
	require(
		&seal,
		"crypto_aead::chacha20poly1305_ietf::encrypt_detached(context.bytes,Some(context.associated_data.as_slice()),&nonce,&key,)",
		"production detached AEAD seal",
	)?;
	require(
		&seal,
		"build_commitment(material,context.associated_data.as_slice(),tag.as_slice(),key_seq,context.sender_kid,)",
		"production seal commitment inputs",
	)?;
	let open = rust_body(ADAPTER_RATCHET, "open_frame")?;
	require(
		&open,
		"build_commitment(material,context.associated_data.as_slice(),&context.ciphertext[ct_len-COMMITMENT_SIZE-AEAD_TAG_LEN..ct_len-COMMITMENT_SIZE],key_seq,context.sender_kid,)",
		"production retained-tag commitment inputs",
	)?;
	require(
		&open,
		"crypto_aead::chacha20poly1305_ietf::decrypt(&context.ciphertext[..ct_len-COMMITMENT_SIZE],Some(context.associated_data.as_slice()),&nonce,&key,)",
		"production AEAD open",
	)?;
	let commitment = rust_body(ADAPTER_RATCHET, "build_commitment")?;
	require(
		&commitment,
		"build_commitment_transcript(key,nonce,ad,tag,seq,kid)",
		"production CTX builder call",
	)?;
	require(
		&commitment,
		"crypto_generichash::generichash(input.as_bytes(),None,COMMITMENT_SIZE)",
		"unkeyed unlabeled BLAKE2b-512 call",
	)?;
	Ok(())
}

fn validate(snapshot: &Snapshot) -> Result<(), String> {
	validate_manifest(&snapshot.interface)?;
	validate_pv(snapshot)?;
	validate_phase2_source(snapshot)?;
	validate_makefile(&snapshot.makefile)
}

fn replace_once(source: &mut String, from: &str, to: &str) {
	let start = source
		.find(from)
		.unwrap_or_else(|| panic!("mutation anchor missing: {from}"));
	source.replace_range(start..start + from.len(), to);
}

fn mutate_fact(source: &mut String, key: &str, value: &str) {
	let marker = format!("{FACT_PREFIX}{key}=");
	let start = source
		.find(&marker)
		.unwrap_or_else(|| panic!("mutation fact missing: {key}"));
	let value_start = start + marker.len();
	let value_end = value_start + source[value_start..].find(FACT_SUFFIX).unwrap();
	source.replace_range(value_start..value_end, value);
}

fn assert_rejected(name: &str, diagnostic: &str, mutate: impl FnOnce(&mut Snapshot)) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate(&snapshot) {
		Ok(()) => panic!("mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"mutation {name} produced wrong diagnostic: {error}"
	);
}

fn omit_ctx(snapshot: &mut Snapshot, field: &str) {
	let anchor = "    ctx_preimage(\n";
	let call = snapshot.interface.find(anchor).unwrap();
	let with_comma = format!("      {field},\n");
	let without_comma = format!("      {field}\n");
	let (relative, length) = snapshot.interface[call..]
		.find(&with_comma)
		.map(|start| (start, with_comma.len()))
		.or_else(|| {
			snapshot.interface[call..]
				.find(&without_comma)
				.map(|start| (start, without_comma.len()))
		})
		.unwrap();
	let start = call + relative;
	snapshot.interface.replace_range(start..start + length, "");
}

#[test]
fn production_manifest_symbolic_model_and_adapters_are_exact() {
	validate(&Snapshot::production()).unwrap();
	validate_adapters().unwrap();
}

#[test]
fn compiled_core_matches_the_canonical_transcript() {
	let facts = parse_facts(INTERFACE).unwrap();
	assert_eq!(
		pqxdh::PQXDH_INFO.as_slice(),
		decode_hex(fact_value(&facts, "domain.pqxdh.hex"))
	);
	assert_eq!(
		SYM_RATCHET_INFO.as_slice(),
		decode_hex(fact_value(&facts, "domain.symmetric.hex"))
	);
	assert_ne!(pqxdh::PQXDH_INFO.as_slice(), SYM_RATCHET_INFO.as_slice());
	assert_eq!(pqxdh::PQXDH_INFO.len(), 46);
	assert_eq!(SYM_RATCHET_INFO.len(), 41);
	assert_eq!(pqxdh::ROOT_KEY_INPUT_SIZE, 192);
	assert_eq!(pqxdh::INITIAL_RATCHET_KDF_OUTPUT_SIZE, 64);
	assert_eq!(RATCHET_KDF_OUTPUT_SIZE, 76);

	let secrets = PqxdhSharedSecrets {
		dh1: [0x11; 32],
		dh2: [0x22; 32],
		dh3: [0x33; 32],
		dh4: [0x44; 32],
		kem_shared_secret: [0x55; 32],
	};
	let root = pqxdh::build_root_key_input(&secrets).unwrap();
	let root = root.as_bytes();
	assert_eq!(&root[0..32], &[0xff; 32]);
	assert_eq!(&root[32..64], &secrets.dh1);
	assert_eq!(&root[64..96], &secrets.dh2);
	assert_eq!(&root[96..128], &secrets.dh3);
	assert_eq!(&root[128..160], &secrets.dh4);
	assert_eq!(&root[160..192], &secrets.kem_shared_secret);

	let server_identity = [0xa1; 32];
	let beacon_identity = [0xb2; 32];
	let ad = pqxdh::build_associated_data(server_identity, beacon_identity);
	assert_eq!(ad.len(), 153);
	assert_eq!(ad[0], 0x01);
	assert_eq!(&ad[1..33], &server_identity);
	assert_eq!(ad[33], 0x01);
	assert_eq!(&ad[34..66], &beacon_identity);
	assert_eq!(&ad[66..112], pqxdh::PQXDH_INFO);
	assert_eq!(&ad[112..153], SYM_RATCHET_INFO);

	let prekey = [0xc3; 32];
	let one_time = [0xd4; 32];
	let pq_key = [0xe5; pqxdh::MLKEM768_PUBLIC_KEY_SIZE];
	let started = pqxdh::beacon_start(
		BeaconFresh::new(ServerBinding {
			identity_public_key: server_identity,
			identity_key_id: 7,
		}),
		BeaconStartInputs {
			identity_public_key: beacon_identity,
			prekey_public_key: prekey,
			pq_public_key: pq_key,
		},
		BeaconCoins {
			one_time_public_key: one_time,
		},
	);
	assert_eq!(started.message.identity_key()[0], 0x01);
	assert_eq!(&started.message.identity_key()[1..], &beacon_identity);
	assert_eq!(&started.message.prekey()[0..2], &[0x04, 0x80]);
	assert_eq!(&started.message.prekey()[2..], &prekey);
	assert_eq!(&started.message.one_time_key()[0..2], &[0x04, 0x81]);
	assert_eq!(&started.message.one_time_key()[2..], &one_time);
	assert_eq!(started.message.pq_key()[0], 0x03);
	assert_eq!(&started.message.pq_key()[1..], &pq_key);
	let verified = pqxdh::validate_init_kex(started.message).unwrap();
	assert_eq!(verified.beacon_prekey_public_key(), &prekey);
	assert_eq!(verified.beacon_one_time_public_key(), &one_time);
	assert_eq!(verified.beacon_pq_public_key(), &pq_key);

	let initial_output: [u8; 64] = core::array::from_fn(|index| index as u8);
	let server_chains = pqxdh::split_initial_ratchet_kdf_output(
		&initial_output,
		pqxdh::server_ratchet_initialization(),
	);
	let beacon_chains = pqxdh::split_initial_ratchet_kdf_output(
		&initial_output,
		pqxdh::beacon_ratchet_initialization(),
	);
	assert_eq!(
		server_chains.send_chain().as_bytes(),
		&initial_output[0..32]
	);
	assert_eq!(
		server_chains.receive_chain().as_bytes(),
		&initial_output[32..64]
	);
	assert_eq!(
		beacon_chains.send_chain().as_bytes(),
		&initial_output[32..64]
	);
	assert_eq!(
		beacon_chains.receive_chain().as_bytes(),
		&initial_output[0..32]
	);

	let step_output: [u8; 76] = core::array::from_fn(|index| index as u8);
	let step = split_ratchet_kdf_output(&step_output);
	assert_eq!(step.key().as_bytes(), &step_output[0..32]);
	assert_eq!(step.next_chain().as_bytes(), &step_output[32..64]);
	assert_eq!(step.nonce().as_bytes(), &step_output[64..76]);
	assert_eq!(server_chains.send_chain().as_bytes(), step.key().as_bytes());
	assert_eq!(
		server_chains.receive_chain().as_bytes(),
		step.next_chain().as_bytes()
	);

	let root = [0x36; 32];
	let pending = pqxdh::start_server_ratchet_kdf(&root);
	assert_eq!(pending.request().input(), &root);
	assert_eq!(pending.request().info(), SYM_RATCHET_INFO);
	let kernel = pqxdh::resume_initial_ratchet_kdf(
		pending,
		InitialRatchetKdfResponse::from_bytes(initial_output),
	);
	match begin_send(kernel, ()) {
		SendStart::SendKdfRequested(request) => {
			assert_eq!(request.request().input(), &initial_output[0..32]);
			assert_eq!(request.request().info(), SYM_RATCHET_INFO);
		}
		SendStart::SendExhausted { .. } => panic!("fresh ratchet unexpectedly exhausted"),
	}

	assert_eq!(AEAD_KEY_SIZE, 32);
	assert_eq!(AEAD_NONCE_SIZE, 12);
	assert_eq!(AEAD_TAG_SIZE, 16);
	assert_eq!(COMMITMENT_TRANSCRIPT_SIZE, 229);
	let key = core::array::from_fn(|index| index as u8);
	let nonce = core::array::from_fn(|index| 0x20 + index as u8);
	let associated_data = core::array::from_fn(|index| (index as u8).wrapping_add(0x40));
	let tag = core::array::from_fn(|index| 0xe0 + index as u8);
	let sequence = 0x0807_0605_0403_0201;
	let sender_id = 0x1817_1615_1413_1211;
	let transcript =
		build_commitment_transcript(&key, &nonce, &associated_data, &tag, sequence, sender_id);
	let bytes = transcript.as_bytes();
	assert_eq!(&bytes[0..32], &key);
	assert_eq!(&bytes[32..44], &nonce);
	assert_eq!(&bytes[44..197], &associated_data);
	assert_eq!(&bytes[197..213], &tag);
	assert_eq!(&bytes[213..221], &sequence.to_le_bytes());
	assert_eq!(&bytes[221..229], &sender_id.to_le_bytes());
}

#[test]
fn requested_transcript_mutations_are_rejected() {
	assert_rejected("pqxdh_label_byte", "domain.pqxdh.hex", |snapshot| {
		mutate_fact(
			&mut snapshot.interface,
			"domain.pqxdh.hex",
			"436561636f6e637279707450717864685f435552564532353531395f5348412d3531325f4d4c2d4b454d2d373638",
		);
	});
	assert_rejected("symmetric_label_byte", "domain.symmetric.hex", |snapshot| {
		mutate_fact(
			&mut snapshot.interface,
			"domain.symmetric.hex",
			"52796d526174636865745f484b44465f5348412d3531325f43484143484132305f504f4c5931333035",
		);
	});
	assert_rejected("aliased_domains", "PQXDH root domain", |snapshot| {
		replace_once(
			&mut snapshot.crypto,
			"hkdf_sha512_no_salt(input, pqxdh_domain())",
			"hkdf_sha512_no_salt(input, symmetric_ratchet_domain())",
		);
	});
	assert_rejected(
		"separate_initial_step_domain",
		"step next-chain projection",
		|snapshot| {
			snapshot.crypto = snapshot.crypto.replace(
				"hkdf_sha512_no_salt(chain, symmetric_ratchet_domain())",
				"hkdf_sha512_no_salt(chain, step_ratchet_domain())",
			);
		},
	);
	assert_rejected(
		"reversed_ad_identities",
		"associated-data identity order",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"        server_identity,\n        beacon_identity",
				"        beacon_identity,\n        server_identity",
			);
		},
	);
	assert_rejected(
		"swapped_x25519_roles",
		"encoding.x25519_prekey",
		|snapshot| {
			mutate_fact(
				&mut snapshot.interface,
				"encoding.x25519_prekey",
				"04,81,pk",
			);
			mutate_fact(
				&mut snapshot.interface,
				"encoding.x25519_one_time",
				"04,80,pk",
			);
		},
	);
	assert_rejected(
		"reordered_phase2_manifest_field",
		"phase2.response.field.3",
		|snapshot| {
			mutate_fact(
				&mut snapshot.interface,
				"phase2.response.field.3",
				"keyId@4:assigned_key_id",
			);
		},
	);
	for (name, key, value) in [
		(
			"changed_phase2_manifest_constructor",
			"phase2.response.constructor",
			"legacy_kex_response",
		),
		(
			"changed_phase2_manifest_field_count",
			"phase2.response.field_count",
			"4",
		),
		(
			"changed_phase2_manifest_field_0",
			"phase2.response.field.0",
			"ephemeralKey@1:server_ephemeral",
		),
		(
			"changed_phase2_manifest_field_1",
			"phase2.response.field.1",
			"identityKey@0:server_identity",
		),
		(
			"changed_phase2_manifest_field_2",
			"phase2.response.field.2",
			"appCipherText@3:initial_frame",
		),
		(
			"changed_phase2_manifest_field_4",
			"phase2.response.field.4",
			"appCipherText@3:initial_frame",
		),
		(
			"changed_phase2_manifest_server_writes",
			"phase2.response.server_writes",
			"candidate.ephemeral_public_key,candidate.server_identity_public_key,candidate.kem_ciphertext,initial_encrypted_frame,candidate.key_id",
		),
		(
			"changed_phase2_manifest_beacon_reads",
			"phase2.response.beacon_reads",
			"server_ephemeral,response_server_identity,kem_ciphertext,initial_frame,assigned_key_id",
		),
	] {
		assert_rejected(name, key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, value);
		});
	}
	assert_rejected(
		"legacy_phase2_symbolic_order",
		"Phase-2 response constructor",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"fun kex_response(\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring,\n  key_id\n): bitstring [data].",
				"fun kex_response(\n  bitstring,\n  bitstring,\n  bitstring,\n  key_id,\n  bitstring\n): bitstring [data].",
			);
		},
	);
	assert_rejected(
		"permuted_phase2_beacon_destructure",
		"Phase-2 response destructuring order",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"    response_server_identity,\n    server_ephemeral,\n    kem_ciphertext,\n    initial_frame,\n    assigned_key_id",
				"    server_ephemeral,\n    response_server_identity,\n    kem_ciphertext,\n    initial_frame,\n    assigned_key_id",
			);
		},
	);
	assert_rejected(
		"permuted_phase2_response_construction",
		"Phase-2 response construction order",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"        server_identity,\n        server_ephemeral,\n        kem_ciphertext,\n        initial_frame,\n        assigned_key_id",
				"        server_ephemeral,\n        server_identity,\n        kem_ciphertext,\n        initial_frame,\n        assigned_key_id",
			);
		},
	);
	assert_rejected(
		"permuted_active_quantum_phase2_destructure",
		"active-quantum Phase-2 response destructuring order",
		|snapshot| {
			replace_once(
				&mut snapshot.active_quantum_witness,
				"    response_server_identity,\n    server_ephemeral,\n    kem_ciphertext,\n    initial_frame,\n    assigned_key_id",
				"    server_ephemeral,\n    response_server_identity,\n    kem_ciphertext,\n    initial_frame,\n    assigned_key_id",
			);
		},
	);
	assert_rejected(
		"reordered_phase2_schema_fields",
		"Phase-2 response schema",
		|snapshot| {
			replace_once(
				&mut snapshot.phase2_schema,
				"    appCipherText @3 :Data;\n    # The ID assigned to this beacon instance's identity\n    keyId @4 :UInt64;",
				"    keyId @4 :UInt64;\n    # The encrypted initial application frame\n    appCipherText @3 :Data;",
			);
		},
	);
	assert_rejected(
		"omitted_phase2_schema_field",
		"Phase-2 response schema",
		|snapshot| {
			replace_once(
				&mut snapshot.phase2_schema,
				"    appCipherText @3 :Data;\n",
				"",
			);
		},
	);
	assert_rejected(
		"renamed_phase2_schema_field",
		"Phase-2 response schema",
		|snapshot| {
			replace_once(
				&mut snapshot.phase2_schema,
				"appCipherText @3",
				"initialFrame @3",
			);
		},
	);
	for (name, from, to, label) in [
		(
			"swapped_phase2_server_identity_mapping",
			"bundle.set_identity_key(candidate.server_identity_public_key());",
			"bundle.set_identity_key(candidate.ephemeral_public_key());",
			"Phase-2 server identity mapping",
		),
		(
			"swapped_phase2_server_ephemeral_mapping",
			"bundle.set_ephemeral_key(candidate.ephemeral_public_key());",
			"bundle.set_ephemeral_key(candidate.server_identity_public_key());",
			"Phase-2 server ephemeral mapping",
		),
		(
			"swapped_phase2_server_kem_mapping",
			"bundle.set_kem_cipher_text(candidate.kem_ciphertext());",
			"bundle.set_kem_cipher_text(&encrypted.ciphertext);",
			"Phase-2 server KEM-ciphertext mapping",
		),
		(
			"swapped_phase2_server_frame_mapping",
			"bundle.set_app_cipher_text(&encrypted.ciphertext);",
			"bundle.set_app_cipher_text(candidate.kem_ciphertext());",
			"Phase-2 server initial-frame mapping",
		),
		(
			"swapped_phase2_server_key_id_mapping",
			"bundle.set_key_id(remote_kid);",
			"bundle.set_key_id(candidate.server_identity_key_id());",
			"Phase-2 server assigned-ID mapping",
		),
	] {
		assert_rejected(name, label, |snapshot| {
			replace_once(&mut snapshot.adapter_server, from, to);
		});
	}
	for (name, from, to, label) in [
		(
			"swapped_phase2_beacon_identity_mapping",
			"response.get_identity_key()",
			"response.get_ephemeral_key()",
			"Phase-2 beacon identity mapping",
		),
		(
			"swapped_phase2_beacon_ephemeral_mapping",
			"response.get_ephemeral_key()",
			"response.get_identity_key()",
			"Phase-2 beacon ephemeral mapping",
		),
		(
			"swapped_phase2_beacon_kem_mapping",
			"response.get_kem_cipher_text()",
			"response.get_app_cipher_text()",
			"Phase-2 beacon KEM-ciphertext mapping",
		),
		(
			"swapped_phase2_beacon_frame_mapping",
			"response.get_app_cipher_text()",
			"response.get_kem_cipher_text()",
			"Phase-2 beacon initial-frame mapping",
		),
		(
			"swapped_phase2_beacon_key_id_mapping",
			"response.get_key_id()",
			"candidate.server_key_id()",
			"Phase-2 beacon assigned-ID mapping",
		),
	] {
		assert_rejected(name, label, |snapshot| {
			replace_once(&mut snapshot.adapter_beacon, from, to);
		});
	}
	assert_rejected(
		"agreement_without_selected_pqpk",
		"beacon establishment emitter",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"      beacon_pq,\n      server_ephemeral,",
				"      server_ephemeral,",
			);
		},
	);
	assert_rejected(
		"agreement_without_kem_ciphertext",
		"beacon establishment emitter",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"      kem_ciphertext,\n      initial_frame,",
				"      initial_frame,",
			);
		},
	);
	for (name, field) in [
		("ctx_without_key", "key"),
		("ctx_without_nonce", "nonce"),
		("ctx_without_associated_data", "associated_data"),
		("ctx_without_retained_aead_tag", "retained_aead_tag"),
		("ctx_without_sequence", "sequence_le64(message_sequence)"),
		("ctx_without_sender_id", "sender_id_le64(sender_id)"),
	] {
		assert_rejected(name, "CTX preimage field order", |snapshot| {
			omit_ctx(snapshot, field);
		});
	}
}
