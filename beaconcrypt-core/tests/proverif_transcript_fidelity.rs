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
const CORE_COMMITMENT: &str = include_str!("../src/commitment.rs");
const CORE_PQXDH: &str = include_str!("../src/pqxdh.rs");
const CRYPTOFRAME_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/cryptoframe.capnp");
const PHASE1_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/phase1.capnp");
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
	"phase1.init_kex.constructor=signed_init_kex",
	"phase1.init_kex.field_count=4",
	"phase1.init_kex.field.0=identityKey@0:encoded_ed25519_identity",
	"phase1.init_kex.field.1=preKey@1:signed_tagged_x25519_prekey",
	"phase1.init_kex.field.2=oneTimeKey@2:signed_tagged_x25519_one_time",
	"phase1.init_kex.field.3=pqKey@3:signed_tagged_mlkem768_public_key",
	"phase1.signature.primitive=ed25519",
	"phase1.signature.format=attached(signature||encoded_key)",
	"phase1.init_kex.beacon_writes=identityKey:identity,preKey:signed_prekey,oneTimeKey:signed_one_time,pqKey:signed_pq",
	"phase1.init_kex.beacon_signs=preKey:tag_x25519_prekey,oneTimeKey:tag_x25519_one_time,pqKey:tag_mlkem768",
	"phase1.init_kex.server_reads=identityKey,pqKey,preKey,oneTimeKey",
	"phase1.init_kex.server.verifies=pqKey:pq_verified,preKey:prekey_verified,oneTimeKey:onetime_verified;identity:remote_id",
	"phase1.init_kex.server.from_encoded=encoded_identity,prekey_verified,onetime_verified,pq_verified",
	"phase1.init_kex.server.validates=tag_ed25519,tag_x25519_prekey,tag_x25519_one_time,tag_mlkem768",
	"phase1.init_kex.symbolic.fields=encoded_identity,signed_prekey,signed_one_time,signed_pq",
	"phase1.init_kex.symbolic.producers=honest,malicious,active_quantum",
	"phase1.init_kex.symbolic.consumers=server,malicious_server,active_quantum",
	"phase1.init_kex.symbolic.validation=identity,prekey,one_time,pq",
	"phase2.response.constructor=kex_response",
	"phase2.response.field_count=5",
	"phase2.response.field.0=identityKey@0:server_identity",
	"phase2.response.field.1=ephemeralKey@1:server_ephemeral",
	"phase2.response.field.2=kemCipherText@2:kem_ciphertext",
	"phase2.response.field.3=appCipherText@3:initial_frame",
	"phase2.response.field.4=keyId@4:assigned_key_id",
	"phase2.response.server_writes=candidate.server_identity_public_key,candidate.ephemeral_public_key,candidate.kem_ciphertext,initial_encrypted_frame,candidate.key_id",
	"phase2.response.beacon_reads=response_server_identity,server_ephemeral,kem_ciphertext,initial_frame,assigned_key_id",
	"cryptoframe.schema.constructor=CryptoFrame",
	"cryptoframe.schema.id=ef858976d7f7863b",
	"cryptoframe.schema.field_count=3",
	"cryptoframe.schema.field.0=seq@0:sequence",
	"cryptoframe.schema.field.1=keyId@1:sender_id",
	"cryptoframe.schema.field.2=cipherText@2:ciphertext||retained_aead_tag||commitment",
	"cryptoframe.wire.key_id=sender_kid",
	"cryptoframe.local.encrypted.key_id=target_kid:not_serialized",
	"cryptoframe.seal.inputs=key:32,nonce:12,associated_data:153,plaintext",
	"cryptoframe.seal.detached_outputs=ciphertext,retained_aead_tag:16",
	"cryptoframe.seal.commitment.output=blake2b512_unkeyed_unlabeled:64",
	"cryptoframe.seal.commitment.input=existing_ctx_transcript",
	"cryptoframe.seal.commitment.context=selected_material,associated_data,retained_aead_tag,selected_sequence,sender_kid",
	"cryptoframe.seal.payload=ciphertext||retained_aead_tag||commitment",
	"cryptoframe.seal.payload.overhead=80",
	"cryptoframe.seal.setter_order=cipherText,seq,keyId",
	"cryptoframe.seal.serialize=TypedBuilder<CryptoFrame>,write_message(buffer)",
	"cryptoframe.seal.empty_plaintext=caller_rejects_before_ratchet",
	"cryptoframe.seal.one_use=returned_material,returned_sequence,frame_context,finish",
	"cryptoframe.open.empty_wire=rejected_before_parse",
	"cryptoframe.open.parse=capnp_typed_reader<CryptoFrame>",
	"cryptoframe.open.getter_order=keyId,cipherText,seq",
	"cryptoframe.open.sender_gate=parsed_sender_kid==expected_sender_kid:before_ratchet",
	"cryptoframe.open.length_gate=payload_length>80:before_ratchet",
	"cryptoframe.open.ratchet=begin_receive(parsed_sequence,frame_context)",
	"cryptoframe.open.one_use=returned_material,returned_sequence,frame_context,finish",
	"cryptoframe.open.commitment_slice=payload[last64..]",
	"cryptoframe.open.tag_slice=payload[len-80..len-64]",
	"cryptoframe.open.ciphertext_slice=payload[..len-80]",
	"cryptoframe.open.commitment.context=selected_material,associated_data,parsed_retained_aead_tag,selected_sequence,parsed_sender_kid",
	"cryptoframe.open.commitment.compare=libsodium_memcmp_call",
	"cryptoframe.open.order=commitment_equality_before_aead_decrypt",
	"cryptoframe.open.decrypt.input=ciphertext||retained_aead_tag",
	"cryptoframe.open.decrypt.excludes=commitment",
	"cryptoframe.open.decrypt.context=selected_material_key,selected_material_nonce,same_associated_data",
	"cryptoframe.open.result.metadata=parsed_sender_kid,parsed_sequence",
	"cryptoframe.symbolic.constructor=crypto_frame",
	"cryptoframe.symbolic.fields=ciphertext,retained_aead_tag,commitment,sequence,sender_id",
	"cryptoframe.symbolic.seal=exact_production_fields",
	"cryptoframe.symbolic.open=ideal_exact_constructor_rule",
	"cryptoframe.symbolic.retained_tag=shared_by_aead_and_commitment",
	"cryptoframe.symbolic.absent=frame_and_seal_arguments:target_id,direction,session,phase,aead_label,ctx_label",
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
	adapter_ratchet: String,
	core_commitment: String,
	core_pqxdh: String,
	cryptoframe_schema: String,
	phase1_schema: String,
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
			adapter_ratchet: ADAPTER_RATCHET.to_owned(),
			core_commitment: CORE_COMMITMENT.to_owned(),
			core_pqxdh: CORE_PQXDH.to_owned(),
			cryptoframe_schema: CRYPTOFRAME_SCHEMA.to_owned(),
			phase1_schema: PHASE1_SCHEMA.to_owned(),
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

fn require_ordered_once(source: &str, wanted: &[&str], label: &str) -> Result<(), String> {
	let mut cursor = 0usize;
	for item in wanted {
		let occurrences = count(source, item);
		if occurrences != 1 {
			return Err(format!(
				"{label} changed: expected one exact occurrence of {item}, found {occurrences}"
			));
		}
		let relative = source[cursor..]
			.find(item)
			.ok_or_else(|| format!("{label} changed: {item} is out of order"))?;
		cursor += relative + item.len();
	}
	Ok(())
}

fn validate_phase1_source(snapshot: &Snapshot) -> Result<(), String> {
	let schema = compact(&uncommented_capnp(&snapshot.phase1_schema));
	let expected_schema = "@0xd840dedb1017061a;structInitKex{identityKey@0:Data;preKey@1:Data;oneTimeKey@2:Data;pqKey@3:Data;}";
	if schema != expected_schema {
		return Err(format!(
			"Phase-1 InitKex schema changed: expected {expected_schema}, found {schema}"
		));
	}

	let core_start = rust_body(&snapshot.core_pqxdh, "beacon_start")?;
	for (wanted, label) in [
		(
			"identity_key:tag_sign_key(inputs.identity_public_key)",
			"Phase-1 core identity encoding",
		),
		(
			"prekey:tag_x25519_key(KEY_ROLE_PREKEY,inputs.prekey_public_key)",
			"Phase-1 core prekey encoding",
		),
		(
			"one_time_key:tag_x25519_key(KEY_ROLE_ONE_TIME,coins.one_time_public_key)",
			"Phase-1 core one-time encoding",
		),
		(
			"pq_key:tag_mlkem768_key(inputs.pq_public_key)",
			"Phase-1 core ML-KEM encoding",
		),
	] {
		require_once(&core_start, wanted, label)?;
	}
	require_ordered_once(
		&core_start,
		&[
			"identity_key:tag_sign_key(inputs.identity_public_key)",
			"prekey:tag_x25519_key(KEY_ROLE_PREKEY,inputs.prekey_public_key)",
			"one_time_key:tag_x25519_key(KEY_ROLE_ONE_TIME,coins.one_time_public_key)",
			"pq_key:tag_mlkem768_key(inputs.pq_public_key)",
		],
		"Phase-1 core InitKex field order",
	)?;

	let beacon = rust_body(&snapshot.adapter_beacon, "get_registration_bundle")?;
	for (function, expected, label) in [
		(
			"bundle.set_identity_key",
			"started.message.identity_key()",
			"Phase-1 Beacon identity setter mapping",
		),
		(
			"bundle.set_pre_key",
			"&prekey_sig",
			"Phase-1 Beacon prekey setter mapping",
		),
		(
			"bundle.set_one_time_key",
			"&onetime_sig",
			"Phase-1 Beacon one-time setter mapping",
		),
		(
			"bundle.set_pq_key",
			"&pq_sig",
			"Phase-1 Beacon ML-KEM setter mapping",
		),
	] {
		require_one_call(&beacon, function, &[expected], label)?;
	}
	let sign_calls = all_arguments(&beacon, "crypto_sign::sign")?;
	let expected_sign_calls = [
		["started.message.prekey()", "self.identity_sk()"],
		["started.message.one_time_key()", "self.identity_sk()"],
		["started.message.pq_key()", "self.identity_sk()"],
	]
	.map(|arguments| arguments.map(str::to_owned).to_vec());
	if sign_calls != expected_sign_calls {
		return Err(format!(
			"Phase-1 Beacon attached-signature inputs changed: {sign_calls:?}"
		));
	}
	require_ordered_once(
		&beacon,
		&[
			"bundle.set_identity_key(started.message.identity_key())",
			"crypto_sign::sign(started.message.prekey(),self.identity_sk())",
			"bundle.set_pre_key(&prekey_sig)",
			"crypto_sign::sign(started.message.one_time_key(),self.identity_sk())",
			"bundle.set_one_time_key(&onetime_sig)",
			"crypto_sign::sign(started.message.pq_key(),self.identity_sk())",
			"bundle.set_pq_key(&pq_sig)",
		],
		"Phase-1 Beacon serialization order",
	)?;

	let server = rust_body(&snapshot.adapter_server, "get_shared_secret")?;
	for (wanted, label) in [
		(
			"letencoded_identity:[u8;verified_pqxdh::ENCODED_SIGN_PUBLIC_KEY_SIZE]=registration.get_identity_key().ok()?.try_into().ok()?;",
			"Phase-1 Server identity consumer",
		),
		(
			"ifencoded_identity[0]!=verified_pqxdh::SIGN_TYPE_ED25519{returnNone;}",
			"Phase-1 Server Ed25519 identity tag gate",
		),
		(
			"letremote_id=crypto_sign::PublicKey::from_bytes(&encoded_identity[1..]).ok()?;",
			"Phase-1 Server identity decoder",
		),
		(
			"letpq_verified=crypto_sign::verify(registration.get_pq_key().ok()?,&remote_id)?;",
			"Phase-1 Server ML-KEM signature consumer",
		),
		(
			"letprekey_verified=crypto_sign::verify(registration.get_pre_key().ok()?,&remote_id)?;",
			"Phase-1 Server prekey signature consumer",
		),
		(
			"letonetime_verified=crypto_sign::verify(registration.get_one_time_key().ok()?,&remote_id)?;",
			"Phase-1 Server one-time signature consumer",
		),
		(
			"letverified_registration=verified_pqxdh::validate_init_kex(init_kex).ok()?;",
			"Phase-1 Server typed tag validation",
		),
	] {
		require_once(&server, wanted, label)?;
	}
	require_one_call(
		&server,
		"verified_pqxdh::InitKex::from_encoded",
		&[
			"encoded_identity",
			"prekey_verified.as_slice().try_into().ok()?",
			"onetime_verified.as_slice().try_into().ok()?",
			"pq_verified.as_slice().try_into().ok()?",
			"",
		],
		"Phase-1 Server from_encoded mapping",
	)?;
	require_ordered_once(
		&server,
		&[
			"registration.get_identity_key()",
			"encoded_identity[0]!=verified_pqxdh::SIGN_TYPE_ED25519",
			"crypto_sign::PublicKey::from_bytes(&encoded_identity[1..])",
			"registration.get_pq_key()",
			"registration.get_pre_key()",
			"registration.get_one_time_key()",
			"verified_pqxdh::InitKex::from_encoded(",
			"verified_pqxdh::validate_init_kex(init_kex)",
		],
		"Phase-1 Server source evaluation order",
	)?;

	let core_validation = rust_body(&snapshot.core_pqxdh, "validate_init_kex")?;
	for (wanted, label) in [
		(
			"untag_sign_key(message.identity_key)",
			"Phase-1 core Ed25519 tag validation",
		),
		(
			"untag_x25519_key(message.prekey,KEY_ROLE_PREKEY)",
			"Phase-1 core X25519 prekey role validation",
		),
		(
			"untag_x25519_key(message.one_time_key,KEY_ROLE_ONE_TIME)",
			"Phase-1 core X25519 one-time role validation",
		),
		(
			"untag_mlkem768_key(message.pq_key)",
			"Phase-1 core ML-KEM tag validation",
		),
	] {
		require_once(&core_validation, wanted, label)?;
	}
	require_ordered_once(
		&core_validation,
		&[
			"untag_sign_key(message.identity_key)",
			"untag_x25519_key(message.prekey,KEY_ROLE_PREKEY)",
			"untag_x25519_key(message.one_time_key,KEY_ROLE_ONE_TIME)",
			"untag_mlkem768_key(message.pq_key)",
		],
		"Phase-1 core tag-validation order",
	)?;
	Ok(())
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

fn validate_cryptoframe_source(snapshot: &Snapshot) -> Result<(), String> {
	let schema = compact(&uncommented_capnp(&snapshot.cryptoframe_schema));
	let expected_schema =
		"@0xef858976d7f7863b;structCryptoFrame{seq@0:UInt64;keyId@1:UInt64;cipherText@2:Data;}";
	if schema != expected_schema {
		return Err(format!(
			"CryptoFrame schema changed: expected {expected_schema}, found {schema}"
		));
	}

	let ratchet = compact(&uncommented_rust(&snapshot.adapter_ratchet)?);
	for (wanted, label) in [
		(
			"pubconstAEAD_KEY_LEN:usize=32;",
			"CryptoFrame AEAD key length",
		),
		(
			"pubconstAEAD_NONCE_LEN:usize=12;",
			"CryptoFrame AEAD nonce length",
		),
		(
			"pubconstAEAD_TAG_LEN:usize=16;",
			"CryptoFrame AEAD tag length",
		),
		(
			"pubconstCOMMITMENT_SIZE:usize=64;",
			"CryptoFrame commitment length",
		),
		(
			"pubconstMESSAGE_OVERHEAD:usize=COMMITMENT_SIZE+AEAD_TAG_LEN;",
			"CryptoFrame payload overhead",
		),
	] {
		require_once(&ratchet, wanted, label)?;
	}

	let seal = rust_body(&snapshot.adapter_ratchet, "seal_frame")?;
	for (wanted, label) in [
		(
			"letkey:AeadKey=(*material.key().as_bytes()).into();",
			"CryptoFrame seal selected key",
		),
		(
			"letnonce:AeadNonce=(*material.nonce().as_bytes()).into();",
			"CryptoFrame seal selected nonce",
		),
	] {
		require_once(&seal, wanted, label)?;
	}
	require_one_call(
		&seal,
		"crypto_aead::chacha20poly1305_ietf::encrypt_detached",
		&[
			"context.bytes",
			"Some(context.associated_data.as_slice())",
			"&nonce",
			"&key",
			"",
		],
		"CryptoFrame detached AEAD seal",
	)?;
	require_one_call(
		&seal,
		"build_commitment",
		&[
			"material",
			"context.associated_data.as_slice()",
			"tag.as_slice()",
			"key_seq",
			"context.sender_kid",
			"",
		],
		"CryptoFrame seal commitment mapping",
	)?;
	require_ordered_once(
		&seal,
		&[
			"plaintext.append(&muttag)",
			"plaintext.append(&mutcommitment)",
		],
		"CryptoFrame seal payload order",
	)?;
	for (function, expected, label) in [
		(
			"builder.set_cipher_text",
			"&plaintext",
			"CryptoFrame payload setter mapping",
		),
		(
			"builder.set_seq",
			"key_seq",
			"CryptoFrame sequence setter mapping",
		),
		(
			"builder.set_key_id",
			"context.sender_kid",
			"CryptoFrame sender-ID setter mapping",
		),
	] {
		require_one_call(&seal, function, &[expected], label)?;
	}
	require_ordered_once(
		&seal,
		&[
			"letmutt_builder=TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default()",
			"letmutbuilder:cryptoframe_capnp::crypto_frame::Builder<'_>=t_builder.init_root()",
			"builder.set_cipher_text(&plaintext)",
			"builder.set_seq(key_seq)",
			"builder.set_key_id(context.sender_kid)",
			"letmutbuffer=vec![]",
			"capnp::serialize::write_message(&mutbuffer,t_builder.borrow_inner()).ok()?",
		],
		"CryptoFrame builder serialization order",
	)?;
	require_once(
		&seal,
		"Some(Encrypted{ciphertext:buffer,key_id:context.target_kid,seq:key_seq,})",
		"CryptoFrame local target metadata",
	)?;
	forbid(
		&seal,
		"builder.set_key_id(context.target_kid)",
		"serialized local target ID",
	)?;

	let encrypt = rust_body(&snapshot.adapter_ratchet, "encrypt_message_with_ratchet")?;
	require_once(
		&encrypt,
		"ifbytes.is_empty(){returnNone;}",
		"CryptoFrame empty-plaintext rejection",
	)?;
	require_once(
		&encrypt,
		"letcontext=SealFrameContext{bytes,target_kid,sender_kid,associated_data,};",
		"CryptoFrame seal context mapping",
	)?;
	require_once(
		&encrypt,
		"letsealed=seal_frame(seal.material(),seal.sequence(),seal.context());",
		"CryptoFrame selected send material and sequence",
	)?;
	require_once(
		&encrypt,
		"let(kernel,sealed)=seal.finish(sealed);",
		"CryptoFrame one-use send completion",
	)?;
	require_ordered_once(
		&encrypt,
		&[
			"ifbytes.is_empty()",
			"verified_ratchet::begin_send(kernel,context)",
			"seal_frame(seal.material(),seal.sequence(),seal.context())",
			"seal.finish(sealed)",
		],
		"CryptoFrame empty-input and send ordering",
	)?;

	let open = rust_body(&snapshot.adapter_ratchet, "open_frame")?;
	require_once(
		&open,
		"ifct_len<=MESSAGE_OVERHEAD{returnNone;}",
		"CryptoFrame open length gate",
	)?;
	for (wanted, label) in [
		(
			"letkey:AeadKey=(*material.key().as_bytes()).into();",
			"CryptoFrame open selected key",
		),
		(
			"letnonce:AeadNonce=(*material.nonce().as_bytes()).into();",
			"CryptoFrame open selected nonce",
		),
	] {
		require_once(&open, wanted, label)?;
	}
	require_one_call(
		&open,
		"build_commitment",
		&[
			"material",
			"context.associated_data.as_slice()",
			"&context.ciphertext[ct_len-COMMITMENT_SIZE-AEAD_TAG_LEN..ct_len-COMMITMENT_SIZE]",
			"key_seq",
			"context.sender_kid",
			"",
		],
		"CryptoFrame open commitment mapping",
	)?;
	require_once(
		&open,
		"if!memcmp(&commitment,&context.ciphertext[ct_len-COMMITMENT_SIZE..]){returnNone;}",
		"CryptoFrame libsodium memcmp commitment comparison",
	)?;
	require_one_call(
		&open,
		"crypto_aead::chacha20poly1305_ietf::decrypt",
		&[
			"&context.ciphertext[..ct_len-COMMITMENT_SIZE]",
			"Some(context.associated_data.as_slice())",
			"&nonce",
			"&key",
			"",
		],
		"CryptoFrame C-and-tag AEAD open",
	)?;
	require_ordered_once(
		&open,
		&[
			"letcommitment=build_commitment(",
			"memcmp(&commitment,&context.ciphertext[ct_len-COMMITMENT_SIZE..])",
			"letkey:AeadKey=(*material.key().as_bytes()).into()",
			"letnonce:AeadNonce=(*material.nonce().as_bytes()).into()",
			"crypto_aead::chacha20poly1305_ietf::decrypt(",
		],
		"CryptoFrame commitment-before-AEAD order",
	)?;

	let decrypt = rust_body(&snapshot.adapter_ratchet, "decrypt_message_with_ratchet")?;
	for (wanted, label) in [
		(
			"ifdata.is_empty(){returnNone;}",
			"CryptoFrame empty-wire rejection",
		),
		(
			"letreader=capnp::serialize::read_message(data,ReaderOptions::new()).ok()?;",
			"CryptoFrame Cap'n Proto parse",
		),
		(
			"lettyped_reader=TypedReader::<_,cryptoframe_capnp::crypto_frame::Owned>::new(reader);",
			"CryptoFrame typed reader",
		),
		(
			"letframe=typed_reader.get().ok()?;",
			"CryptoFrame typed root",
		),
		("letkid=frame.get_key_id();", "CryptoFrame parsed sender ID"),
		(
			"ifkid!=expected_sender_kid{returnNone;}",
			"CryptoFrame expected-sender gate",
		),
		(
			"letciphertext=frame.get_cipher_text().ok()?;",
			"CryptoFrame payload getter",
		),
		(
			"ifct_len<=MESSAGE_OVERHEAD{returnNone;}",
			"CryptoFrame pre-ratchet length gate",
		),
		(
			"letcontext=OpenFrameContext{ciphertext,associated_data,sender_kid:kid,};",
			"CryptoFrame open context mapping",
		),
		("letkey_seq=frame.get_seq();", "CryptoFrame parsed sequence"),
		(
			"letmuteffect=verified_ratchet::begin_receive(kernel,key_seq,context);",
			"CryptoFrame parsed-sequence ratchet selection",
		),
		(
			"letopened=open_frame(material,open.sequence(),open.context());",
			"CryptoFrame selected receive material and sequence",
		),
		(
			"let(kernel,opened)=open.finish(opened);",
			"CryptoFrame one-use receive completion",
		),
	] {
		require_once(&decrypt, wanted, label)?;
	}
	require_ordered_once(
		&decrypt,
		&[
			"ifdata.is_empty()",
			"capnp::serialize::read_message(data,ReaderOptions::new())",
			"letkid=frame.get_key_id()",
			"ifkid!=expected_sender_kid",
			"letciphertext=frame.get_cipher_text().ok()?",
			"ifct_len<=MESSAGE_OVERHEAD",
			"letcontext=OpenFrameContext{ciphertext,associated_data,sender_kid:kid,}",
			"letkey_seq=frame.get_seq()",
			"letkernel=ratchet.refined.take()",
			"verified_ratchet::begin_receive(kernel,key_seq,context)",
			"verified_ratchet::ReceiveEffect::ReceiveOpenRequested",
			"open.material()",
			"open_frame(material,open.sequence(),open.context())",
			"open.finish(opened)",
		],
		"CryptoFrame parser and gate evaluation order",
	)?;
	require_once(
		&decrypt,
		"Some(Decrypted{plaintext,key_id:kid,seq:key_seq,})",
		"CryptoFrame returned parsed metadata",
	)?;

	let adapter_commitment = rust_body(&snapshot.adapter_ratchet, "build_commitment")?;
	for (wanted, label) in [
		(
			"letkey=material.key().as_bytes();",
			"CryptoFrame commitment selected key",
		),
		(
			"letnonce=material.nonce().as_bytes();",
			"CryptoFrame commitment selected nonce",
		),
		(
			"letad=ad.try_into().ok()?;",
			"CryptoFrame commitment fixed-width AD",
		),
		(
			"lettag=tag.try_into().ok()?;",
			"CryptoFrame commitment fixed-width retained tag",
		),
	] {
		require_once(&adapter_commitment, wanted, label)?;
	}
	require_one_call(
		&adapter_commitment,
		"build_commitment_transcript",
		&["key", "nonce", "ad", "tag", "seq", "kid"],
		"CryptoFrame adapter-to-core commitment mapping",
	)?;
	require_one_call(
		&adapter_commitment,
		"crypto_generichash::generichash",
		&["input.as_bytes()", "None", "COMMITMENT_SIZE"],
		"CryptoFrame unkeyed commitment hash",
	)?;

	let core_source = compact(&uncommented_rust(&snapshot.core_commitment)?);
	for (wanted, label) in [
		(
			"pubconstAEAD_KEY_SIZE:usize=32;",
			"CryptoFrame core key size",
		),
		(
			"pubconstAEAD_NONCE_SIZE:usize=12;",
			"CryptoFrame core nonce size",
		),
		(
			"pubconstASSOCIATED_DATA_SIZE:usize=crate::constants::ASSOCIATED_DATA_SIZE;",
			"CryptoFrame core associated-data size source",
		),
		(
			"pubconstAEAD_TAG_SIZE:usize=16;",
			"CryptoFrame core tag size",
		),
		(
			"pubconstENCODED_U64_SIZE:usize=8;",
			"CryptoFrame core integer size",
		),
		(
			"pubconstCOMMITMENT_TRANSCRIPT_SIZE:usize=AEAD_KEY_SIZE+AEAD_NONCE_SIZE+ASSOCIATED_DATA_SIZE+AEAD_TAG_SIZE+(2*ENCODED_U64_SIZE);",
			"CryptoFrame core transcript-size formula",
		),
		(
			"const_:()=assert!(ASSOCIATED_DATA_SIZE==153);",
			"CryptoFrame core associated-data length",
		),
		(
			"const_:()=assert!(COMMITMENT_TRANSCRIPT_SIZE==229);",
			"CryptoFrame core transcript length",
		),
		(
			"pubstructCommitmentTranscript{bytes:[u8;COMMITMENT_TRANSCRIPT_SIZE],}",
			"CryptoFrame core fixed-width result",
		),
		(
			"pubfnbuild_commitment_transcript(key:&[u8;AEAD_KEY_SIZE],nonce:&[u8;AEAD_NONCE_SIZE],associated_data:&[u8;ASSOCIATED_DATA_SIZE],tag:&[u8;AEAD_TAG_SIZE],sequence:u64,sender_id:u64,)->CommitmentTranscript",
			"CryptoFrame core transcript signature",
		),
	] {
		require_once(&core_source, wanted, label)?;
	}
	let core_commitment = rust_body(&snapshot.core_commitment, "build_commitment_transcript")?;
	let encode_u64 = rust_body(&snapshot.core_commitment, "encode_u64_le")?;
	require_once(
		&encode_u64,
		"[valueasu8,(value>>8)asu8,(value>>16)asu8,(value>>24)asu8,(value>>32)asu8,(value>>40)asu8,(value>>48)asu8,(value>>56)asu8,]",
		"CryptoFrame core LE64 encoding",
	)?;
	let encoded = all_arguments(&core_commitment, "encode_u64_le")?;
	if encoded != [vec!["sequence".to_owned()], vec!["sender_id".to_owned()]] {
		return Err(format!(
			"CryptoFrame core integer mapping changed: {encoded:?}"
		));
	}
	for (wanted, label) in [
		("ifi<32{key[i]}", "CryptoFrame core key field"),
		("elseifi<44{nonce[i-32]}", "CryptoFrame core nonce field"),
		(
			"elseifi<197{associated_data[i-44]}",
			"CryptoFrame core associated-data field",
		),
		(
			"elseifi<213{tag[i-197]}",
			"CryptoFrame core retained-tag field",
		),
		(
			"elseifi<221{sequence[i-213]}",
			"CryptoFrame core sequence field",
		),
		("else{sender_id[i-221]}", "CryptoFrame core sender-ID field"),
	] {
		require_once(&core_commitment, wanted, label)?;
	}
	require_ordered_once(
		&core_commitment,
		&[
			"ifi<32{key[i]}",
			"elseifi<44{nonce[i-32]}",
			"elseifi<197{associated_data[i-44]}",
			"elseifi<213{tag[i-197]}",
			"elseifi<221{sequence[i-213]}",
			"else{sender_id[i-221]}",
		],
		"CryptoFrame core transcript field order",
	)?;
	require_once(
		&core_commitment,
		"letbytes=core::array::from_fn(|i|",
		"CryptoFrame core fixed-width construction",
	)?;
	require_once(
		&core_commitment,
		"CommitmentTranscript{bytes}",
		"CryptoFrame core transcript result",
	)?;

	let crypto = compact(&uncommented_pv(&snapshot.crypto)?);
	require_once(
		&snapshot.crypto,
		"(* @beaconcrypt-cryptoframe-v1 crypto_frame.fields=ciphertext,retained_aead_tag,commitment,sequence,sender_id *)\nfun crypto_frame(",
		"CryptoFrame symbolic semantic field order",
	)?;
	require_once(
		&crypto,
		"funcrypto_frame(bitstring,bitstring,bitstring,sequence,key_id):bitstring[data].",
		"CryptoFrame symbolic constructor declaration",
	)?;
	let seal_start = crypto
		.find("letfunseal_frame(")
		.ok_or_else(|| "missing symbolic seal_frame".to_owned())?;
	let symbolic_seal = &crypto[seal_start..];
	let seal_arguments = arguments_after(symbolic_seal, "letfunseal_frame(")?;
	let expected_seal_arguments = [
		"material:bitstring",
		"associated_data:bitstring",
		"message_sequence:sequence",
		"sender_id:key_id",
		"plaintext:bitstring",
	];
	if seal_arguments != expected_seal_arguments {
		return Err(format!(
			"CryptoFrame symbolic seal arguments changed: {seal_arguments:?}"
		));
	}
	let seal_fields = arguments_after(symbolic_seal, ")=crypto_frame(")?;
	let expected_seal_fields = [
		"aead_cipher(material_key(material),material_nonce(material),associated_data,plaintext)",
		"aead_tag(material_key(material),material_nonce(material),associated_data,plaintext)",
		"ctx_commitment(material_key(material),material_nonce(material),associated_data,aead_tag(material_key(material),material_nonce(material),associated_data,plaintext),message_sequence,sender_id)",
		"message_sequence",
		"sender_id",
	];
	if seal_fields != expected_seal_fields {
		return Err(format!(
			"CryptoFrame symbolic seal fields changed: {seal_fields:?}"
		));
	}
	let open_start = crypto
		.find("reducforallkey:bitstring,nonce:bitstring,associated_data:bitstring,message_sequence:sequence,sender_id:key_id,plaintext:bitstring;open_frame(")
		.ok_or_else(|| "missing symbolic open_frame reduction".to_owned())?;
	let symbolic_open = &crypto[open_start..];
	let open_fields = arguments_after(symbolic_open, "crypto_frame(")?;
	let expected_open_fields = [
		"aead_cipher(key,nonce,associated_data,plaintext)",
		"aead_tag(key,nonce,associated_data,plaintext)",
		"blake2b512(ctx_preimage(key,nonce,associated_data,aead_tag(key,nonce,associated_data,plaintext),sequence_le64(message_sequence),sender_id_le64(sender_id)))",
		"message_sequence",
		"sender_id",
	];
	if open_fields != expected_open_fields {
		return Err(format!(
			"CryptoFrame symbolic open fields changed: {open_fields:?}"
		));
	}
	let open_arguments = arguments_after(symbolic_open, "open_frame(")?;
	let expected_open_arguments = vec![
		"ratchet_key_nonce(key,nonce)".to_owned(),
		"associated_data".to_owned(),
		"message_sequence".to_owned(),
		"sender_id".to_owned(),
		format!("crypto_frame({})", expected_open_fields.join(",")),
	];
	if open_arguments != expected_open_arguments {
		return Err(format!(
			"CryptoFrame symbolic open acceptance changed: {open_arguments:?}"
		));
	}
	if !symbolic_open.ends_with(")=plaintext.") {
		return Err("CryptoFrame symbolic open result changed".to_owned());
	}
	let symbolic_boundary = &crypto[seal_start..];
	for absent in [
		"target_id",
		"direction",
		"session",
		"phase",
		"aead_label",
		"ctx_label",
	] {
		forbid(
			symbolic_boundary,
			absent,
			"invented CryptoFrame symbolic field",
		)?;
	}
	Ok(())
}

fn validate_pv(snapshot: &Snapshot) -> Result<(), String> {
	let interface = compact(&uncommented_pv(&snapshot.interface)?);
	let crypto = compact(&uncommented_pv(&snapshot.crypto)?);
	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	let active_quantum_witness = compact(&uncommented_pv(&snapshot.active_quantum_witness)?);
	require_once(
		&snapshot.environment,
		"(* @beaconcrypt-phase1-v1 signed_init_kex.fields=encoded_identity,signed_prekey,signed_one_time,signed_pq *)\nfun signed_init_kex(",
		"Phase-1 symbolic constructor semantic order",
	)?;
	require_once(
		&environment,
		"funsigned_init_kex(bitstring,bitstring,bitstring,bitstring):bitstring[data].",
		"Phase-1 symbolic constructor declaration",
	)?;
	require_once(
		&crypto,
		"funsign(bitstring,bitstring):bitstring.",
		"Phase-1 symbolic Ed25519 signature declaration",
	)?;
	require_once(
		&crypto,
		"reducforallmessage:bitstring,signing_key:bitstring;verify_signature(sign(message,signing_key),ed_public(signing_key))=message.",
		"Phase-1 symbolic attached-signature verification",
	)?;

	let honest_producer = "signed_init_kex(tag_ed25519(beacon_identity),sign(tag_x25519_prekey(beacon_prekey),beacon_identity_secret),sign(tag_x25519_one_time(beacon_one_time),beacon_identity_secret),sign(tag_mlkem768(beacon_pq),beacon_identity_secret))";
	if count(&environment, honest_producer) != 2 {
		return Err(format!(
			"Phase-1 symbolic honest/malicious producer order changed: expected two exact producers, found {}",
			count(&environment, honest_producer)
		));
	}
	let server_consumer = "letsigned_init_kex(encoded_identity,signed_prekey,signed_one_time,signed_pq)=incoming_initin";
	if count(&environment, server_consumer) != 2 {
		return Err(format!(
			"Phase-1 symbolic Server consumer order changed: expected two exact consumers, found {}",
			count(&environment, server_consumer)
		));
	}
	require_once(
		&active_quantum_witness,
		server_consumer,
		"Phase-1 active-quantum consumer order",
	)?;
	require_once(
		&active_quantum_witness,
		"signed_init_kex(tag_ed25519(beacon_identity),sign(tag_x25519_prekey(forged_prekey),beacon_identity_secret),sign(tag_x25519_one_time(forged_one_time),beacon_identity_secret),sign(tag_mlkem768(forged_pq),beacon_identity_secret))",
		"Phase-1 active-quantum producer order",
	)?;

	for (wanted, expected_count, label) in [
		(
			"lettag_ed25519(beacon_identity:bitstring)=encoded_identityin",
			2,
			"Phase-1 symbolic identity validation",
		),
		(
			"lettag_x25519_prekey(beacon_prekey:bitstring)=verify_signature(signed_prekey,beacon_identity)in",
			2,
			"Phase-1 symbolic prekey validation",
		),
		(
			"lettag_x25519_one_time(beacon_one_time:bitstring)=verify_signature(signed_one_time,beacon_identity)in",
			2,
			"Phase-1 symbolic one-time validation",
		),
		(
			"lettag_mlkem768(beacon_pq:bitstring)=verify_signature(signed_pq,beacon_identity)in",
			2,
			"Phase-1 symbolic ML-KEM validation",
		),
		(
			"letcore_init=beaconcrypt_core__pqxdh__InitKex(encoded_identity,tag_x25519_prekey(beacon_prekey),tag_x25519_one_time(beacon_one_time),tag_mlkem768(beacon_pq))in",
			2,
			"Phase-1 symbolic Server core mapping",
		),
		(
			"letcore_init=beaconcrypt_core__pqxdh__InitKex(tag_ed25519(beacon_identity),tag_x25519_prekey(beacon_prekey),tag_x25519_one_time(beacon_one_time),tag_mlkem768(beacon_pq))in",
			1,
			"Phase-1 symbolic honest core mapping",
		),
	] {
		let actual = count(&environment, wanted);
		if actual != expected_count {
			return Err(format!(
				"{label} changed: expected {expected_count} exact occurrence(s), found {actual}"
			));
		}
	}
	let symbolic_gate_order = "lettag_ed25519(beacon_identity:bitstring)=encoded_identityinlettag_x25519_prekey(beacon_prekey:bitstring)=verify_signature(signed_prekey,beacon_identity)inlettag_x25519_one_time(beacon_one_time:bitstring)=verify_signature(signed_one_time,beacon_identity)inlettag_mlkem768(beacon_pq:bitstring)=verify_signature(signed_pq,beacon_identity)inletcore_init=beaconcrypt_core__pqxdh__InitKex(encoded_identity,tag_x25519_prekey(beacon_prekey),tag_x25519_one_time(beacon_one_time),tag_mlkem768(beacon_pq))in";
	if count(&environment, symbolic_gate_order) != 2 {
		return Err(format!(
			"Phase-1 symbolic pure-gate evaluation order changed: expected two exact blocks, found {}",
			count(&environment, symbolic_gate_order)
		));
	}
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
	if scenarios.len() != 27 {
		return Err(format!(
			"expected 27 ProVerif scenarios, found {}",
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
	validate_phase1_source(snapshot)?;
	validate_phase2_source(snapshot)?;
	validate_cryptoframe_source(snapshot)?;
	validate_makefile(&snapshot.makefile)
}

fn replace_once(source: &mut String, from: &str, to: &str) {
	let start = source
		.find(from)
		.unwrap_or_else(|| panic!("mutation anchor missing: {from}"));
	source.replace_range(start..start + from.len(), to);
}

fn replace_once_after(source: &mut String, marker: &str, from: &str, to: &str) {
	let marker_start = source
		.find(marker)
		.unwrap_or_else(|| panic!("mutation scope missing: {marker}"));
	let relative = source[marker_start..]
		.find(from)
		.unwrap_or_else(|| panic!("mutation anchor missing after {marker}: {from}"));
	let start = marker_start + relative;
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

fn replace_call(source: &mut String, function: &str, occurrence: usize, arguments: &[String]) {
	let marker = format!("{function}(");
	let mut offset = 0usize;
	let mut found = None;
	for index in 0..=occurrence {
		let relative = source[offset..]
			.find(&marker)
			.unwrap_or_else(|| panic!("mutation call missing: {function} occurrence {occurrence}"));
		let start = offset + relative;
		if index == occurrence {
			found = Some(start);
			break;
		}
		let (_, end) = parse_call(source, start + marker.len() - 1).unwrap();
		offset = end;
	}
	let start = found.unwrap();
	let (_, end) = parse_call(source, start + marker.len() - 1).unwrap();
	source.replace_range(start..end, &format!("{function}({})", arguments.join(",")));
}

fn phase1_permutations() -> Vec<[usize; 4]> {
	let mut permutations = Vec::new();
	for first in 0..4 {
		for second in 0..4 {
			for third in 0..4 {
				for fourth in 0..4 {
					let candidate = [first, second, third, fourth];
					if candidate
						.iter()
						.enumerate()
						.all(|(index, value)| !candidate[..index].contains(value))
					{
						permutations.push(candidate);
					}
				}
			}
		}
	}
	permutations
}

fn phase1_transpositions() -> Vec<[usize; 4]> {
	let mut transpositions = Vec::new();
	for left in 0..4 {
		for right in left + 1..4 {
			let mut permutation = [0, 1, 2, 3];
			permutation.swap(left, right);
			transpositions.push(permutation);
		}
	}
	transpositions
}

fn cryptoframe_permutations() -> [[usize; 3]; 6] {
	[
		[0, 1, 2],
		[0, 2, 1],
		[1, 0, 2],
		[1, 2, 0],
		[2, 0, 1],
		[2, 1, 0],
	]
}

fn permute_cryptoframe(arguments: &[&str; 3], permutation: [usize; 3]) -> Vec<String> {
	permutation
		.into_iter()
		.map(|index| arguments[index].to_owned())
		.collect()
}

fn replace_cryptoframe_schema(snapshot: &mut Snapshot, fields: &[(&str, usize, &str)]) {
	let start = snapshot
		.cryptoframe_schema
		.find("struct CryptoFrame {")
		.unwrap();
	let relative_end = snapshot.cryptoframe_schema[start..].find("\n}").unwrap();
	let end = start + relative_end + 2;
	let declarations = fields
		.iter()
		.map(|(name, ordinal, field_type)| format!("    {name} @{ordinal} :{field_type};"))
		.collect::<Vec<_>>()
		.join("\n");
	snapshot.cryptoframe_schema.replace_range(
		start..end,
		&format!("struct CryptoFrame {{\n{declarations}\n}}"),
	);
}

fn permute_phase1(arguments: &[&str; 4], permutation: [usize; 4]) -> Vec<String> {
	permutation
		.into_iter()
		.map(|index| arguments[index].to_owned())
		.collect()
}

fn replace_phase1_schema(snapshot: &mut Snapshot, fields: &[(&str, usize)]) {
	let start = snapshot.phase1_schema.find("struct InitKex {").unwrap();
	let relative_end = snapshot.phase1_schema[start..].find("\n}").unwrap();
	let end = start + relative_end + 2;
	let declarations = fields
		.iter()
		.map(|(name, ordinal)| format!("    {name} @{ordinal} :Data;"))
		.collect::<Vec<_>>()
		.join("\n");
	snapshot.phase1_schema.replace_range(
		start..end,
		&format!("struct InitKex {{\n{declarations}\n}}"),
	);
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

const CRYPTOFRAME_WIRE_MUTATION_COUNT: usize = 223;

#[test]
fn cryptoframe_wire_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;

	for fact in EXPECTED_FACTS
		.iter()
		.filter(|fact| fact.starts_with("cryptoframe."))
	{
		let key = fact.split_once('=').unwrap().0;
		assert_rejected(&format!("cryptoframe_fact_{key}"), key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, "mutated");
		});
		mutation_count += 1;
	}

	let schema_fields = [
		("seq", 0, "UInt64"),
		("keyId", 1, "UInt64"),
		("cipherText", 2, "Data"),
	];
	assert_rejected(
		"cryptoframe_schema_id_drift",
		"CryptoFrame schema changed",
		|snapshot| {
			replace_once(
				&mut snapshot.cryptoframe_schema,
				"@0xef858976d7f7863b;",
				"@0xef858976d7f7863c;",
			);
		},
	);
	mutation_count += 1;
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let fields = permutation.map(|field| schema_fields[field]);
		assert_rejected(
			&format!("cryptoframe_schema_declaration_permutation_{index}"),
			"CryptoFrame schema changed",
			move |snapshot| replace_cryptoframe_schema(snapshot, &fields),
		);
		mutation_count += 1;
	}
	for omitted in 0..3 {
		let fields = schema_fields
			.iter()
			.copied()
			.filter(|(name, _, _)| *name != schema_fields[omitted].0)
			.collect::<Vec<_>>();
		assert_rejected(
			&format!("cryptoframe_schema_omits_field_{omitted}"),
			"CryptoFrame schema changed",
			move |snapshot| replace_cryptoframe_schema(snapshot, &fields),
		);
		mutation_count += 1;
	}
	for (index, renamed) in ["messageSeq", "senderKeyId", "payload"]
		.into_iter()
		.enumerate()
	{
		let mut fields = schema_fields;
		fields[index].0 = renamed;
		assert_rejected(
			&format!("cryptoframe_schema_renames_field_{index}"),
			"CryptoFrame schema changed",
			move |snapshot| replace_cryptoframe_schema(snapshot, &fields),
		);
		mutation_count += 1;
	}
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let fields: [(&str, usize, &str); 3] = core::array::from_fn(|field| {
			let (name, _, field_type) = schema_fields[field];
			(name, permutation[field], field_type)
		});
		assert_rejected(
			&format!("cryptoframe_schema_ordinal_permutation_{index}"),
			"CryptoFrame schema changed",
			move |snapshot| replace_cryptoframe_schema(snapshot, &fields),
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_adapter_key_length_drift",
			"pub const AEAD_KEY_LEN: usize = 32;",
			"pub const AEAD_KEY_LEN: usize = 31;",
			"CryptoFrame AEAD key length",
		),
		(
			"cryptoframe_adapter_nonce_length_drift",
			"pub const AEAD_NONCE_LEN: usize = 12;",
			"pub const AEAD_NONCE_LEN: usize = 11;",
			"CryptoFrame AEAD nonce length",
		),
		(
			"cryptoframe_adapter_tag_length_drift",
			"pub const AEAD_TAG_LEN: usize = 16;",
			"pub const AEAD_TAG_LEN: usize = 15;",
			"CryptoFrame AEAD tag length",
		),
		(
			"cryptoframe_adapter_commitment_length_drift",
			"pub const COMMITMENT_SIZE: usize = 64;",
			"pub const COMMITMENT_SIZE: usize = 63;",
			"CryptoFrame commitment length",
		),
		(
			"cryptoframe_adapter_overhead_formula_drift",
			"pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE + AEAD_TAG_LEN;",
			"pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE;",
			"CryptoFrame payload overhead",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_ratchet, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_seal_uses_zero_key",
			"let key: AeadKey = (*material.key().as_bytes()).into();",
			"let key: AeadKey = [0u8; AEAD_KEY_LEN].into();",
			"CryptoFrame seal selected key",
		),
		(
			"cryptoframe_seal_uses_zero_nonce",
			"let nonce: AeadNonce = (*material.nonce().as_bytes()).into();",
			"let nonce: AeadNonce = [0u8; AEAD_NONCE_LEN].into();",
			"CryptoFrame seal selected nonce",
		),
		(
			"cryptoframe_seal_encrypts_associated_data",
			"\t\tcontext.bytes,\n\t\tSome(context.associated_data.as_slice()),",
			"\t\tcontext.associated_data.as_slice(),\n\t\tSome(context.associated_data.as_slice()),",
			"CryptoFrame detached AEAD seal",
		),
		(
			"cryptoframe_seal_omits_associated_data",
			"Some(context.associated_data.as_slice()),",
			"None,",
			"CryptoFrame detached AEAD seal",
		),
		(
			"cryptoframe_seal_commitment_swaps_ad_and_tag",
			"\t\tcontext.associated_data.as_slice(),\n\t\ttag.as_slice(),",
			"\t\ttag.as_slice(),\n\t\tcontext.associated_data.as_slice(),",
			"CryptoFrame seal commitment mapping",
		),
		(
			"cryptoframe_seal_commitment_swaps_sequence_sender",
			"\t\tkey_seq,\n\t\tcontext.sender_kid,",
			"\t\tcontext.sender_kid,\n\t\tkey_seq,",
			"CryptoFrame seal commitment mapping",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_ratchet, from, to);
		});
		mutation_count += 1;
	}

	let payload_fields = ["plaintext", "tag", "commitment"];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let ordered = permutation.map(|field| payload_fields[field]);
		let replacement = format!(
			"\tlet mut payload = vec![];\n\tpayload.append(&mut {});\n\tpayload.append(&mut {});\n\tpayload.append(&mut {});",
			ordered[0], ordered[1], ordered[2]
		);
		assert_rejected(
			&format!("cryptoframe_payload_permutation_{index}"),
			"CryptoFrame seal payload order",
			move |snapshot| {
				replace_once(
					&mut snapshot.adapter_ratchet,
					"\tplaintext.append(&mut tag);\n\tplaintext.append(&mut commitment);",
					&replacement,
				);
				replace_once(
					&mut snapshot.adapter_ratchet,
					"builder.set_cipher_text(&plaintext)",
					"builder.set_cipher_text(&payload)",
				);
			},
		);
		mutation_count += 1;
	}
	for omitted in 0..3 {
		let retained = (0..3)
			.filter(|field| *field != omitted)
			.map(|field| payload_fields[field])
			.collect::<Vec<_>>();
		let replacement = format!(
			"\tlet mut payload = vec![];\n\tpayload.append(&mut {});\n\tpayload.append(&mut {});",
			retained[0], retained[1]
		);
		assert_rejected(
			&format!("cryptoframe_payload_omits_field_{omitted}"),
			"CryptoFrame seal payload order",
			move |snapshot| {
				replace_once(
					&mut snapshot.adapter_ratchet,
					"\tplaintext.append(&mut tag);\n\tplaintext.append(&mut commitment);",
					&replacement,
				);
				replace_once(
					&mut snapshot.adapter_ratchet,
					"builder.set_cipher_text(&plaintext)",
					"builder.set_cipher_text(&payload)",
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_payload_setter_uses_tag",
			"builder.set_cipher_text(&plaintext)",
			"builder.set_cipher_text(&tag)",
			"CryptoFrame payload setter mapping",
		),
		(
			"cryptoframe_sequence_setter_uses_sender",
			"builder.set_seq(key_seq)",
			"builder.set_seq(context.sender_kid)",
			"CryptoFrame sequence setter mapping",
		),
		(
			"cryptoframe_sender_setter_uses_sequence",
			"builder.set_key_id(context.sender_kid)",
			"builder.set_key_id(key_seq)",
			"CryptoFrame sender-ID setter mapping",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_ratchet, from, to);
		});
		mutation_count += 1;
	}

	let setters = [
		"builder.set_cipher_text(&plaintext);",
		"builder.set_seq(key_seq);",
		"builder.set_key_id(context.sender_kid);",
	];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let replacement = permutation.map(|setter| setters[setter]).join("\n\t");
		assert_rejected(
			&format!("cryptoframe_builder_order_permutation_{index}"),
			"CryptoFrame builder serialization order",
			move |snapshot| {
				replace_once(
					&mut snapshot.adapter_ratchet,
					"builder.set_cipher_text(&plaintext);\n\tbuilder.set_seq(key_seq);\n\tbuilder.set_key_id(context.sender_kid);",
					&replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to) in [
		(
			"cryptoframe_builder_type_drift",
			"TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default()",
			"TypedBuilder::<crate::cryptoframe_capnp::crypto_frame::Owned>::new_default()",
		),
		(
			"cryptoframe_builder_root_drift",
			"t_builder.init_root()",
			"t_builder.get_root().ok()?",
		),
		(
			"cryptoframe_output_buffer_prefixed",
			"let mut buffer = vec![];",
			"let mut buffer = vec![0u8];",
		),
		(
			"cryptoframe_serializes_into_payload",
			"write_message(&mut buffer, t_builder.borrow_inner())",
			"write_message(&mut plaintext, t_builder.borrow_inner())",
		),
	] {
		assert_rejected(
			name,
			"CryptoFrame builder serialization order",
			|snapshot| {
				replace_once(&mut snapshot.adapter_ratchet, from, to);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_local_metadata_uses_sender",
			"key_id: context.target_kid,",
			"key_id: context.sender_kid,",
			"CryptoFrame local target metadata",
		),
		(
			"cryptoframe_seal_context_target_uses_sender",
			"\t\ttarget_kid,\n\t\tsender_kid,",
			"\t\ttarget_kid: sender_kid,\n\t\tsender_kid,",
			"CryptoFrame seal context mapping",
		),
		(
			"cryptoframe_seal_context_sender_uses_target",
			"\t\ttarget_kid,\n\t\tsender_kid,",
			"\t\ttarget_kid,\n\t\tsender_kid: target_kid,",
			"CryptoFrame seal context mapping",
		),
		(
			"cryptoframe_empty_plaintext_gate_removed",
			"\tif bytes.is_empty() {\n\t\treturn None;\n\t}\n",
			"",
			"CryptoFrame empty-plaintext rejection",
		),
		(
			"cryptoframe_seal_uses_unallocated_sequence",
			"seal_frame(seal.material(), seal.sequence(), seal.context())",
			"seal_frame(seal.material(), sender_kid, seal.context())",
			"CryptoFrame selected send material and sequence",
		),
		(
			"cryptoframe_seal_skips_one_use_finish",
			"let (kernel, sealed) = seal.finish(sealed);",
			"let (kernel, sealed) = (kernel, sealed);",
			"CryptoFrame one-use send completion",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_ratchet, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_empty_wire_gate_removed",
			"\tif data.is_empty() {\n\t\treturn None;\n\t}\n",
			"",
			"CryptoFrame empty-wire rejection",
		),
		(
			"cryptoframe_parse_uses_unbounded_options",
			"read_message(data, ReaderOptions::new())",
			"read_message(data, Default::default())",
			"CryptoFrame Cap'n Proto parse",
		),
		(
			"cryptoframe_parse_typed_reader_path_drift",
			"TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader)",
			"TypedReader::<_, crate::cryptoframe_capnp::crypto_frame::Owned>::new(reader)",
			"CryptoFrame typed reader",
		),
		(
			"cryptoframe_parse_typed_root_unwraps",
			"let frame = typed_reader.get().ok()?;",
			"let frame = typed_reader.get().unwrap();",
			"CryptoFrame typed root",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn decrypt_message_with_ratchet(",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	let getter_declarations = [
		"let kid = frame.get_key_id();",
		"let ciphertext = frame.get_cipher_text().ok()?;",
		"let key_seq = frame.get_seq();",
	];
	let getter_block = "\tlet kid = frame.get_key_id();\n\tif kid != expected_sender_kid {\n\t\treturn None;\n\t}\n\tlet ciphertext = frame.get_cipher_text().ok()?;\n\tlet ct_len = ciphertext.len();\n\tif ct_len <= MESSAGE_OVERHEAD {\n\t\treturn None;\n\t}\n\tlet context = OpenFrameContext {\n\t\tciphertext,\n\t\tassociated_data,\n\t\tsender_kid: kid,\n\t};\n\tlet key_seq = frame.get_seq();";
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let getters = permutation
			.map(|getter| getter_declarations[getter])
			.join("\n\t");
		let replacement = format!(
			"\t{getters}\n\tif kid != expected_sender_kid {{\n\t\treturn None;\n\t}}\n\tlet ct_len = ciphertext.len();\n\tif ct_len <= MESSAGE_OVERHEAD {{\n\t\treturn None;\n\t}}\n\tlet context = OpenFrameContext {{\n\t\tciphertext,\n\t\tassociated_data,\n\t\tsender_kid: kid,\n\t}};"
		);
		assert_rejected(
			&format!("cryptoframe_getter_permutation_{index}"),
			"CryptoFrame parser and gate evaluation order",
			move |snapshot| {
				replace_once(&mut snapshot.adapter_ratchet, getter_block, &replacement);
			},
		);
		mutation_count += 1;
	}

	assert_rejected(
		"cryptoframe_sender_gate_compares_wire_to_itself",
		"CryptoFrame expected-sender gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn decrypt_message_with_ratchet(",
				"if kid != expected_sender_kid {",
				"if kid != frame.get_key_id() {",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"cryptoframe_open_length_accepts_exact_overhead",
		"CryptoFrame open length gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn open_frame(",
				"if ct_len <= MESSAGE_OVERHEAD",
				"if ct_len < MESSAGE_OVERHEAD",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"cryptoframe_parser_length_accepts_exact_overhead",
		"CryptoFrame pre-ratchet length gate",
		|snapshot| {
			let start = snapshot
				.adapter_ratchet
				.find("fn decrypt_message_with_ratchet(")
				.unwrap();
			let relative = snapshot.adapter_ratchet[start..]
				.find("if ct_len <= MESSAGE_OVERHEAD")
				.unwrap();
			let gate = start + relative;
			snapshot.adapter_ratchet.replace_range(
				gate..gate + "if ct_len <= MESSAGE_OVERHEAD".len(),
				"if ct_len < MESSAGE_OVERHEAD",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_open_context_payload_is_wire_data",
			"\t\tciphertext,\n\t\tassociated_data,",
			"\t\tciphertext: data,\n\t\tassociated_data,",
			"CryptoFrame open context mapping",
		),
		(
			"cryptoframe_open_context_ad_is_ciphertext",
			"\t\tciphertext,\n\t\tassociated_data,",
			"\t\tciphertext,\n\t\tassociated_data: ciphertext.try_into().ok()?,",
			"CryptoFrame open context mapping",
		),
		(
			"cryptoframe_open_context_sender_is_expected",
			"sender_kid: kid,",
			"sender_kid: expected_sender_kid,",
			"CryptoFrame open context mapping",
		),
		(
			"cryptoframe_ratchet_selects_sender_as_sequence",
			"begin_receive(kernel, key_seq, context)",
			"begin_receive(kernel, kid, context)",
			"CryptoFrame parsed-sequence ratchet selection",
		),
		(
			"cryptoframe_open_capability_pattern_is_mutable",
			"verified_ratchet::ReceiveEffect::ReceiveOpenRequested(open) =>",
			"beaconcrypt_core::ratchet::ReceiveEffect::ReceiveOpenRequested(open) =>",
			"CryptoFrame parser and gate evaluation order",
		),
		(
			"cryptoframe_open_uses_parsed_not_returned_sequence",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, key_seq, open.context())",
			"CryptoFrame selected receive material and sequence",
		),
		(
			"cryptoframe_open_uses_rebuilt_context",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, open.sequence(), &context)",
			"CryptoFrame selected receive material and sequence",
		),
		(
			"cryptoframe_open_finish_discards_plaintext",
			"open.finish(opened)",
			"open.finish(None)",
			"CryptoFrame one-use receive completion",
		),
		(
			"cryptoframe_result_swaps_sender_sequence",
			"key_id: kid,\n\t\tseq: key_seq,",
			"key_id: key_seq,\n\t\tseq: kid,",
			"CryptoFrame returned parsed metadata",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn decrypt_message_with_ratchet(",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"cryptoframe_open_renames_returned_material",
		"CryptoFrame selected receive material and sequence",
		|snapshot| {
			replace_once(
				&mut snapshot.adapter_ratchet,
				"let Some(material) = open.material() else {",
				"let Some(selected_material) = open.material() else {",
			);
			replace_once(
				&mut snapshot.adapter_ratchet,
				"open_frame(material, open.sequence(), open.context())",
				"open_frame(selected_material, open.sequence(), open.context())",
			);
		},
	);
	mutation_count += 1;

	for (name, fields) in [
		(
			"cryptoframe_schema_seq_type_drift",
			[
				("seq", 0, "Data"),
				("keyId", 1, "UInt64"),
				("cipherText", 2, "Data"),
			],
		),
		(
			"cryptoframe_schema_sender_type_drift",
			[
				("seq", 0, "UInt64"),
				("keyId", 1, "Data"),
				("cipherText", 2, "Data"),
			],
		),
		(
			"cryptoframe_schema_payload_type_drift",
			[
				("seq", 0, "UInt64"),
				("keyId", 1, "UInt64"),
				("cipherText", 2, "UInt64"),
			],
		),
	] {
		assert_rejected(name, "CryptoFrame schema changed", move |snapshot| {
			replace_cryptoframe_schema(snapshot, &fields);
		});
		mutation_count += 1;
	}
	assert_rejected(
		"cryptoframe_schema_extra_field",
		"CryptoFrame schema changed",
		|snapshot| {
			replace_cryptoframe_schema(
				snapshot,
				&[
					("seq", 0, "UInt64"),
					("keyId", 1, "UInt64"),
					("cipherText", 2, "Data"),
					("targetId", 3, "UInt64"),
				],
			);
		},
	);
	mutation_count += 1;

	for (index, duplicated) in [
		["plaintext", "plaintext", "commitment"],
		["plaintext", "tag", "tag"],
		["commitment", "tag", "commitment"],
	]
	.into_iter()
	.enumerate()
	{
		let replacement = format!(
			"\tlet mut payload = vec![];\n\tpayload.append(&mut {});\n\tpayload.append(&mut {});\n\tpayload.append(&mut {});",
			duplicated[0], duplicated[1], duplicated[2]
		);
		assert_rejected(
			&format!("cryptoframe_payload_duplicate_{index}"),
			"CryptoFrame seal payload order",
			move |snapshot| {
				replace_once(
					&mut snapshot.adapter_ratchet,
					"\tplaintext.append(&mut tag);\n\tplaintext.append(&mut commitment);",
					&replacement,
				);
				replace_once(
					&mut snapshot.adapter_ratchet,
					"builder.set_cipher_text(&plaintext)",
					"builder.set_cipher_text(&payload)",
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_open_uses_zero_key",
			"let key: AeadKey = (*material.key().as_bytes()).into();",
			"let key: AeadKey = [0u8; AEAD_KEY_LEN].into();",
			"CryptoFrame open selected key",
		),
		(
			"cryptoframe_open_uses_zero_nonce",
			"let nonce: AeadNonce = (*material.nonce().as_bytes()).into();",
			"let nonce: AeadNonce = [0u8; AEAD_NONCE_LEN].into();",
			"CryptoFrame open selected nonce",
		),
		(
			"cryptoframe_open_tag_slice_starts_late",
			"ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE",
			"ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN + 1..ct_len - COMMITMENT_SIZE",
			"CryptoFrame open commitment mapping",
		),
		(
			"cryptoframe_open_tag_slice_ends_late",
			"ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE",
			"ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE + 1",
			"CryptoFrame open commitment mapping",
		),
		(
			"cryptoframe_open_tag_uses_commitment_suffix",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE]",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE..]",
			"CryptoFrame open commitment mapping",
		),
		(
			"cryptoframe_open_commitment_slice_starts_late",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE..]",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE + 1..]",
			"CryptoFrame libsodium memcmp commitment comparison",
		),
		(
			"cryptoframe_open_commitment_slice_ends_early",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE..]",
			"&context.ciphertext[ct_len - COMMITMENT_SIZE..ct_len - 1]",
			"CryptoFrame libsodium memcmp commitment comparison",
		),
		(
			"cryptoframe_open_decrypts_ciphertext_without_tag",
			"&context.ciphertext[..ct_len - COMMITMENT_SIZE]",
			"&context.ciphertext[..ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN]",
			"CryptoFrame C-and-tag AEAD open",
		),
		(
			"cryptoframe_open_decrypts_commitment_too",
			"&context.ciphertext[..ct_len - COMMITMENT_SIZE]",
			"context.ciphertext",
			"CryptoFrame C-and-tag AEAD open",
		),
		(
			"cryptoframe_open_decrypt_prefix_boundary_late",
			"&context.ciphertext[..ct_len - COMMITMENT_SIZE]",
			"&context.ciphertext[..ct_len - COMMITMENT_SIZE + 1]",
			"CryptoFrame C-and-tag AEAD open",
		),
		(
			"cryptoframe_open_omits_associated_data",
			"Some(context.associated_data.as_slice()),",
			"None,",
			"CryptoFrame C-and-tag AEAD open",
		),
		(
			"cryptoframe_open_commitment_swaps_sequence_sender",
			"\t\tkey_seq,\n\t\tcontext.sender_kid,",
			"\t\tcontext.sender_kid,\n\t\tkey_seq,",
			"CryptoFrame open commitment mapping",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_ratchet, "fn open_frame(", from, to);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"cryptoframe_open_decrypts_before_commitment_equality",
		"CryptoFrame commitment-before-AEAD order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn open_frame(",
				"\tif !memcmp(&commitment, &context.ciphertext[ct_len - COMMITMENT_SIZE..]) {\n\t\treturn None;\n\t}\n\tlet key: AeadKey = (*material.key().as_bytes()).into();\n\tlet nonce: AeadNonce = (*material.nonce().as_bytes()).into();\n\tcrypto_aead::chacha20poly1305_ietf::decrypt(\n\t\t&context.ciphertext[..ct_len - COMMITMENT_SIZE],\n\t\tSome(context.associated_data.as_slice()),\n\t\t&nonce,\n\t\t&key,\n\t)\n\t.ok()",
				"\tlet key: AeadKey = (*material.key().as_bytes()).into();\n\tlet nonce: AeadNonce = (*material.nonce().as_bytes()).into();\n\tlet opened = crypto_aead::chacha20poly1305_ietf::decrypt(\n\t\t&context.ciphertext[..ct_len - COMMITMENT_SIZE],\n\t\tSome(context.associated_data.as_slice()),\n\t\t&nonce,\n\t\t&key,\n\t)\n\t.ok();\n\tif !memcmp(&commitment, &context.ciphertext[ct_len - COMMITMENT_SIZE..]) {\n\t\treturn None;\n\t}\n\topened",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_commitment_extracts_zero_key",
			"let key = material.key().as_bytes();",
			"let key = &[0u8; AEAD_KEY_LEN];",
			"CryptoFrame commitment selected key",
		),
		(
			"cryptoframe_commitment_extracts_zero_nonce",
			"let nonce = material.nonce().as_bytes();",
			"let nonce = &[0u8; AEAD_NONCE_LEN];",
			"CryptoFrame commitment selected nonce",
		),
		(
			"cryptoframe_commitment_converts_tag_as_ad",
			"let ad = ad.try_into().ok()?;",
			"let ad = tag.try_into().ok()?;",
			"CryptoFrame commitment fixed-width AD",
		),
		(
			"cryptoframe_commitment_uses_ad_prefix_as_tag",
			"let tag = tag.try_into().ok()?;",
			"let tag = ad[..AEAD_TAG_LEN].try_into().ok()?;",
			"CryptoFrame commitment fixed-width retained tag",
		),
		(
			"cryptoframe_commitment_core_call_swaps_sequence_sender",
			"build_commitment_transcript(key, nonce, ad, tag, seq, kid)",
			"build_commitment_transcript(key, nonce, ad, tag, kid, seq)",
			"CryptoFrame adapter-to-core commitment mapping",
		),
		(
			"cryptoframe_commitment_hash_output_shortened",
			"generichash(input.as_bytes(), None, COMMITMENT_SIZE)",
			"generichash(input.as_bytes(), None, COMMITMENT_SIZE - 1)",
			"CryptoFrame unkeyed commitment hash",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn build_commitment(",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_core_key_size_drift",
			"pub const AEAD_KEY_SIZE: usize = 32;",
			"pub const AEAD_KEY_SIZE: usize = 31;",
			"CryptoFrame core key size",
		),
		(
			"cryptoframe_core_nonce_size_drift",
			"pub const AEAD_NONCE_SIZE: usize = 12;",
			"pub const AEAD_NONCE_SIZE: usize = 11;",
			"CryptoFrame core nonce size",
		),
		(
			"cryptoframe_core_ad_size_source_drift",
			"pub const ASSOCIATED_DATA_SIZE: usize = crate::constants::ASSOCIATED_DATA_SIZE;",
			"pub const ASSOCIATED_DATA_SIZE: usize = 152;",
			"CryptoFrame core associated-data size source",
		),
		(
			"cryptoframe_core_tag_size_drift",
			"pub const AEAD_TAG_SIZE: usize = 16;",
			"pub const AEAD_TAG_SIZE: usize = 15;",
			"CryptoFrame core tag size",
		),
		(
			"cryptoframe_core_integer_size_drift",
			"pub const ENCODED_U64_SIZE: usize = 8;",
			"pub const ENCODED_U64_SIZE: usize = 7;",
			"CryptoFrame core integer size",
		),
		(
			"cryptoframe_core_transcript_formula_omits_sender",
			"AEAD_TAG_SIZE + (2 * ENCODED_U64_SIZE)",
			"AEAD_TAG_SIZE + ENCODED_U64_SIZE",
			"CryptoFrame core transcript-size formula",
		),
		(
			"cryptoframe_core_ad_length_assertion_drift",
			"assert!(ASSOCIATED_DATA_SIZE == 153)",
			"assert!(ASSOCIATED_DATA_SIZE == 152)",
			"CryptoFrame core associated-data length",
		),
		(
			"cryptoframe_core_transcript_length_assertion_drift",
			"assert!(COMMITMENT_TRANSCRIPT_SIZE == 229)",
			"assert!(COMMITMENT_TRANSCRIPT_SIZE == 228)",
			"CryptoFrame core transcript length",
		),
		(
			"cryptoframe_core_result_uses_literal_size",
			"bytes: [u8; COMMITMENT_TRANSCRIPT_SIZE]",
			"bytes: [u8; 229]",
			"CryptoFrame core fixed-width result",
		),
		(
			"cryptoframe_core_sequence_parameter_narrows",
			"sequence: u64,\n\tsender_id: u64,",
			"sequence: u32,\n\tsender_id: u64,",
			"CryptoFrame core transcript signature",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_commitment, from, to);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"cryptoframe_core_le64_uses_big_endian_order",
		"CryptoFrame core LE64 encoding",
		|snapshot| {
			replace_once(
				&mut snapshot.core_commitment,
				"\t\tvalue as u8,\n\t\t(value >> 8) as u8,\n\t\t(value >> 16) as u8,\n\t\t(value >> 24) as u8,\n\t\t(value >> 32) as u8,\n\t\t(value >> 40) as u8,\n\t\t(value >> 48) as u8,\n\t\t(value >> 56) as u8,",
				"\t\t(value >> 56) as u8,\n\t\t(value >> 48) as u8,\n\t\t(value >> 40) as u8,\n\t\t(value >> 32) as u8,\n\t\t(value >> 24) as u8,\n\t\t(value >> 16) as u8,\n\t\t(value >> 8) as u8,\n\t\tvalue as u8,",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"cryptoframe_core_swaps_encoded_sequence_sender",
		"CryptoFrame core integer mapping",
		|snapshot| {
			replace_once(
				&mut snapshot.core_commitment,
				"\tlet sequence = encode_u64_le(sequence);\n\tlet sender_id = encode_u64_le(sender_id);",
				"\tlet sequence = encode_u64_le(sender_id);\n\tlet sender_id = encode_u64_le(sequence);",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"cryptoframe_core_key_bytes_reversed",
			"key[i]",
			"key[31 - i]",
			"CryptoFrame core key field",
		),
		(
			"cryptoframe_core_nonce_offset_drift",
			"nonce[i - 32]",
			"nonce[i - 31]",
			"CryptoFrame core nonce field",
		),
		(
			"cryptoframe_core_ad_offset_drift",
			"associated_data[i - 44]",
			"associated_data[i - 43]",
			"CryptoFrame core associated-data field",
		),
		(
			"cryptoframe_core_tag_offset_drift",
			"tag[i - 197]",
			"tag[i - 196]",
			"CryptoFrame core retained-tag field",
		),
		(
			"cryptoframe_core_sequence_offset_drift",
			"sequence[i - 213]",
			"sequence[i - 212]",
			"CryptoFrame core sequence field",
		),
		(
			"cryptoframe_core_sender_offset_drift",
			"sender_id[i - 221]",
			"sender_id[i - 220]",
			"CryptoFrame core sender-ID field",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_commitment, from, to);
		});
		mutation_count += 1;
	}
	assert_rejected(
		"cryptoframe_core_array_builder_spelling_drift",
		"CryptoFrame core fixed-width construction",
		|snapshot| {
			replace_once(
				&mut snapshot.core_commitment,
				"core::array::from_fn(|i|",
				"core::array::from_fn::<_, COMMITMENT_TRANSCRIPT_SIZE, _>(|i|",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"cryptoframe_core_result_clones_bytes",
		"CryptoFrame core transcript result",
		|snapshot| {
			replace_once(
				&mut snapshot.core_commitment,
				"CommitmentTranscript { bytes }",
				"CommitmentTranscript { bytes: bytes.clone() }",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"cryptoframe_core_reorders_tag_and_sequence_branches",
		"CryptoFrame core transcript field order",
		|snapshot| {
			replace_once(
				&mut snapshot.core_commitment,
				"\t\t} else if i < 213 {\n\t\t\ttag[i - 197]\n\t\t} else if i < 221 {\n\t\t\tsequence[i - 213]",
				"\t\t} else if i < 221 {\n\t\t\tsequence[i - 213]\n\t\t} else if i < 213 {\n\t\t\ttag[i - 197]",
			);
		},
	);
	mutation_count += 1;

	let symbolic_fields = ["ciphertext", "retained_aead_tag", "commitment"];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let fields = permutation.map(|field| symbolic_fields[field]);
		let mutated = format!(
			"crypto_frame.fields={},sequence,sender_id",
			fields.join(",")
		);
		assert_rejected(
			&format!("cryptoframe_symbolic_annotation_permutation_{index}"),
			"CryptoFrame symbolic semantic field order",
			move |snapshot| {
				replace_once(
					&mut snapshot.crypto,
					"crypto_frame.fields=ciphertext,retained_aead_tag,commitment,sequence,sender_id",
					&mutated,
				);
			},
		);
		mutation_count += 1;
	}
	assert_rejected(
		"cryptoframe_symbolic_annotation_uses_target_id",
		"CryptoFrame symbolic semantic field order",
		|snapshot| {
			replace_once(
				&mut snapshot.crypto,
				"commitment,sequence,sender_id *)",
				"commitment,sequence,target_id *)",
			);
		},
	);
	mutation_count += 1;
	for (name, from, to) in [
		(
			"cryptoframe_symbolic_sequence_type_drift",
			"  sequence,\n  key_id\n): bitstring [data].",
			"  key_id,\n  key_id\n): bitstring [data].",
		),
		(
			"cryptoframe_symbolic_sender_type_drift",
			"  sequence,\n  key_id\n): bitstring [data].",
			"  sequence,\n  bitstring\n): bitstring [data].",
		),
	] {
		assert_rejected(
			name,
			"CryptoFrame symbolic constructor declaration",
			|snapshot| {
				replace_once(&mut snapshot.crypto, from, to);
			},
		);
		mutation_count += 1;
	}

	let seal_formals = [
		"material: bitstring",
		"associated_data: bitstring",
		"message_sequence: sequence",
		"sender_id: key_id",
		"plaintext: bitstring",
	];
	let seal_bitstrings = [seal_formals[0], seal_formals[1], seal_formals[4]];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let permuted = permute_cryptoframe(&seal_bitstrings, permutation);
		let mut arguments = seal_formals.map(str::to_owned).to_vec();
		arguments[0] = permuted[0].clone();
		arguments[1] = permuted[1].clone();
		arguments[4] = permuted[2].clone();
		assert_rejected(
			&format!("cryptoframe_symbolic_seal_argument_permutation_{index}"),
			"CryptoFrame symbolic seal arguments",
			move |snapshot| replace_call(&mut snapshot.crypto, "seal_frame", 0, &arguments),
		);
		mutation_count += 1;
	}

	let seal_fields = [
		"aead_cipher(material_key(material),material_nonce(material),associated_data,plaintext)",
		"aead_tag(material_key(material),material_nonce(material),associated_data,plaintext)",
		"ctx_commitment(material_key(material),material_nonce(material),associated_data,aead_tag(material_key(material),material_nonce(material),associated_data,plaintext),message_sequence,sender_id)",
	];
	let seal_tail = ["message_sequence", "sender_id"];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let mut arguments = permute_cryptoframe(&seal_fields, permutation);
		arguments.extend(seal_tail.map(str::to_owned));
		assert_rejected(
			&format!("cryptoframe_symbolic_seal_field_permutation_{index}"),
			"CryptoFrame symbolic seal fields",
			move |snapshot| replace_call(&mut snapshot.crypto, "crypto_frame", 1, &arguments),
		);
		mutation_count += 1;
	}
	for (index, duplicated) in [
		[seal_fields[0], seal_fields[0], seal_fields[2]],
		[seal_fields[0], seal_fields[1], seal_fields[1]],
		[seal_fields[2], seal_fields[1], seal_fields[2]],
	]
	.into_iter()
	.enumerate()
	{
		let mut arguments = duplicated.map(str::to_owned).to_vec();
		arguments.extend(seal_tail.map(str::to_owned));
		let diagnostic = match index {
			1 => "seal CTX input",
			2 => "seal AEAD input",
			_ => "CryptoFrame symbolic seal fields",
		};
		assert_rejected(
			&format!("cryptoframe_symbolic_seal_field_duplicate_{index}"),
			diagnostic,
			move |snapshot| replace_call(&mut snapshot.crypto, "crypto_frame", 1, &arguments),
		);
		mutation_count += 1;
	}

	let open_fields = [
		"aead_cipher(key,nonce,associated_data,plaintext)",
		"aead_tag(key,nonce,associated_data,plaintext)",
		"blake2b512(ctx_preimage(key,nonce,associated_data,aead_tag(key,nonce,associated_data,plaintext),sequence_le64(message_sequence),sender_id_le64(sender_id)))",
	];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let mut arguments = permute_cryptoframe(&open_fields, permutation);
		arguments.extend(seal_tail.map(str::to_owned));
		assert_rejected(
			&format!("cryptoframe_symbolic_open_field_permutation_{index}"),
			"CryptoFrame symbolic open fields",
			move |snapshot| replace_call(&mut snapshot.crypto, "crypto_frame", 2, &arguments),
		);
		mutation_count += 1;
	}
	for (index, duplicated) in [
		[open_fields[0], open_fields[0], open_fields[2]],
		[open_fields[0], open_fields[1], open_fields[1]],
		[open_fields[2], open_fields[1], open_fields[2]],
	]
	.into_iter()
	.enumerate()
	{
		let mut arguments = duplicated.map(str::to_owned).to_vec();
		arguments.extend(seal_tail.map(str::to_owned));
		let diagnostic = if index == 1 {
			"open CTX input"
		} else {
			"CryptoFrame symbolic open fields"
		};
		assert_rejected(
			&format!("cryptoframe_symbolic_open_field_duplicate_{index}"),
			diagnostic,
			move |snapshot| replace_call(&mut snapshot.crypto, "crypto_frame", 2, &arguments),
		);
		mutation_count += 1;
	}

	let open_frame_arguments = [
		"ratchet_key_nonce(key,nonce)",
		"associated_data",
		"message_sequence",
		"sender_id",
		"crypto_frame(aead_cipher(key,nonce,associated_data,plaintext),aead_tag(key,nonce,associated_data,plaintext),blake2b512(ctx_preimage(key,nonce,associated_data,aead_tag(key,nonce,associated_data,plaintext),sequence_le64(message_sequence),sender_id_le64(sender_id))),message_sequence,sender_id)",
	];
	let open_bitstrings = [
		open_frame_arguments[0],
		open_frame_arguments[1],
		open_frame_arguments[4],
	];
	for (index, permutation) in cryptoframe_permutations().into_iter().skip(1).enumerate() {
		let permuted = permute_cryptoframe(&open_bitstrings, permutation);
		let mut arguments = open_frame_arguments.map(str::to_owned).to_vec();
		arguments[0] = permuted[0].clone();
		arguments[1] = permuted[1].clone();
		arguments[4] = permuted[2].clone();
		assert_rejected(
			&format!("cryptoframe_symbolic_open_argument_permutation_{index}"),
			"CryptoFrame symbolic open acceptance",
			move |snapshot| replace_call(&mut snapshot.crypto, "open_frame", 0, &arguments),
		);
		mutation_count += 1;
	}
	assert_rejected(
		"cryptoframe_symbolic_open_returns_associated_data",
		"CryptoFrame symbolic open result",
		|snapshot| {
			let end = snapshot.crypto.rfind(") = plaintext.").unwrap();
			snapshot
				.crypto
				.replace_range(end..end + ") = plaintext.".len(), ") = associated_data.");
		},
	);
	mutation_count += 1;

	for (name, occurrence, seal_context, diagnostic) in [
		(
			"cryptoframe_symbolic_seal_commitment_uses_different_tag",
			1,
			true,
			"seal CTX input",
		),
		(
			"cryptoframe_symbolic_open_commitment_uses_different_tag",
			3,
			false,
			"open CTX input",
		),
	] {
		let arguments = if seal_context {
			[
				"material_key(material)",
				"material_nonce(material)",
				"associated_data",
				"associated_data",
			]
			.map(str::to_owned)
		} else {
			["key", "nonce", "associated_data", "associated_data"].map(str::to_owned)
		};
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_call(&mut snapshot.crypto, "aead_tag", occurrence, &arguments);
		});
		mutation_count += 1;
	}

	let ctx_fields = [
		"key",
		"nonce",
		"associated_data",
		"retained_aead_tag",
		"sequence_le64(message_sequence)",
		"sender_id_le64(sender_id)",
	];
	for left in 0..6 {
		for right in left + 1..6 {
			let mut arguments = ctx_fields.map(str::to_owned);
			arguments.swap(left, right);
			assert_rejected(
				&format!("cryptoframe_ctx_pair_transposition_{left}_{right}"),
				"CTX preimage field order",
				move |snapshot| {
					replace_call(&mut snapshot.interface, "ctx_preimage", 1, &arguments);
				},
			);
			mutation_count += 1;
		}
	}
	for omitted in 0..6 {
		let mut arguments = ctx_fields.map(str::to_owned);
		arguments[omitted] = ctx_fields[(omitted + 1) % 6].to_owned();
		assert_rejected(
			&format!("cryptoframe_ctx_omits_and_duplicates_field_{omitted}"),
			"CTX preimage field order",
			move |snapshot| {
				replace_call(&mut snapshot.interface, "ctx_preimage", 1, &arguments);
			},
		);
		mutation_count += 1;
	}

	assert_eq!(mutation_count, CRYPTOFRAME_WIRE_MUTATION_COUNT);
}

const PHASE1_REGISTRATION_MUTATION_COUNT: usize = 163;

#[test]
fn phase1_registration_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	for key in [
		"phase1.init_kex.constructor",
		"phase1.init_kex.field_count",
		"phase1.init_kex.field.0",
		"phase1.init_kex.field.1",
		"phase1.init_kex.field.2",
		"phase1.init_kex.field.3",
		"phase1.signature.primitive",
		"phase1.signature.format",
		"phase1.init_kex.beacon_writes",
		"phase1.init_kex.beacon_signs",
		"phase1.init_kex.server_reads",
		"phase1.init_kex.server.verifies",
		"phase1.init_kex.server.from_encoded",
		"phase1.init_kex.server.validates",
		"phase1.init_kex.symbolic.fields",
		"phase1.init_kex.symbolic.producers",
		"phase1.init_kex.symbolic.consumers",
		"phase1.init_kex.symbolic.validation",
	] {
		let name = format!("changed_{key}");
		assert_rejected(&name, key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, "mutated");
		});
		mutation_count += 1;
	}

	const SCHEMA_FIELDS: [(&str, usize); 4] = [
		("identityKey", 0),
		("preKey", 1),
		("oneTimeKey", 2),
		("pqKey", 3),
	];
	let permutations = phase1_permutations();
	assert_eq!(permutations.len(), 24);
	for (index, permutation) in permutations
		.iter()
		.copied()
		.filter(|permutation| permutation != &[0, 1, 2, 3])
		.enumerate()
	{
		let fields = permutation.map(|field| SCHEMA_FIELDS[field]);
		let name = format!("phase1_schema_same_typed_permutation_{index}");
		assert_rejected(&name, "Phase-1 InitKex schema", move |snapshot| {
			replace_phase1_schema(snapshot, &fields);
		});
		mutation_count += 1;
	}
	for omitted in 0..4 {
		let fields = SCHEMA_FIELDS
			.iter()
			.enumerate()
			.filter(|(index, _)| *index != omitted)
			.enumerate()
			.map(|(ordinal, (_, (name, _)))| (*name, ordinal))
			.collect::<Vec<_>>();
		let name = format!("phase1_schema_omits_field_{omitted}");
		assert_rejected(&name, "Phase-1 InitKex schema", move |snapshot| {
			replace_phase1_schema(snapshot, &fields);
		});
		mutation_count += 1;
	}
	for (original, renamed) in [
		("identityKey", "renamedIdentityKey"),
		("preKey", "renamedPreKey"),
		("oneTimeKey", "renamedOneTimeKey"),
		("pqKey", "renamedPqKey"),
	] {
		let name = format!("phase1_schema_renames_{original}");
		assert_rejected(&name, "Phase-1 InitKex schema", |snapshot| {
			replace_once(&mut snapshot.phase1_schema, original, renamed);
		});
		mutation_count += 1;
	}
	for (index, permutation) in phase1_transpositions().into_iter().enumerate() {
		let fields = SCHEMA_FIELDS.map(|(name, _)| {
			(
				name,
				permutation[SCHEMA_FIELDS
					.iter()
					.position(|(candidate, _)| candidate == &name)
					.unwrap()],
			)
		});
		let name = format!("phase1_schema_ordinal_drift_{index}");
		assert_rejected(&name, "Phase-1 InitKex schema", move |snapshot| {
			replace_phase1_schema(snapshot, &fields);
		});
		mutation_count += 1;
	}

	let beacon_setters = [
		(
			"bundle.set_identity_key",
			"started.message.identity_key()",
			"Phase-1 Beacon identity setter mapping",
		),
		(
			"bundle.set_pre_key",
			"&prekey_sig",
			"Phase-1 Beacon prekey setter mapping",
		),
		(
			"bundle.set_one_time_key",
			"&onetime_sig",
			"Phase-1 Beacon one-time setter mapping",
		),
		(
			"bundle.set_pq_key",
			"&pq_sig",
			"Phase-1 Beacon ML-KEM setter mapping",
		),
	];
	let beacon_payloads = [
		"started.message.identity_key()",
		"&crypto_sign::sign(started.message.prekey(), self.identity_sk()).ok()?",
		"&crypto_sign::sign(started.message.one_time_key(), self.identity_sk()).ok()?",
		"&crypto_sign::sign(started.message.pq_key(), self.identity_sk()).ok()?",
	];
	for (setter_index, (function, canonical, diagnostic)) in beacon_setters.iter().enumerate() {
		for (payload_index, payload) in beacon_payloads.iter().enumerate() {
			if setter_index == payload_index {
				continue;
			}
			let name = format!("phase1_beacon_setter_{setter_index}_uses_{payload_index}");
			let from = format!("{function}({canonical});");
			let to = format!("{function}({payload});");
			assert_rejected(&name, diagnostic, |snapshot| {
				replace_once(&mut snapshot.adapter_beacon, &from, &to);
			});
			mutation_count += 1;
		}
	}
	let signed_inputs = [
		"started.message.prekey()",
		"started.message.one_time_key()",
		"started.message.pq_key()",
	];
	for (signature_index, canonical) in signed_inputs.iter().enumerate() {
		for (input_index, replacement) in signed_inputs.iter().enumerate() {
			if signature_index == input_index {
				continue;
			}
			let name = format!("phase1_beacon_signature_{signature_index}_uses_{input_index}");
			let from = format!("crypto_sign::sign({canonical}, self.identity_sk())");
			let to = format!("crypto_sign::sign({replacement}, self.identity_sk())");
			assert_rejected(
				&name,
				"Phase-1 Beacon attached-signature inputs",
				|snapshot| {
					replace_once(&mut snapshot.adapter_beacon, &from, &to);
				},
			);
			mutation_count += 1;
		}
	}

	let server_consumers = [
		(
			"registration.get_identity_key()",
			"Phase-1 Server identity consumer",
		),
		(
			"registration.get_pre_key()",
			"Phase-1 Server prekey signature consumer",
		),
		(
			"registration.get_one_time_key()",
			"Phase-1 Server one-time signature consumer",
		),
		(
			"registration.get_pq_key()",
			"Phase-1 Server ML-KEM signature consumer",
		),
	];
	for (consumer_index, (canonical, diagnostic)) in server_consumers.iter().enumerate() {
		for (field_index, (replacement, _)) in server_consumers.iter().enumerate() {
			if consumer_index == field_index {
				continue;
			}
			let name = format!("phase1_server_consumer_{consumer_index}_uses_{field_index}");
			assert_rejected(&name, diagnostic, |snapshot| {
				replace_once(&mut snapshot.adapter_server, canonical, replacement);
			});
			mutation_count += 1;
		}
	}
	for (name, getter, diagnostic) in [
		(
			"phase1_server_pq_verifies_under_local_identity",
			"registration.get_pq_key().ok()?",
			"Phase-1 Server ML-KEM signature consumer",
		),
		(
			"phase1_server_prekey_verifies_under_local_identity",
			"registration.get_pre_key().ok()?",
			"Phase-1 Server prekey signature consumer",
		),
		(
			"phase1_server_one_time_verifies_under_local_identity",
			"registration.get_one_time_key().ok()?",
			"Phase-1 Server one-time signature consumer",
		),
	] {
		let from = format!("crypto_sign::verify({getter}, &remote_id)");
		let to = format!("crypto_sign::verify({getter}, self.identity_pk())");
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_server, &from, &to);
		});
		mutation_count += 1;
	}
	let encoded_identity = "encoded_identity";
	let prekey_verified = "prekey_verified.as_slice().try_into().ok()?";
	let onetime_verified = "onetime_verified.as_slice().try_into().ok()?";
	let pq_verified = "pq_verified.as_slice().try_into().ok()?";
	for (name, arguments) in [
		(
			"phase1_from_encoded_duplicates_one_time",
			[
				encoded_identity,
				onetime_verified,
				onetime_verified,
				pq_verified,
			],
		),
		(
			"phase1_from_encoded_duplicates_prekey",
			[
				encoded_identity,
				prekey_verified,
				prekey_verified,
				pq_verified,
			],
		),
		(
			"phase1_from_encoded_swaps_x25519_roles",
			[
				encoded_identity,
				onetime_verified,
				prekey_verified,
				pq_verified,
			],
		),
	] {
		let arguments = arguments.map(str::to_owned);
		assert_rejected(
			name,
			"Phase-1 Server from_encoded mapping",
			move |snapshot| {
				replace_call(
					&mut snapshot.adapter_server,
					"verified_pqxdh::InitKex::from_encoded",
					0,
					&arguments,
				);
			},
		);
		mutation_count += 1;
	}

	let declaration_arguments = [
		"encoded_identity",
		"signed_prekey",
		"signed_one_time",
		"signed_pq",
	];
	let producer_arguments = [
		"tag_ed25519(beacon_identity)",
		"sign(tag_x25519_prekey(beacon_prekey), beacon_identity_secret)",
		"sign(tag_x25519_one_time(beacon_one_time), beacon_identity_secret)",
		"sign(tag_mlkem768(beacon_pq), beacon_identity_secret)",
	];
	let forged_producer_arguments = [
		"tag_ed25519(beacon_identity)",
		"sign(tag_x25519_prekey(forged_prekey), beacon_identity_secret)",
		"sign(tag_x25519_one_time(forged_one_time), beacon_identity_secret)",
		"sign(tag_mlkem768(forged_pq), beacon_identity_secret)",
	];
	let server_core_arguments = [
		"encoded_identity",
		"tag_x25519_prekey(beacon_prekey)",
		"tag_x25519_one_time(beacon_one_time)",
		"tag_mlkem768(beacon_pq)",
	];
	let honest_core_arguments = [
		"tag_ed25519(beacon_identity)",
		"tag_x25519_prekey(beacon_prekey)",
		"tag_x25519_one_time(beacon_one_time)",
		"tag_mlkem768(beacon_pq)",
	];
	for (index, permutation) in phase1_transpositions().into_iter().enumerate() {
		let declaration = permute_phase1(&declaration_arguments, permutation);
		let declaration_value = declaration.join(",");
		let annotation =
			"signed_init_kex.fields=encoded_identity,signed_prekey,signed_one_time,signed_pq";
		let mutated_annotation = format!("signed_init_kex.fields={declaration_value}");
		assert_rejected(
			&format!("phase1_symbolic_declaration_transposition_{index}"),
			"Phase-1 symbolic constructor semantic order",
			|snapshot| {
				replace_once(&mut snapshot.environment, annotation, &mutated_annotation);
			},
		);
		mutation_count += 1;

		for (name, occurrence, diagnostic) in [
			(
				"honest_producer",
				1,
				"Phase-1 symbolic honest/malicious producer order",
			),
			(
				"malicious_producer",
				2,
				"Phase-1 symbolic honest/malicious producer order",
			),
		] {
			let arguments = permute_phase1(&producer_arguments, permutation);
			assert_rejected(
				&format!("phase1_symbolic_{name}_transposition_{index}"),
				diagnostic,
				move |snapshot| {
					replace_call(
						&mut snapshot.environment,
						"signed_init_kex",
						occurrence,
						&arguments,
					);
				},
			);
			mutation_count += 1;
		}
		let arguments = permute_phase1(&forged_producer_arguments, permutation);
		assert_rejected(
			&format!("phase1_symbolic_active_quantum_producer_transposition_{index}"),
			"Phase-1 active-quantum producer order",
			move |snapshot| {
				replace_call(
					&mut snapshot.active_quantum_witness,
					"signed_init_kex",
					1,
					&arguments,
				);
			},
		);
		mutation_count += 1;

		for (name, occurrence) in [("server_consumer", 3), ("malicious_server_consumer", 4)] {
			let arguments = permute_phase1(&declaration_arguments, permutation);
			assert_rejected(
				&format!("phase1_symbolic_{name}_transposition_{index}"),
				"Phase-1 symbolic Server consumer order",
				move |snapshot| {
					replace_call(
						&mut snapshot.environment,
						"signed_init_kex",
						occurrence,
						&arguments,
					);
				},
			);
			mutation_count += 1;
		}
		let arguments = permute_phase1(&declaration_arguments, permutation);
		assert_rejected(
			&format!("phase1_symbolic_active_quantum_consumer_transposition_{index}"),
			"Phase-1 active-quantum consumer order",
			move |snapshot| {
				replace_call(
					&mut snapshot.active_quantum_witness,
					"signed_init_kex",
					0,
					&arguments,
				);
			},
		);
		mutation_count += 1;

		let arguments = permute_phase1(&honest_core_arguments, permutation);
		assert_rejected(
			&format!("phase1_symbolic_honest_core_transposition_{index}"),
			"Phase-1 symbolic honest core mapping",
			move |snapshot| {
				replace_call(
					&mut snapshot.environment,
					"beaconcrypt_core__pqxdh__InitKex",
					0,
					&arguments,
				);
			},
		);
		mutation_count += 1;
		for (name, occurrence) in [("server_core", 1), ("malicious_server_core", 2)] {
			let arguments = permute_phase1(&server_core_arguments, permutation);
			assert_rejected(
				&format!("phase1_symbolic_{name}_transposition_{index}"),
				"Phase-1 symbolic Server core mapping",
				move |snapshot| {
					replace_call(
						&mut snapshot.environment,
						"beaconcrypt_core__pqxdh__InitKex",
						occurrence,
						&arguments,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (name, from, to, diagnostic) in [
		(
			"phase1_core_prekey_uses_one_time_role",
			"prekey: tag_x25519_key(KEY_ROLE_PREKEY, inputs.prekey_public_key)",
			"prekey: tag_x25519_key(KEY_ROLE_ONE_TIME, inputs.prekey_public_key)",
			"Phase-1 core prekey encoding",
		),
		(
			"phase1_core_one_time_uses_prekey_role",
			"one_time_key: tag_x25519_key(KEY_ROLE_ONE_TIME, coins.one_time_public_key)",
			"one_time_key: tag_x25519_key(KEY_ROLE_PREKEY, coins.one_time_public_key)",
			"Phase-1 core one-time encoding",
		),
		(
			"phase1_core_prekey_validates_one_time_role",
			"untag_x25519_key(message.prekey, KEY_ROLE_PREKEY)",
			"untag_x25519_key(message.prekey, KEY_ROLE_ONE_TIME)",
			"Phase-1 core X25519 prekey role validation",
		),
		(
			"phase1_core_one_time_validates_prekey_role",
			"untag_x25519_key(message.one_time_key, KEY_ROLE_ONE_TIME)",
			"untag_x25519_key(message.one_time_key, KEY_ROLE_PREKEY)",
			"Phase-1 core X25519 one-time role validation",
		),
	] {
		assert_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_pqxdh, from, to);
		});
		mutation_count += 1;
	}
	assert_rejected(
		"phase1_server_accepts_mlkem_identity_tag",
		"Phase-1 Server Ed25519 identity tag gate",
		|snapshot| {
			replace_once(
				&mut snapshot.adapter_server,
				"encoded_identity[0] != verified_pqxdh::SIGN_TYPE_ED25519",
				"encoded_identity[0] != verified_pqxdh::KEM_TYPE_MLKEM768",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_server_decodes_identity_with_tag",
		"Phase-1 Server identity decoder",
		|snapshot| {
			replace_once(
				&mut snapshot.adapter_server,
				"crypto_sign::PublicKey::from_bytes(&encoded_identity[1..])",
				"crypto_sign::PublicKey::from_bytes(&encoded_identity[..32])",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_symbolic_signature_verifies_under_x25519_key",
		"Phase-1 symbolic attached-signature verification",
		|snapshot| {
			replace_once(
				&mut snapshot.crypto,
				"ed_public(signing_key)) = message",
				"x25519_public(signing_key)) = message",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_server_reorders_pq_and_prekey_verification",
		"Phase-1 Server source evaluation order",
		|snapshot| {
			replace_once(
				&mut snapshot.adapter_server,
				"\t\tlet pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id)?;\n\t\tlet prekey_verified = crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id)?;",
				"\t\tlet prekey_verified = crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id)?;\n\t\tlet pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id)?;",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_symbolic_reorders_prekey_and_one_time_gates",
		"Phase-1 symbolic pure-gate evaluation order",
		|snapshot| {
			replace_once(
				&mut snapshot.environment,
				"  let tag_x25519_prekey(beacon_prekey: bitstring) =\n    verify_signature(signed_prekey, beacon_identity)\n  in\n  let tag_x25519_one_time(beacon_one_time: bitstring) =\n    verify_signature(signed_one_time, beacon_identity)\n  in",
				"  let tag_x25519_one_time(beacon_one_time: bitstring) =\n    verify_signature(signed_one_time, beacon_identity)\n  in\n  let tag_x25519_prekey(beacon_prekey: bitstring) =\n    verify_signature(signed_prekey, beacon_identity)\n  in",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_beacon_serializes_identity_after_prekey_signature",
		"Phase-1 Beacon serialization order",
		|snapshot| {
			replace_once(
				&mut snapshot.adapter_beacon,
				"\t\tbundle.set_identity_key(started.message.identity_key());\n\t\tlet prekey_sig = crypto_sign::sign(started.message.prekey(), self.identity_sk()).ok()?;\n\t\tbundle.set_pre_key(&prekey_sig);",
				"\t\tlet prekey_sig = crypto_sign::sign(started.message.prekey(), self.identity_sk()).ok()?;\n\t\tbundle.set_identity_key(started.message.identity_key());\n\t\tbundle.set_pre_key(&prekey_sig);",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_core_reorders_prekey_and_one_time_fields",
		"Phase-1 core InitKex field order",
		|snapshot| {
			replace_once(
				&mut snapshot.core_pqxdh,
				"\t\t\tprekey: tag_x25519_key(KEY_ROLE_PREKEY, inputs.prekey_public_key),\n\t\t\tone_time_key: tag_x25519_key(KEY_ROLE_ONE_TIME, coins.one_time_public_key),",
				"\t\t\tone_time_key: tag_x25519_key(KEY_ROLE_ONE_TIME, coins.one_time_public_key),\n\t\t\tprekey: tag_x25519_key(KEY_ROLE_PREKEY, inputs.prekey_public_key),",
			);
		},
	);
	mutation_count += 1;
	assert_rejected(
		"phase1_core_reorders_prekey_and_one_time_validation",
		"Phase-1 core tag-validation order",
		|snapshot| {
			replace_once(
				&mut snapshot.core_pqxdh,
				"\tlet Some(prekey) = untag_x25519_key(message.prekey, KEY_ROLE_PREKEY) else {\n\t\treturn Err(RegistrationError::InvalidKeyEncoding);\n\t};\n\tlet Some(one_time) = untag_x25519_key(message.one_time_key, KEY_ROLE_ONE_TIME) else {\n\t\treturn Err(RegistrationError::InvalidKeyEncoding);\n\t};",
				"\tlet Some(one_time) = untag_x25519_key(message.one_time_key, KEY_ROLE_ONE_TIME) else {\n\t\treturn Err(RegistrationError::InvalidKeyEncoding);\n\t};\n\tlet Some(prekey) = untag_x25519_key(message.prekey, KEY_ROLE_PREKEY) else {\n\t\treturn Err(RegistrationError::InvalidKeyEncoding);\n\t};",
			);
		},
	);
	mutation_count += 1;

	assert_eq!(mutation_count, PHASE1_REGISTRATION_MUTATION_COUNT);
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
