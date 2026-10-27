// SPDX-License-Identifier: 0BSD

//! Exact source contracts for the extracted transport policy and its native delegates.

use super::{Snapshot, require_once, rust_body};

const CONTRACTS: &[(&str, &str)] = &[
	("complete_message_size_admitted", "length<=MAX_MESSAGE_SIZE"),
	(
		"argument_len",
		"ifvalue<=23{1}elseifvalue<=255{2}elseifvalue<=65_535{3}elseifvalue<=4_294_967_295{5}else{9}",
	),
	("new", "Self{value:Some(3)}"),
	(
		"integer",
		"Self{value:matchself.value{Some(length)=>length.checked_add(argument_len(value)),None=>None,},}",
	),
	(
		"bytes",
		"letwith_header=self.integer(byte_lengthasu64);Self{value:matchwith_header.value{Some(length)=>length.checked_add(byte_length),None=>None,},}",
	),
	(
		"finish",
		"matchself.value{Some(length)ifcomplete_message_size_admitted(length)=>Some(length),_=>None,}",
	),
	(
		"encoded_frame_len",
		"CborLength::new().integer(sequence).integer(sender).bytes(ciphertext_length).finish()",
	),
	(
		"encoded_init_len",
		"CborLength::new().bytes(lengths[0]).bytes(lengths[1]).bytes(lengths[2]).bytes(lengths[3]).bytes(lengths[4]).bytes(lengths[5]).finish()",
	),
	(
		"encoded_response_len",
		"CborLength::new().bytes(lengths[0]).bytes(lengths[1]).bytes(lengths[2]).bytes(lengths[3]).integer(assigned_key_id).bytes(lengths[4]).finish()",
	),
	(
		"protected_frame_len",
		"letciphertext_length=matchplaintext_length.checked_add(MESSAGE_OVERHEAD){Some(length)=>length,None=>returnNone,};encoded_frame_len(sequence,sender,ciphertext_length)",
	),
	(
		"registration_response_len",
		"letbound_length=matchapplication_length.checked_add(8){Some(length)=>length,None=>returnNone,};letciphertext_length=matchbound_length.checked_add(MESSAGE_OVERHEAD){Some(length)=>length,None=>returnNone,};encoded_response_len([SIGN_PUBLIC_KEY_SIZE,X25519_PUBLIC_KEY_SIZE,MLKEM768_CIPHERTEXT_SIZE,ciphertext_length,MLDSA_SIGNATURE_LEN,],assigned_key_id,)",
	),
	(
		"admit_frame",
		"ifsender!=expected_sender{returnNone;}Some(FrameView{sequence,sender,ciphertext,})",
	),
	(
		"normalize_registration_application",
		"matchapplication{Some(bytes)=>RegistrationApplication::Provided(bytes),None=>RegistrationApplication::Witness(REGISTRATION_WITNESS),}",
	),
];

const RENDER_BODY: &str = "matchrequest{beaconcrypt_core::transport::RegistrationApplication::Witness(bytes)=>bytes,beaconcrypt_core::transport::RegistrationApplication::Provided(bytes)=>bytes,}";

pub(super) fn validate(snapshot: &Snapshot) -> Result<(), String> {
	for &(name, expected) in CONTRACTS {
		if rust_body(&snapshot.transport_sizing, name)? != expected {
			return Err(format!(
				"CBOR extracted transport policy body differs: {name}"
			));
		}
	}
	if rust_body(&snapshot.adapter_server, "registration_application_bytes")? != RENDER_BODY {
		return Err("CBOR source-selected application view interpreter changed".into());
	}
	require_once(
		&rust_body(&snapshot.adapter_server, "registration_response_fits")?,
		"registration_application_bytes(&application).len()",
		"CBOR size preflight uses the actual core-selected application view",
	)?;
	require_once(
		&rust_body(&snapshot.adapter_server, "build_registration_response")?,
		"letplaintext=registration_application_bytes(&application);",
		"CBOR response uses the actual core-selected application view",
	)?;
	let source = super::compact(&super::uncommented_rust(&snapshot.transport_sizing)?);
	require_once(
		&source,
		"pubconstMAX_MESSAGE_SIZE:usize=33_554_432;",
		"CBOR extracted complete-message bound",
	)?;
	require_once(
		&source,
		"pubconstREGISTRATION_WITNESS:[u8;1]=[0xff];",
		"CBOR registration witness",
	)?;
	Ok(())
}

#[test]
fn extracted_transport_policy_bypass_controls_are_rejected() {
	let mut checked = 0;
	let original = Snapshot::production();
	validate(&original).unwrap();
	let controls = [
		(
			"complete_message_size_admitted",
			"length<=MAX_MESSAGE_SIZE",
			"true",
		),
		("argument_len", "value<=23", "value<=24"),
		("new", "Some(3)", "Some(2)"),
		(
			"integer",
			"length.checked_add(argument_len(value))",
			"Some(length)",
		),
		("bytes", "length.checked_add(byte_length)", "Some(length)"),
		(
			"finish",
			"Some(length)ifcomplete_message_size_admitted(length)",
			"Some(length)",
		),
		(
			"encoded_frame_len",
			".integer(sender)",
			".integer(sequence)",
		),
		("encoded_init_len", ".bytes(lengths[4])", ".bytes(0)"),
		("encoded_response_len", ".bytes(lengths[4])", ".bytes(0)"),
		(
			"protected_frame_len",
			"plaintext_length.checked_add(MESSAGE_OVERHEAD)",
			"Some(plaintext_length)",
		),
		(
			"registration_response_len",
			"application_length.checked_add(8)",
			"Some(application_length)",
		),
		(
			"admit_frame",
			"sender!=expected_sender",
			"sender==expected_sender",
		),
		(
			"normalize_registration_application",
			"Witness(REGISTRATION_WITNESS)",
			"Witness([0])",
		),
	];
	for (name, from, to) in controls {
		let mut changed = original.clone();
		let expected = CONTRACTS
			.iter()
			.find(|(function, _)| *function == name)
			.unwrap()
			.1;
		assert_eq!(expected.matches(from).count(), 1, "control {name}");
		let changed_body = expected.replacen(from, to, 1);
		replace_body(&mut changed.transport_sizing, name, &changed_body);
		assert!(
			validate(&changed).unwrap_err().contains("CBOR"),
			"control {name}"
		);
		checked += 1;
	}
	for (name, from, to) in [
		("complete-message constant", "33_554_432", "33_554_433"),
		("registration witness constant", "[0xff];", "[0];"),
	] {
		let mut changed = original.clone();
		assert_eq!(changed.transport_sizing.matches(from).count(), 1);
		changed.transport_sizing = changed.transport_sizing.replacen(from, to, 1);
		assert!(
			validate(&changed).unwrap_err().contains("CBOR"),
			"control {name}"
		);
		checked += 1;
	}
	// Every request and response byte-string slot must contribute once in source order.
	for (name, fields) in [("encoded_init_len", 6), ("encoded_response_len", 5)] {
		let expected = CONTRACTS
			.iter()
			.find(|(function, _)| *function == name)
			.unwrap()
			.1;
		for field in 0..fields {
			let selected = format!(".bytes(lengths[{field}])");
			assert_eq!(expected.matches(&selected).count(), 1);
			for replacement in [
				String::new(),
				format!(".bytes(lengths[{}])", (field + 1) % fields),
			] {
				let mut changed = original.clone();
				let changed_body = expected.replacen(&selected, &replacement, 1);
				replace_body(&mut changed.transport_sizing, name, &changed_body);
				assert!(
					validate(&changed).unwrap_err().contains("CBOR"),
					"{name} field {field}"
				);
				checked += 1;
			}
		}
	}
	let expected = CONTRACTS
		.iter()
		.find(|(name, _)| *name == "encoded_frame_len")
		.unwrap()
		.1;
	for (selected, substitute) in [
		(".integer(sequence)", ".integer(sender)"),
		(".integer(sender)", ".integer(sequence)"),
		(".bytes(ciphertext_length)", ".bytes(0)"),
	] {
		assert_eq!(expected.matches(selected).count(), 1);
		for replacement in ["", substitute] {
			let mut changed = original.clone();
			let changed_body = expected.replacen(selected, replacement, 1);
			replace_body(
				&mut changed.transport_sizing,
				"encoded_frame_len",
				&changed_body,
			);
			assert!(
				validate(&changed).unwrap_err().contains("CBOR"),
				"frame operand {selected}"
			);
			checked += 1;
		}
	}
	// Diverging Rust is well typed for every return type; the source guard must reject it.
	for (name, _) in CONTRACTS {
		let mut changed = original.clone();
		replace_body(
			&mut changed.transport_sizing,
			name,
			"panic!(\"transport bypass\")",
		);
		assert!(
			validate(&changed).unwrap_err().contains("CBOR"),
			"body bypass {name}"
		);
		checked += 1;
	}
	for (from, to) in [
		(
			"RegistrationApplication::Provided(bytes)=>bytes",
			"RegistrationApplication::Provided(_)=>&[]",
		),
		(
			"RegistrationApplication::Witness(bytes)=>bytes",
			"RegistrationApplication::Witness(_)=>&[0xff]",
		),
	] {
		assert_eq!(RENDER_BODY.matches(from).count(), 1);
		let mut changed = original.clone();
		let body = RENDER_BODY.replacen(from, to, 1);
		replace_body(
			&mut changed.adapter_server,
			"registration_application_bytes",
			&body,
		);
		assert!(validate(&changed).unwrap_err().contains("CBOR"));
		checked += 1;
	}
	let mut changed = original.clone();
	replace_body(
		&mut changed.adapter_server,
		"registration_application_bytes",
		"panic!(\"view bypass\")",
	);
	assert!(validate(&changed).unwrap_err().contains("CBOR"));
	checked += 1;
	for (function, from, to) in [
		(
			"registration_response_fits",
			"registration_application_bytes(&application).len()",
			"0",
		),
		(
			"build_registration_response",
			"letplaintext=registration_application_bytes(&application);",
			"letplaintext=&[];",
		),
	] {
		let mut changed = original.clone();
		let body = rust_body(&changed.adapter_server, function).unwrap();
		assert_eq!(body.matches(from).count(), 1);
		let body = body.replacen(from, to, 1);
		replace_body(&mut changed.adapter_server, function, &body);
		assert!(validate(&changed).unwrap_err().contains("CBOR"));
		checked += 1;
	}
	assert_eq!(checked, TRANSPORT_MUTATION_COUNT);
}

const TRANSPORT_MUTATION_COUNT: usize = 61;

fn replace_body(source: &mut String, name: &str, body: &str) {
	let marker = format!("fn {name}");
	let mut search_start = 0;
	let start = loop {
		let start = search_start + source[search_start..].find(&marker).unwrap();
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
	let open = start + source[start..].find('{').unwrap();
	let mut depth = 1usize;
	let mut end = open + 1;
	while depth > 0 {
		match source.as_bytes()[end] {
			b'{' => depth += 1,
			b'}' => depth -= 1,
			_ => {}
		}
		end += 1;
	}
	source.replace_range(open + 1..end - 1, body);
}
