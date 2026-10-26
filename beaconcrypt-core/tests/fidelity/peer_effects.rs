// SPDX-License-Identifier: 0BSD

//! Exact peer ownership and collection interpreter handoffs. Collection correctness remains external.

use super::{Snapshot, compact, rust_body, uncommented_rust};

fn source<'a>(snapshot: &'a Snapshot, name: &str) -> &'a str {
	match name {
		"peer" => &snapshot.core_peer,
		"shared" => &snapshot.adapter_shared,
		"server" => &snapshot.adapter_server,
		_ => panic!("unknown peer source {name}"),
	}
}

// Every row fixes source-selected operands and one-use continuation ownership.
const BODIES: &[(&str, &str, &str, &str)] = &[
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"from_trusted_parts",
		"Self{binding,ratchet}",
	),
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"key_id",
		"self.binding.assigned_key_id()",
	),
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"binding",
		"&self.binding",
	),
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"ratchet",
		"&self.ratchet",
	),
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"ratchet_mut",
		"&mutself.ratchet",
	),
	(
		"peer",
		"impl<Ratchet> Peer<Ratchet>",
		"into_parts",
		"(self.binding,self.ratchet)",
	),
	(
		"peer",
		"",
		"begin_registration_lookup",
		"RegistrationLookup{control,authenticated,}",
	),
	(
		"peer",
		"impl RegistrationLookup",
		"request",
		"self.authenticated.registration_id()",
	),
	(
		"peer",
		"impl RegistrationLookup",
		"resume",
		"ifconsumed{returnAgreementEffect::Rejected(None);}agreement::begin_server_agreement(self.control,pqxdh::RegistrationStatus::Fresh,self.authenticated,)",
	),
	(
		"peer",
		"",
		"begin_registration_insert",
		"RegistrationInsert{agreement}",
	),
	(
		"peer",
		"impl RegistrationInsert",
		"request",
		"self.agreement.registration_id()",
	),
	(
		"peer",
		"impl RegistrationInsert",
		"resume",
		"if!inserted{returnNone;}Some(ConsumedRegistration{agreement:self.agreement,})",
	),
	(
		"peer",
		"",
		"begin_completion_lookup",
		"letkey_id=matchpqxdh::server_next_key_id(control){Ok(key_id)=>key_id,Err(_)=>returnErr(control),};Ok(CompletionLookup{control,pin,registration,application,key_id,})",
	),
	(
		"peer",
		"impl<'a> CompletionLookup<'a>",
		"request",
		"self.key_id",
	),
	(
		"peer",
		"impl<'a> CompletionLookup<'a>",
		"resume",
		"letavailability=ifoccupied{pqxdh::KeyIdAvailability::Occupied}else{pqxdh::KeyIdAvailability::Available};registration::begin_server_completion(self.control,&self.pin,availability,self.registration.agreement,self.application,)",
	),
	(
		"peer",
		"",
		"begin_peer_insert",
		"letkey_id=matchpqxdh::server_next_key_id(control){Ok(key_id)=>key_id,Err(_)=>returnErr(control),};let(next,binding,kernel,encoded)=published.into_parts();ifnext.last_key_id()!=key_id{returnErr(control);}Ok(PeerInsert{previous:control,next,peer:Peer::from_trusted_parts(binding,kernel),encoded,})",
	),
	(
		"peer",
		"impl<Encoded> PeerInsert<Encoded>",
		"request",
		"self.peer.key_id()",
	),
	(
		"peer",
		"impl<Encoded> PeerInsert<Encoded>",
		"into_parts",
		"letkey_id=self.peer.key_id();(self.peer,PublicationFinish{previous:self.previous,next:self.next,key_id,encoded:self.encoded,},)",
	),
	(
		"peer",
		"impl<Encoded> PublicationFinish<Encoded>",
		"finish",
		"if!inserted{returnErr(self.previous);}Ok(PublishedPeer{control:self.next,key_id:self.key_id,encoded:self.encoded,})",
	),
	(
		"peer",
		"impl<Encoded> PublishedPeer<Encoded>",
		"into_parts",
		"(self.control,self.key_id,self.encoded)",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"new",
		"Self{pk,peer:beaconcrypt_core::peer::Peer::from_trusted_parts(binding,ratchet),}",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"from_peer",
		"Self{pk,peer:map_peer_ratchet(peer),}",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"mldsa_public_key_hash",
		"self.peer.binding().beacon_fingerprint()",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"binding",
		"self.peer.binding()",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"ratchet",
		"self.peer.ratchet()",
	),
	(
		"shared",
		"impl<PkType: SignaturePk> EstablishedRemote<PkType>",
		"ratchet_mut",
		"self.peer.ratchet_mut()",
	),
	(
		"shared",
		"",
		"map_peer_ratchet",
		"let(binding,kernel)=peer.into_parts();beaconcrypt_core::peer::Peer::from_trusted_parts(binding,RatchetManager::from_kernel(kernel))",
	),
	(
		"server",
		"impl ProviderServer for Server",
		"get_shared_secret",
		"letlookup=beaconcrypt_core::peer::begin_registration_lookup(control,authenticated);letregistration_id=*lookup.request().as_bytes();letconsumed=self.consumed_registrations.contains(&registration_id);leteffect=lookup.resume(consumed);ifmatches!(effect,AgreementEffect::Rejected(_)){returnNone;}self.consumed_registrations.try_reserve(1).ok()?;",
	),
	(
		"server",
		"impl ProviderServer for Server",
		"get_shared_secret",
		"letpending=beaconcrypt_core::peer::begin_registration_insert(agreement);letinserted=self.consumed_registrations.insert(*pending.request().as_bytes());letregistration=pending.resume(inserted)?;Some(RegistrationOutput{registration})",
	),
	(
		"server",
		"impl ProviderServer for Server",
		"build_registration_response",
		"letpending=beaconcrypt_core::peer::begin_peer_insert(control,ready.publish(buffer).ok()?).ok()?;letremote_kid=pending.request();let(peer,finish)=pending.into_parts();letpublic_key=crypto_sign::PublicKey::from_bytes(peer.binding().beacon_identity_public_key()).ok()?;letinserted=matchself.known_ids.entry(remote_kid){std::collections::hash_map::Entry::Vacant(entry)=>{entry.insert(EstablishedRemote::from_peer(public_key,peer));true}std::collections::hash_map::Entry::Occupied(_)=>false,};let(next_control,remote_kid,buffer)=finish.finish(inserted).ok()?.into_parts();self.control=next_control;Some(RegResponse{serialized:buffer,kid:remote_kid,})",
	),
];

fn selected_body(
	snapshot: &Snapshot,
	name: &str,
	scope: &str,
	function: &str,
) -> Result<String, String> {
	let raw = source(snapshot, name);
	let raw = raw
		.split_once(scope)
		.ok_or_else(|| format!("missing peer scope {scope}"))?
		.1;
	rust_body(raw, function)
}

pub(super) fn validate(snapshot: &Snapshot) -> Result<(), String> {
	for &(name, scope, function, expected) in BODIES {
		let actual = selected_body(snapshot, name, scope, function)?;
		let exact = if name == "server" {
			actual.matches(expected).count() == 1
		} else {
			actual == expected
		};
		if !exact {
			return Err(format!(
				"peer effects exact source binding changed: {name}::{scope}::{function}"
			));
		}
	}
	for &(name, declaration) in DECLARATIONS {
		let raw = compact(&uncommented_rust(source(snapshot, name))?);
		if raw.matches(declaration).count() != 1 {
			return Err(format!(
				"peer effects private ownership declaration changed: {declaration}"
			));
		}
	}
	let raw = compact(&uncommented_rust(&snapshot.core_peer)?);
	if raw.contains("usealloc::")
		|| raw.contains("usestd::")
		|| raw.contains("#[derive(Clone")
		|| raw.contains("#[derive(Copy")
	{
		return Err("peer effects one-use allocation-free boundary changed".into());
	}
	Ok(())
}

const DECLARATIONS: &[(&str, &str)] = &[
	(
		"peer",
		"pubstructPeer<Ratchet>{binding:SessionBinding,ratchet:Ratchet,}",
	),
	(
		"peer",
		"pubstructRegistrationLookup{control:ServerState,authenticated:AuthenticatedInit,}",
	),
	(
		"peer",
		"pubstructRegistrationInsert{agreement:ServerAgreement,}",
	),
	(
		"peer",
		"pubstructConsumedRegistration{agreement:ServerAgreement,}",
	),
	(
		"peer",
		"pubstructCompletionLookup<'a>{control:ServerState,pin:ServerAuthenticationPin,registration:ConsumedRegistration,application:&'a[u8],key_id:u64,}",
	),
	(
		"peer",
		"pubstructPeerInsert<Encoded>{previous:ServerState,next:ServerState,peer:Peer<ConcreteRatchetKernel>,encoded:Encoded,}",
	),
	(
		"peer",
		"pubstructPublicationFinish<Encoded>{previous:ServerState,next:ServerState,key_id:u64,encoded:Encoded,}",
	),
	(
		"peer",
		"pubstructPublishedPeer<Encoded>{control:ServerState,key_id:u64,encoded:Encoded,}",
	),
	(
		"shared",
		"pubstructEstablishedRemote<PkType:SignaturePk>{pk:PkType,peer:beaconcrypt_core::peer::Peer<RatchetManager>,}",
	),
	(
		"server",
		"pubstructRegistrationOutput{registration:beaconcrypt_core::peer::ConsumedRegistration,}",
	),
];

fn replace_once(snapshot: &mut Snapshot, name: &str, scope: &str, from: &str, to: &str) {
	let raw = match name {
		"peer" => &mut snapshot.core_peer,
		"shared" => &mut snapshot.adapter_shared,
		"server" => &mut snapshot.adapter_server,
		_ => panic!("unknown peer mutation source {name}"),
	};
	*raw = uncommented_rust(raw).unwrap();
	let scope = raw.find(scope).expect("peer mutation scope");
	let positions: Vec<_> = raw[scope..]
		.char_indices()
		.filter(|(_, c)| !c.is_whitespace())
		.map(|(i, _)| scope + i)
		.collect();
	let flat = compact(&raw[scope..]);
	let start = flat.find(from).expect("peer mutation operand");
	raw.replace_range(positions[start]..positions[start + from.len() - 1] + 1, to);
}

#[test]
fn peer_controller_and_interpreter_omission_duplication_and_bypass_are_rejected() {
	let baseline = Snapshot::production();
	validate(&baseline).unwrap();
	let mut checked = 0;
	for &(name, scope, function, expected) in BODIES {
		for replacement in [
			String::new(),
			format!("{expected}{expected}"),
			"panic!(\"peer bypass\")".to_owned(),
		] {
			let mut changed = baseline.clone();
			replace_once(&mut changed, name, scope, expected, &replacement);
			assert!(
				validate(&changed).is_err(),
				"peer control survived {name}::{scope}::{function}"
			);
			checked += 1;
		}
	}
	assert_eq!(checked, 90);
}

#[test]
fn peer_tokens_and_stored_metadata_cannot_expose_mutable_public_fields() {
	let baseline = Snapshot::production();
	validate(&baseline).unwrap();
	let mut checked = 0;
	for &(name, declaration) in DECLARATIONS {
		let start = declaration.find('{').unwrap() + 1;
		let altered = format!("{}pub {}", &declaration[..start], &declaration[start..]);
		let mut changed = baseline.clone();
		replace_once(&mut changed, name, "", declaration, &altered);
		assert!(
			validate(&changed).is_err(),
			"peer field became public: {declaration}"
		);
		checked += 1;
	}
	assert_eq!(checked, 10);
	for prefix in [
		"#[derive(Clone)]",
		"#[derive(Copy)]",
		"use alloc::vec::Vec;",
		"use std::collections::HashMap;",
	] {
		let mut changed = baseline.clone();
		changed.core_peer.insert_str(0, prefix);
		assert!(
			validate(&changed).is_err(),
			"peer ownership escape survived: {prefix}"
		);
	}
}
