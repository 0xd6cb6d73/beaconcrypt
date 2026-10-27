// SPDX-License-Identifier: 0BSD

//! Exact production record-controller/primitive wiring, reviewed across the extracted core and native interpreters.
//! Ordinary and registration traffic share these continuations. Primitive honesty remains external.

use super::{Snapshot, compact, rust_body, uncommented_rust};

fn source<'a>(snapshot: &'a Snapshot, name: &str) -> &'a str {
	match name {
		"records" => &snapshot.core_record_effects,
		"registration" => &snapshot.core_registration,
		"ratchet" => &snapshot.adapter_ratchet,
		"beacon" => &snapshot.adapter_beacon,
		"server" => &snapshot.adapter_server,
		_ => panic!("unknown record source {name}"),
	}
}

// Each readable body fixes operands, failure branches, order and affine continuation provenance.
const BODIES: &[(&str, &str, &str, &str, &str, &str, &str)] = &[
	(
		"records",
		"impl<'a> SealFrameContext<'a>",
		"new",
		"",
		"",
		"Self{plaintext,prefix:None,associated_data:*associated_data,target_kid,sender_kid,encoding,}",
		"records::impl<'a> SealFrameContext<'a>::new",
	),
	(
		"records",
		"impl<'a> SealFrameContext<'a>",
		"registration",
		"",
		"",
		"letprefix=*crate::pqxdh::registration_key_id_binding(assigned_kid).as_bytes();Self{plaintext:application,prefix:Some(prefix),associated_data:*associated_data,target_kid:assigned_kid,sender_kid,encoding:RecordEncoding::Raw,}",
		"records::impl<'a> SealFrameContext<'a>::registration",
	),
	(
		"records",
		"impl<'a> SealFrameContext<'a>",
		"plaintext_request",
		"",
		"",
		"match&self.prefix{Some(prefix)=>SealPlaintextRequest::Prefixed{prefix,application:self.plaintext,},None=>SealPlaintextRequest::Single(self.plaintext),}",
		"records::impl<'a> SealFrameContext<'a>::plaintext_request",
	),
	(
		"records",
		"",
		"begin_record_send",
		"",
		"",
		"ifcontext.plaintext.is_empty()&&context.prefix.is_none(){returnRecordSendStart::Rejected(kernel);}matchbegin_send(kernel,context){SendStart::SendExhausted{kernel,..}=>RecordSendStart::Rejected(kernel),SendStart::SendKdfRequested(pending)=>{RecordSendStart::KdfRequested(RecordSendKdf{pending})}}",
		"records::begin_record_send",
	),
	(
		"records",
		"impl<'a> RecordSendKdf<'a>",
		"request",
		"",
		"",
		"self.pending.request()",
		"records::impl<'a> RecordSendKdf<'a>::request",
	),
	(
		"records",
		"impl<'a> RecordSendKdf<'a>",
		"cancel",
		"",
		"",
		"self.pending.cancel().0",
		"records::impl<'a> RecordSendKdf<'a>::cancel",
	),
	(
		"records",
		"impl<'a> RecordSendKdf<'a>",
		"resume",
		"",
		"",
		"SealAead{seal:self.pending.resume(response),}",
		"records::impl<'a> RecordSendKdf<'a>::resume",
	),
	(
		"records",
		"",
		"reject_send",
		"",
		"",
		"pending.finish(None)",
		"records::reject_send",
	),
	(
		"records",
		"impl<'a> SealAead<'a>",
		"request",
		"",
		"",
		"letmaterial=self.seal.material();letcontext=self.seal.context();AeadSealRequest{key:material.key().as_bytes(),nonce:material.nonce().as_bytes(),associated_data:&context.associated_data,plaintext:context.plaintext_request(),}",
		"records::impl<'a> SealAead<'a>::request",
	),
	(
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"",
		"",
		"letSome((ciphertext,tag))=detachedelse{returnSealAfterAead::Rejected(reject_send(self.seal).0);};letmaterial=self.seal.material();letcontext=self.seal.context();lettranscript=build_commitment_transcript(material.key().as_bytes(),material.nonce().as_bytes(),&context.associated_data,&tag,self.seal.sequence(),context.sender_kid,);SealAfterAead::CommitmentRequested(SealCommitment{seal:self.seal,ciphertext,tag,transcript,})",
		"records::impl<'a> SealAead<'a>::resume",
	),
	(
		"records",
		"impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>",
		"transcript",
		"",
		"",
		"&self.transcript",
		"records::impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>::transcript",
	),
	(
		"records",
		"impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>",
		"transcript_mut",
		"",
		"",
		"&mutself.transcript",
		"records::impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>::transcript_mut",
	),
	(
		"records",
		"impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>",
		"resume",
		"",
		"",
		"letSome(commitment)=commitmentelse{returnSealAfterCommitment::Rejected(reject_send(self.seal).0);};SealAfterCommitment::WriteRequested(SealWrite{seal:self.seal,ciphertext:self.ciphertext,tag:self.tag,commitment,})",
		"records::impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext>::resume",
	),
	(
		"records",
		"impl SealWrite<'_, '_>",
		"request",
		"",
		"",
		"letparts=[self.ciphertext,self.tag.as_slice(),self.commitment.as_slice(),];matchself.seal.context().encoding{RecordEncoding::Raw=>RecordWriteRequest::Raw{parts},RecordEncoding::Frame=>RecordWriteRequest::Frame{parts,sequence:self.seal.sequence(),sender:self.seal.context().sender_kid,},}",
		"records::impl SealWrite<'_, '_>::request",
	),
	(
		"records",
		"impl SealWrite<'_, '_>",
		"finish",
		"",
		"",
		"letciphertext=matchwritten{Some(ciphertext)=>ciphertext,None=>returnself.seal.finish(None),};letkey_id=self.seal.context().target_kid;letseq=self.seal.sequence();letoutput=SealedRecord{ciphertext,key_id,seq,};self.seal.finish(Some(output))",
		"records::impl SealWrite<'_, '_>::finish",
	),
	(
		"records",
		"",
		"begin_record_receive",
		"",
		"",
		"letSome(context)=OpenFrameContext::from_frame(ciphertext,associated_data,sender)else{returnRecordReceiveEffect::Rejected(kernel);};normalize_receive(begin_receive(kernel,sequence,context))",
		"records::begin_record_receive",
	),
	(
		"records",
		"",
		"normalize_receive",
		"",
		"",
		"matcheffect{ReceiveEffect::ReceiveRejected{kernel,..}=>RecordReceiveEffect::Rejected(kernel),ReceiveEffect::ReceiveKdfRequested(pending)=>{RecordReceiveEffect::KdfRequested(RecordReceiveKdf{pending})}ReceiveEffect::ReceiveOpenRequested(opening)=>matchbegin_open(opening){OpenStart::OpenRejected(kernel)=>RecordReceiveEffect::Rejected(kernel),OpenStart::OpenCommitmentRequested(pending)=>{RecordReceiveEffect::CommitmentRequested(RecordReceiveCommitment{pending})}},}",
		"records::normalize_receive",
	),
	(
		"records",
		"impl<'a> RecordReceiveKdf<'a>",
		"request",
		"",
		"",
		"self.pending.request()",
		"records::impl<'a> RecordReceiveKdf<'a>::request",
	),
	(
		"records",
		"impl<'a> RecordReceiveKdf<'a>",
		"cancel",
		"",
		"",
		"self.pending.cancel().0",
		"records::impl<'a> RecordReceiveKdf<'a>::cancel",
	),
	(
		"records",
		"impl<'a> RecordReceiveKdf<'a>",
		"resume",
		"",
		"",
		"normalize_receive(self.pending.resume(response))",
		"records::impl<'a> RecordReceiveKdf<'a>::resume",
	),
	(
		"records",
		"impl<'a> RecordReceiveCommitment<'a>",
		"transcript",
		"",
		"",
		"self.pending.transcript()",
		"records::impl<'a> RecordReceiveCommitment<'a>::transcript",
	),
	(
		"records",
		"impl<'a> RecordReceiveCommitment<'a>",
		"transcript_mut",
		"",
		"",
		"&mutself.pending.transcript",
		"records::impl<'a> RecordReceiveCommitment<'a>::transcript_mut",
	),
	(
		"records",
		"impl<'a> RecordReceiveCommitment<'a>",
		"supplied_commitment",
		"",
		"",
		"self.pending.supplied_commitment()",
		"records::impl<'a> RecordReceiveCommitment<'a>::supplied_commitment",
	),
	(
		"records",
		"impl<'a> RecordReceiveCommitment<'a>",
		"resume",
		"",
		"",
		"matchself.pending.resume(commitment_matches){OpenAfterCommitment::OpenCommitmentRejected(kernel)=>{RecordReceiveEffect::Rejected(kernel)}OpenAfterCommitment::OpenAeadRequested(pending)=>{RecordReceiveEffect::AeadRequested(RecordReceiveAead{pending})}}",
		"records::impl<'a> RecordReceiveCommitment<'a>::resume",
	),
	(
		"records",
		"impl RecordReceiveAead<'_>",
		"request",
		"",
		"",
		"self.pending.request()",
		"records::impl RecordReceiveAead<'_>::request",
	),
	(
		"records",
		"impl RecordReceiveAead<'_>",
		"finish",
		"",
		"",
		"self.pending.finish(plaintext)",
		"records::impl RecordReceiveAead<'_>::finish",
	),
	(
		"registration",
		"impl<'a> BeaconInitialKdf<'a>",
		"resume",
		"",
		"",
		"letresponse=matchresponse{Some(response)=>response,None=>{returnErr(crate::pqxdh::beacon_abort_candidate(self.agreement.candidate,));}};letkernel=crate::pqxdh::resume_initial_ratchet_kdf(self.pending,response);leteffect=records::begin_record_receive(kernel,1,self.agreement.application_ciphertext,self.agreement.binding.associated_data(),self.agreement.candidate.server_key_id(),);normalize_beacon_open(self.agreement,effect)",
		"registration::impl<'a> BeaconInitialKdf<'a>::resume",
	),
	(
		"registration",
		"",
		"normalize_beacon_open",
		"",
		"",
		"matcheffect{records::RecordReceiveEffect::Rejected(_)=>{Err(crate::pqxdh::beacon_abort_candidate(agreement.candidate))}records::RecordReceiveEffect::KdfRequested(pending)=>{Ok(BeaconInitialOpen::KdfRequested(BeaconRecordKdf{agreement,pending,}))}records::RecordReceiveEffect::CommitmentRequested(pending)=>Ok(BeaconInitialOpen::CommitmentRequested(BeaconRecordCommitment{agreement,pending}),),records::RecordReceiveEffect::AeadRequested(pending)=>{Ok(BeaconInitialOpen::AeadRequested(BeaconRecordAead{agreement,pending,}))}}",
		"registration::normalize_beacon_open",
	),
	(
		"registration",
		"impl<'a> BeaconRecordKdf<'a>",
		"request",
		"",
		"",
		"self.pending.request()",
		"registration::impl<'a> BeaconRecordKdf<'a>::request",
	),
	(
		"registration",
		"impl<'a> BeaconRecordKdf<'a>",
		"resume",
		"",
		"",
		"letresponse=matchresponse{Some(response)=>response,None=>{returnErr(crate::pqxdh::beacon_abort_candidate(self.agreement.candidate,));}};normalize_beacon_open(self.agreement,self.pending.resume(response))",
		"registration::impl<'a> BeaconRecordKdf<'a>::resume",
	),
	(
		"registration",
		"impl<'a> BeaconRecordCommitment<'a>",
		"transcript",
		"",
		"",
		"self.pending.transcript()",
		"registration::impl<'a> BeaconRecordCommitment<'a>::transcript",
	),
	(
		"registration",
		"impl<'a> BeaconRecordCommitment<'a>",
		"transcript_mut",
		"",
		"",
		"&mutself.pending.pending.transcript",
		"registration::impl<'a> BeaconRecordCommitment<'a>::transcript_mut",
	),
	(
		"registration",
		"impl<'a> BeaconRecordCommitment<'a>",
		"supplied_commitment",
		"",
		"",
		"self.pending.supplied_commitment()",
		"registration::impl<'a> BeaconRecordCommitment<'a>::supplied_commitment",
	),
	(
		"registration",
		"impl<'a> BeaconRecordCommitment<'a>",
		"resume",
		"",
		"",
		"normalize_beacon_open(self.agreement,self.pending.resume(commitment_matches))",
		"registration::impl<'a> BeaconRecordCommitment<'a>::resume",
	),
	(
		"registration",
		"impl BeaconRecordAead<'_>",
		"request",
		"",
		"",
		"self.pending.request()",
		"registration::impl BeaconRecordAead<'_>::request",
	),
	(
		"registration",
		"impl BeaconRecordAead<'_>",
		"finish",
		"",
		"",
		"letrejected=crate::pqxdh::BeaconAborted::new(self.agreement.candidate.server_key_id());let(kernel,opened)=self.pending.finish(plaintext);letopened=matchopened{Some(opened)=>opened,None=>returnErr(rejected),};ifopened.plaintext.len()<=crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE{returnErr(rejected);}let(prefix,application)=opened.plaintext.split_at(crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE);letprefix=matchprefix.try_into(){Ok(prefix)=>prefix,Err(_)=>returnErr(rejected),};letauthenticated=matchcrate::pqxdh::authenticate_registration_key_id_binding(self.agreement.candidate,opened.key_id,prefix,){Ok(authenticated)=>authenticated,Err(_)=>returnErr(rejected),};letbinding=self.agreement.binding.finish(authenticated.assigned_key_id());Ok(CompletedBeacon{control:crate::pqxdh::beacon_commit(authenticated),binding,kernel,application,})",
		"registration::impl BeaconRecordAead<'_>::finish",
	),
	(
		"registration",
		"impl<'a> ServerInitialKdf<'a>",
		"resume",
		"",
		"",
		"letrejected=crate::pqxdh::server_abort_candidate(&self.candidate);letresponse=matchresponse{Some(response)=>response,None=>returnErr(rejected),};letkernel=crate::pqxdh::resume_initial_ratchet_kdf(self.pending,response);letcontext=records::SealFrameContext::registration(self.application,self.candidate.key_id(),self.candidate.server_identity_key_id(),self.binding.associated_data(),);letpending=matchrecords::begin_record_send(kernel,context){records::RecordSendStart::Rejected(_)=>returnErr(rejected),records::RecordSendStart::KdfRequested(pending)=>pending,};Ok(ServerInitialSeal{state:ServerRecordState{candidate:self.candidate,binding:self.binding,application:self.application,},pending,})",
		"registration::impl<'a> ServerInitialKdf<'a>::resume",
	),
	(
		"registration",
		"impl<'a> ServerInitialSeal<'a>",
		"request",
		"",
		"",
		"self.pending.request()",
		"registration::impl<'a> ServerInitialSeal<'a>::request",
	),
	(
		"registration",
		"impl<'a> ServerInitialSeal<'a>",
		"resume",
		"",
		"",
		"letresponse=matchresponse{Some(response)=>response,None=>returnErr(crate::pqxdh::server_abort_candidate(&self.state.candidate)),};Ok(ServerRecordAead{state:self.state,pending:self.pending.resume(response),})",
		"registration::impl<'a> ServerInitialSeal<'a>::resume",
	),
	(
		"registration",
		"impl<'a> ServerRecordAead<'a>",
		"request",
		"",
		"",
		"self.pending.request()",
		"registration::impl<'a> ServerRecordAead<'a>::request",
	),
	(
		"registration",
		"impl<'a> ServerRecordAead<'a>",
		"resume",
		"",
		"",
		"matchself.pending.resume(detached){records::SealAfterAead::Rejected(_)=>{Err(crate::pqxdh::server_abort_candidate(&self.state.candidate))}records::SealAfterAead::CommitmentRequested(pending)=>Ok(ServerRecordCommitment{state:self.state,pending,}),}",
		"registration::impl<'a> ServerRecordAead<'a>::resume",
	),
	(
		"registration",
		"impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>",
		"transcript",
		"",
		"",
		"self.pending.transcript()",
		"registration::impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>::transcript",
	),
	(
		"registration",
		"impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>",
		"transcript_mut",
		"",
		"",
		"&mutself.pending.transcript",
		"registration::impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>::transcript_mut",
	),
	(
		"registration",
		"impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>",
		"resume",
		"",
		"",
		"matchself.pending.resume(commitment){records::SealAfterCommitment::Rejected(_)=>{Err(crate::pqxdh::server_abort_candidate(&self.state.candidate))}records::SealAfterCommitment::WriteRequested(pending)=>Ok(ServerRecordWrite{state:self.state,pending,}),}",
		"registration::impl<'a, 'ciphertext> ServerRecordCommitment<'a, 'ciphertext>::resume",
	),
	(
		"registration",
		"impl ServerRecordWrite<'_, '_>",
		"request",
		"",
		"",
		"self.pending.request()",
		"registration::impl ServerRecordWrite<'_, '_>::request",
	),
	(
		"registration",
		"impl ServerRecordWrite<'_, '_>",
		"resume",
		"",
		"",
		"letrejected=crate::pqxdh::server_abort_candidate(&self.state.candidate);let(kernel,sealed)=self.pending.finish(ciphertext);letciphertext=matchsealed{Some(sealed)=>sealed.ciphertext,None=>returnErr(rejected),};letbound_length=match8usize.checked_add(self.state.application.len()){Some(length)=>length,None=>returnErr(rejected),};letlength=matchbound_length.checked_add(crate::record::MESSAGE_OVERHEAD){Some(length)=>length,None=>returnErr(rejected),};ifciphertext.len()!=length{returnErr(rejected);}letprefix=build_response_prefix(self.state.binding.init_hash(),self.state.candidate.server_identity_public_key(),self.state.candidate.ephemeral_public_key(),self.state.candidate.kem_ciphertext(),matchu64::try_from(ciphertext.len()){Ok(length)=>length,Err(_)=>returnErr(rejected),},);letassigned_id=encode_u64_le(self.state.candidate.key_id());Ok(ServerResponseHash{candidate:self.state.candidate,binding:self.state.binding,kernel,ciphertext,prefix,assigned_id,})",
		"registration::impl ServerRecordWrite<'_, '_>::resume",
	),
	(
		"ratchet",
		"",
		"execute_seal_request",
		"",
		"",
		"letkey:AeadKey=(*request.key).into();letnonce:AeadNonce=(*request.nonce).into();letprefixed=match&request.plaintext{records::SealPlaintextRequest::Single(_)=>None,records::SealPlaintextRequest::Prefixed{prefix,application,}=>Some(Zeroizing::new(join_record_parts([prefix.as_slice(),*application,])?)),};letplaintext=matchrequest.plaintext{records::SealPlaintextRequest::Single(plaintext)=>plaintext,records::SealPlaintextRequest::Prefixed{..}=>prefixed.as_ref()?.as_slice(),};let(ciphertext,tag)=crypto_aead::chacha20poly1305_ietf::encrypt_detached(plaintext,Some(request.associated_data.as_slice()),&nonce,&key,).ok()?;Some((ciphertext,tag.as_slice().try_into().ok()?))",
		"ratchet::execute_seal_request",
	),
	(
		"ratchet",
		"",
		"execute_commitment_hash",
		"",
		"",
		"letcommitment=crypto_generichash::generichash(transcript.as_bytes(),None,COMMITMENT_SIZE).ok();transcript.as_mut_bytes().zeroize();commitment?.as_slice().try_into().ok()",
		"ratchet::execute_commitment_hash",
	),
	(
		"ratchet",
		"",
		"join_record_parts",
		"",
		"",
		"letlength=parts.iter().try_fold(0usize,|length,part|length.checked_add(part.len()))?;letmutoutput=Vec::new();output.try_reserve_exact(length).ok()?;forpartinparts{output.extend_from_slice(part);}Some(output)",
		"ratchet::join_record_parts",
	),
	(
		"ratchet",
		"",
		"execute_write_request",
		"",
		"",
		"matchrequest{records::RecordWriteRequest::Raw{parts}=>join_record_parts(parts),records::RecordWriteRequest::Frame{parts,sequence,sender,}=>{letciphertext=join_record_parts(parts)?;crate::wire::encode_frame(CryptoFrame{cipher_text:&ciphertext,seq:sequence,key_id:sender,})}}",
		"ratchet::execute_write_request",
	),
	(
		"ratchet",
		"",
		"execute_open_request",
		"",
		"",
		"letrequest=request?;letkey:AeadKey=(*request.key).into();letnonce:AeadNonce=(*request.nonce).into();crypto_aead::chacha20poly1305_ietf::decrypt(request.ciphertext,Some(request.associated_data.as_slice()),&nonce,&key,).ok()",
		"ratchet::execute_open_request",
	),
	(
		"ratchet",
		"",
		"execute_record_send",
		"",
		"",
		"letpending=matchrecords::begin_record_send(kernel,context){records::RecordSendStart::Rejected(kernel)=>return(kernel,None),records::RecordSendStart::KdfRequested(pending)=>pending,};letresponse=ratchet_hkdf(pending.request());letaead=pending.resume(response);letdetached=execute_seal_request(aead.request());letdetached_view=detached.as_ref().map(|(body,tag)|(body.as_slice(),*tag));letmutcommitment=matchaead.resume(detached_view){records::SealAfterAead::Rejected(kernel)=>return(kernel,None),records::SealAfterAead::CommitmentRequested(pending)=>pending,};letdigest=execute_commitment_hash(commitment.transcript_mut());letwriter=matchcommitment.resume(digest){records::SealAfterCommitment::Rejected(kernel)=>return(kernel,None),records::SealAfterCommitment::WriteRequested(writer)=>writer,};letwritten=execute_write_request(writer.request());let(kernel,output)=writer.finish(written);(kernel,output.map(|sealed|Encrypted{ciphertext:sealed.ciphertext,key_id:sealed.key_id,seq:sealed.seq,}),)",
		"ratchet::execute_record_send",
	),
	(
		"ratchet",
		"",
		"execute_record_receive",
		"",
		"",
		"loop{effect=matcheffect{records::RecordReceiveEffect::Rejected(kernel)=>return(kernel,None),records::RecordReceiveEffect::KdfRequested(pending)=>{letresponse=ratchet_hkdf(pending.request());pending.resume(response)}records::RecordReceiveEffect::CommitmentRequested(mutpending)=>{letactual=execute_commitment_hash(pending.transcript_mut());letmatches=matchactual{Some(actual)=>memcmp(&actual,pending.supplied_commitment()),None=>false,};pending.resume(matches)}records::RecordReceiveEffect::AeadRequested(pending)=>{letplaintext=execute_open_request(pending.request());let(kernel,opened)=pending.finish(plaintext);return(kernel,opened.map(|opened|Decrypted{plaintext:opened.plaintext,key_id:opened.key_id,seq:opened.seq,}),);}};}",
		"ratchet::execute_record_receive",
	),
	(
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"",
		"",
		"leteffect=records::begin_record_receive(ratchet.refined.take(),key_seq,ciphertext,associated_data,kid,);let(kernel,opened)=execute_record_receive(effect);ratchet.refined.put(kernel);opened",
		"ratchet::decrypt_payload_with_ratchet",
	),
	(
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"letencoding=",
		"",
		"letencoding=ifframe_encoding{records::RecordEncoding::Frame}else{records::RecordEncoding::Raw};letcontext=records::SealFrameContext::new(bytes,target_kid,sender_kid,associated_data,encoding);let(kernel,sealed)=execute_record_send(ratchet.refined.take(),context);ratchet.refined.put(kernel);sealed",
		"ratchet::encrypt_with_ratchet",
	),
	(
		"beacon",
		"",
		"finish_registration",
		"letpending=registration::begin_beacon_completion(agreement);",
		"",
		"letpending=registration::begin_beacon_completion(agreement);letresponse=verified_pqxdh::InitialRatchetKdfResponse::from_bytes(crate::ratchet::initial_ratchet_hkdf(pending.request()),);letmuteffect=matchpending.resume(Some(response)){Ok(effect)=>effect,Err(control)=>{self.state=BeaconState::Aborted{control};returnNone;}};loop{letnext=matcheffect{registration::BeaconInitialOpen::KdfRequested(pending)=>{letresponse=crate::ratchet::ratchet_hkdf(pending.request());pending.resume(Some(response))}registration::BeaconInitialOpen::CommitmentRequested(mutpending)=>{letcommitment=crate::ratchet::execute_commitment_hash(pending.transcript_mut());letmatches=matchcommitment{Some(commitment)=>beaconcrypt_crypto::utils::memcmp(&commitment,pending.supplied_commitment(),),None=>false,};pending.resume(matches)}registration::BeaconInitialOpen::AeadRequested(pending)=>{letplaintext=crate::ratchet::execute_open_request(pending.request());letcompleted=matchpending.finish(plaintext.as_deref()){Ok(completed)=>completed,Err(control)=>{self.state=BeaconState::Aborted{control};returnNone;}};let(control,binding,kernel,application)=completed.into_parts();letplaintext=application.to_vec();self.identity_key_kid=binding.assigned_key_id();self.state=BeaconState::Established{control,binding,ratchet:RatchetManager::from_kernel(kernel),};returnSome(plaintext);}};effect=matchnext{Ok(effect)=>effect,Err(control)=>{self.state=BeaconState::Aborted{control};returnNone;}};}",
		"beacon::finish_registration",
	),
	(
		"server",
		"",
		"build_registration_response",
		"letresponse=verified_pqxdh::InitialRatchetKdfResponse::from_bytes(",
		"lethash=auth::execute_hash(",
		"letresponse=verified_pqxdh::InitialRatchetKdfResponse::from_bytes(crate::ratchet::initial_ratchet_hkdf(pending.request()),);letpending=pending.resume(Some(response)).ok()?;letresponse=crate::ratchet::ratchet_hkdf(pending.request());letpending=pending.resume(Some(response)).ok()?;letdetached=crate::ratchet::execute_seal_request(pending.request());letdetached_view=detached.as_ref().map(|(body,tag)|(body.as_slice(),*tag));letmutpending=pending.resume(detached_view).ok()?;letcommitment=crate::ratchet::execute_commitment_hash(pending.transcript_mut());letpending=pending.resume(commitment).ok()?;letciphertext=crate::ratchet::execute_write_request(pending.request());letpending=pending.resume(ciphertext.as_deref()).ok()?;",
		"server::build_registration_response",
	),
	(
		"ratchet",
		"",
		"decrypt_message_with_ratchet",
		"",
		"",
		"ifdata.is_empty(){returnNone;}letframe=decode_crypto_frame(data)?;letadmitted=beaconcrypt_core::transport::admit_frame(frame.seq,frame.key_id,frame.cipher_text,expected_sender_kid,)?;decrypt_payload_with_ratchet(admitted.ciphertext,admitted.sequence,admitted.sender,associated_data,ratchet,)",
		"ratchet::decrypt_message_with_ratchet",
	),
];

fn selected_body(
	snapshot: &Snapshot,
	source_name: &str,
	scope: &str,
	function: &str,
	start: &str,
	end: &str,
) -> Result<String, String> {
	let raw = source(snapshot, source_name);
	let raw = if scope.is_empty() {
		raw
	} else {
		raw.split_once(scope)
			.ok_or_else(|| format!("missing record scope {scope}"))?
			.1
	};
	let mut body = rust_body(raw, function)?;
	if !start.is_empty() {
		body = body
			.split_once(start)
			.ok_or_else(|| format!("missing record start {start}"))?
			.1
			.to_owned();
		body.insert_str(0, start);
	}
	if !end.is_empty() {
		body = body
			.split_once(end)
			.ok_or_else(|| format!("missing record end {end}"))?
			.0
			.to_owned();
	}
	Ok(body)
}

pub(super) fn validate(snapshot: &Snapshot) -> Result<(), String> {
	for &(name, scope, function, start, end, expected, label) in BODIES {
		let actual = selected_body(snapshot, name, scope, function, start, end)?;
		if actual != expected {
			return Err(format!(
				"record effects exact production binding changed: {label}"
			));
		}
	}
	let core = compact(&uncommented_rust(&snapshot.core_record_effects)?);
	for declaration in DECLARATIONS {
		if core.matches(declaration).count() != 1 {
			return Err(format!(
				"record effects affine request declaration changed: {declaration}"
			));
		}
	}
	if core.contains("take_kernel") || core.contains("usealloc::") || core.contains("usestd::") {
		return Err("record effects affine allocation-free boundary changed".into());
	}
	Ok(())
}

const DECLARATIONS: &[&str] = &[
	"pubstructSealFrameContext<'a>{plaintext:&'a[u8],prefix:Option<[u8;8]>,associated_data:[u8;ASSOCIATED_DATA_SIZE],target_kid:u64,sender_kid:u64,encoding:RecordEncoding,}",
	"pubstructRecordSendKdf<'a>{pending:SendKdf<SealFrameContext<'a>>,}",
	"pubenumSealPlaintextRequest<'a>{Single(&'a[u8]),Prefixed{prefix:&'a[u8;8],application:&'a[u8],},}",
	"pubstructAeadSealRequest<'a>{pubkey:&'a[u8;AEAD_KEY_SIZE],pubnonce:&'a[u8;AEAD_NONCE_SIZE],pubassociated_data:&'a[u8;ASSOCIATED_DATA_SIZE],pubplaintext:SealPlaintextRequest<'a>,}",
	"pubstructSealAead<'a>{seal:SendSeal<SealFrameContext<'a>>,}",
	"pubstructSealCommitment<'a,'ciphertext>{seal:SendSeal<SealFrameContext<'a>>,ciphertext:&'ciphertext[u8],tag:[u8;AEAD_TAG_SIZE],pub(crate)transcript:CommitmentTranscript,}",
	"pubenumRecordWriteRequest<'a>{Raw{parts:[&'a[u8];3],},Frame{parts:[&'a[u8];3],sequence:u64,sender:u64,},}",
	"pubstructSealWrite<'a,'ciphertext>{seal:SendSeal<SealFrameContext<'a>>,ciphertext:&'ciphertext[u8],tag:[u8;AEAD_TAG_SIZE],commitment:[u8;COMMITMENT_SIZE],}",
	"pubstructRecordReceiveKdf<'a>{pending:ReceiveKdf<OpenFrameContext<'a>>,}",
	"pubstructRecordReceiveCommitment<'a>{pub(crate)pending:OpenCommitment<'a>,}",
	"pubstructRecordReceiveAead<'a>{pending:OpenAead<'a>,}",
];

#[test]
fn exact_record_controller_bodies_and_private_requests_are_required() {
	let baseline = Snapshot::production();
	validate(&baseline).unwrap();
	let mut checked = 0;
	for &(name, scope, function, _, _, expected, label) in BODIES {
		for replacement in [
			"panic!(\"record body bypass\")",
			"return panic!(\"record early return\");",
		] {
			let mut changed = baseline.clone();
			super::registration_effects::replace_contract(
				&mut changed,
				name,
				scope,
				function,
				expected,
				replacement,
			);
			assert!(
				validate(&changed).is_err(),
				"record body bypass survived {label}"
			);
			checked += 1;
		}
	}
	assert_eq!(checked, BODY_MUTATION_COUNT);
}

fn change_declaration(snapshot: &mut Snapshot, declaration: &str, from: &str, to: &str) {
	let source = &mut snapshot.core_record_effects;
	*source = uncommented_rust(source).unwrap();
	let positions: Vec<_> = source
		.char_indices()
		.filter(|(_, c)| !c.is_whitespace())
		.map(|(i, _)| i)
		.collect();
	let flat = compact(source);
	let start = flat.find(declaration).expect("record declaration");
	let offset = start + declaration.find(from).expect("record declaration field");
	source.replace_range(
		positions[offset]..positions[offset + from.len() - 1] + 1,
		to,
	);
}

#[test]
fn record_request_privacy_and_part_types_cannot_be_weakened() {
	let baseline = Snapshot::production();
	validate(&baseline).unwrap();
	let mut checked = 0;
	for declaration in DECLARATIONS {
		let (from, to) = if declaration.contains("pub(crate)pending:") {
			("pub(crate)pending:", "pub pending:")
		} else if declaration.contains("pending:") {
			("pending:", "pub pending:")
		} else if declaration.contains("seal:") {
			("seal:", "pub seal:")
		} else if declaration.contains("plaintext:") {
			("plaintext:", "pub plaintext:")
		} else if declaration.contains("Single(&'a[u8])") {
			("Single(&'a[u8])", "Single(&'static [u8])")
		} else if declaration.contains("parts:[&'a[u8];3]") {
			("parts:[&'a[u8];3]", "parts: [&'a [u8];2]")
		} else {
			(
				"pubnonce:&'a[u8;AEAD_NONCE_SIZE]",
				"pub nonce: &'a [u8;AEAD_KEY_SIZE]",
			)
		};
		let mut changed = baseline.clone();
		change_declaration(&mut changed, declaration, from, to);
		let error = validate(&changed).unwrap_err();
		assert!(
			error.contains("affine request declaration"),
			"record declaration mutation: {error}"
		);
		checked += 1;
	}
	assert_eq!(checked, DECLARATION_MUTATION_COUNT);
}

const BODY_MUTATION_COUNT: usize = 116;
const DECLARATION_MUTATION_COUNT: usize = 11;

// Each old production-record mutation keeps its identity and failure/operand intent at the actual new owner.
const MIGRATED: &[(&str, &str, &str, &str, &str, &str, &str)] = &[
	(
		"later_registration_adapter_kernel_substituted",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.take()",
		"replacement_kernel",
		"record effects",
	),
	(
		"later_registration_adapter_request_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"ratchet_hkdf(pending.request())",
		"ratchet_hkdf(replacement_request)",
		"record effects",
	),
	(
		"later_registration_adapter_pending_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.resume(response)",
		"replacement_pending.resume(response)",
		"record effects",
	),
	(
		"later_registration_adapter_finish_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.finish(plaintext)",
		"pending.finish(replacement_opened)",
		"record effects",
	),
	(
		"later_registration_adapter_result_sequence_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"seq:opened.seq,",
		"seq:1,",
		"record effects",
	),
	(
		"later_registration_adapter_begin_kernel_substituted",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.take()",
		"replacement_kernel",
		"record effects",
	),
	(
		"later_registration_adapter_begin_sequence_substituted",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.take(),key_seq,",
		"ratchet.refined.take(),key_seq.wrapping_add(1),",
		"record effects",
	),
	(
		"later_registration_adapter_begin_context_substituted",
		"records",
		"",
		"begin_record_receive",
		"normalize_receive(begin_receive(kernel,sequence,context))",
		"normalize_receive(begin_receive(kernel,sequence,OpenFrameContext::from_frame(ciphertext,associated_data,0).unwrap()))",
		"record effects",
	),
	(
		"cbor_seal_payload",
		"ratchet",
		"",
		"execute_write_request",
		"cipher_text:&ciphertext,",
		"cipher_text:&[],",
		"record effects",
	),
	(
		"cbor_seal_sequence",
		"ratchet",
		"",
		"execute_write_request",
		"seq:sequence,",
		"seq:sequence.wrapping_add(1),",
		"record effects",
	),
	(
		"cbor_seal_sender",
		"ratchet",
		"",
		"execute_write_request",
		"key_id:sender,",
		"key_id:0,",
		"record effects",
	),
	(
		"cbor_seal_raw_branch",
		"records",
		"impl<'a> SealFrameContext<'a>",
		"registration",
		"encoding:RecordEncoding::Raw,",
		"encoding:RecordEncoding::Frame,",
		"record effects",
	),
	(
		"cbor_registration_implicit_sequence",
		"registration",
		"impl<'a> BeaconInitialKdf<'a>",
		"resume",
		"records::begin_record_receive(kernel,1,",
		"records::begin_record_receive(kernel,2,",
		"registration core implicit sequence",
	),
	(
		"cbor_registration_pinned_sender",
		"registration",
		"impl<'a> BeaconInitialKdf<'a>",
		"resume",
		"self.agreement.candidate.server_key_id()",
		"0",
		"registration core implicit sequence",
	),
	(
		"cryptoframe_open_uses_zero_key",
		"ratchet",
		"",
		"execute_open_request",
		"letkey:AeadKey=(*request.key).into();",
		"letkey:AeadKey=[0u8;AEAD_KEY_LEN].into();",
		"record effects",
	),
	(
		"cryptoframe_open_uses_zero_nonce",
		"ratchet",
		"",
		"execute_open_request",
		"letnonce:AeadNonce=(*request.nonce).into();",
		"letnonce:AeadNonce=[0u8;AEAD_NONCE_LEN].into();",
		"record effects",
	),
	(
		"cryptoframe_open_commitment_slice_starts_late",
		"ratchet",
		"",
		"execute_record_receive",
		"memcmp(&actual,pending.supplied_commitment())",
		"memcmp(&actual,&pending.supplied_commitment()[1..])",
		"record effects",
	),
	(
		"cryptoframe_open_commitment_slice_ends_early",
		"ratchet",
		"",
		"execute_record_receive",
		"memcmp(&actual,pending.supplied_commitment())",
		"memcmp(&actual,&pending.supplied_commitment()[..COMMITMENT_SIZE-1])",
		"record effects",
	),
	(
		"cryptoframe_open_decrypts_ciphertext_without_tag",
		"ratchet",
		"",
		"execute_open_request",
		"request.ciphertext,",
		"&request.ciphertext[..request.ciphertext.len()-AEAD_TAG_LEN],",
		"record effects",
	),
	(
		"cryptoframe_open_decrypts_commitment_too",
		"ratchet",
		"",
		"execute_open_request",
		"request.ciphertext,",
		"pending.supplied_commitment(),",
		"record effects",
	),
	(
		"cryptoframe_open_decrypt_prefix_boundary_late",
		"ratchet",
		"",
		"execute_open_request",
		"request.ciphertext,",
		"&request.ciphertext[..request.ciphertext.len()+1],",
		"record effects",
	),
	(
		"cryptoframe_open_omits_associated_data",
		"ratchet",
		"",
		"execute_open_request",
		"Some(request.associated_data.as_slice()),",
		"None,",
		"record effects",
	),
	(
		"cryptoframe_commitment_extracts_zero_key",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"material.key().as_bytes()",
		"&[0;AEAD_KEY_SIZE]",
		"record effects",
	),
	(
		"cryptoframe_commitment_extracts_zero_nonce",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"material.nonce().as_bytes()",
		"&[0;AEAD_NONCE_SIZE]",
		"record effects",
	),
	(
		"cryptoframe_commitment_converts_tag_as_ad",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"&context.associated_data",
		"&[0;ASSOCIATED_DATA_SIZE]",
		"record effects",
	),
	(
		"cryptoframe_commitment_uses_ad_prefix_as_tag",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"&tag,",
		"&[0;AEAD_TAG_SIZE],",
		"record effects",
	),
	(
		"cryptoframe_commitment_core_call_swaps_sequence_sender",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"self.seal.sequence(),context.sender_kid,",
		"context.sender_kid,self.seal.sequence(),",
		"record effects",
	),
	(
		"cryptoframe_commitment_hash_output_shortened",
		"ratchet",
		"",
		"execute_commitment_hash",
		"generichash(transcript.as_bytes(),None,COMMITMENT_SIZE)",
		"generichash(transcript.as_bytes(),None,COMMITMENT_SIZE-1)",
		"record effects",
	),
	(
		"cryptoframe_executor_shadows_plaintext",
		"ratchet",
		"",
		"execute_record_receive",
		"let(kernel,opened)=pending.finish(plaintext);",
		"letplaintext=Some(vec![0]);let(kernel,opened)=pending.finish(plaintext);",
		"record effects",
	),
	(
		"cryptoframe_executor_accepts_claimed_plaintext",
		"ratchet",
		"",
		"execute_open_request",
		".ok()",
		".ok().or_else(||Some(vec![0]))",
		"record effects",
	),
	(
		"ratchet_driver_send_context_swaps_target_and_sender",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"records::SealFrameContext::new(bytes,target_kid,sender_kid,associated_data,encoding)",
		"records::SealFrameContext::new(bytes,sender_kid,target_kid,associated_data,encoding)",
		"record effects",
	),
	(
		"ratchet_driver_send_context_replaces_plaintext",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"records::SealFrameContext::new(bytes,target_kid,sender_kid,associated_data,encoding)",
		"records::SealFrameContext::new(&[],target_kid,sender_kid,associated_data,encoding)",
		"record effects",
	),
	(
		"ratchet_driver_send_context_replaces_associated_data",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"records::SealFrameContext::new(bytes,target_kid,sender_kid,associated_data,encoding)",
		"records::SealFrameContext::new(bytes,target_kid,sender_kid,&[0;AD_SIZE],encoding)",
		"record effects",
	),
	(
		"ratchet_driver_send_duplicates_kernel_take",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"ratchet.refined.take()",
		"{letkernel=ratchet.refined.take();ratchet.refined.put(kernel);ratchet.refined.take()}",
		"CBOR size precheck before ratchet",
	),
	(
		"ratchet_driver_send_omits_begin",
		"ratchet",
		"",
		"execute_record_send",
		"records::begin_record_send(kernel,context)",
		"panic!(\"beginsendomitted\")",
		"record effects",
	),
	(
		"ratchet_driver_send_begins_with_rebuilt_context",
		"ratchet",
		"",
		"execute_record_send",
		"records::begin_record_send(kernel,context)",
		"records::begin_record_send(kernel,records::SealFrameContext::new(&[1],0,0,&[0;AD_SIZE],records::RecordEncoding::Frame))",
		"record effects",
	),
	(
		"ratchet_driver_send_exhaustion_drops_kernel",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"ratchet.refined.put(kernel);sealed",
		"drop(kernel);sealed",
		"record effects",
	),
	(
		"ratchet_driver_send_exhaustion_puts_after_return",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"ratchet.refined.put(kernel);sealed",
		"returnsealed;ratchet.refined.put(kernel);",
		"record effects",
	),
	(
		"ratchet_driver_send_uses_fixed_request",
		"ratchet",
		"",
		"execute_record_send",
		"ratchet_hkdf(pending.request())",
		"ratchet_hkdf(&verified_ratchet::SymmetricRatchetKdfRequest::new([0;KDF_STATE_SIZE]))",
		"record effects",
	),
	(
		"ratchet_driver_send_omits_request_interpretation",
		"ratchet",
		"",
		"execute_record_send",
		"letresponse=ratchet_hkdf(pending.request());",
		"letresponse=verified_ratchet::RatchetKdfResponse::from_bytes([0;verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]);",
		"record effects",
	),
	(
		"ratchet_driver_send_resumes_with_wrong_response",
		"ratchet",
		"",
		"execute_record_send",
		"pending.resume(response)",
		"pending.resume(verified_ratchet::RatchetKdfResponse::from_bytes([0;verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]))",
		"record effects",
	),
	(
		"ratchet_driver_send_resumes_different_pending",
		"ratchet",
		"",
		"execute_record_send",
		"pending.resume(response)",
		"unsafe{std::hint::unreachable_unchecked()}.resume(response)",
		"record effects",
	),
	(
		"ratchet_driver_send_omits_pending_resume",
		"ratchet",
		"",
		"execute_record_send",
		"letaead=pending.resume(response);",
		"letaead=panic!(\"pendingresumeomitted\");",
		"record effects",
	),
	(
		"ratchet_driver_send_seals_with_wrong_material",
		"records",
		"impl<'a> SealAead<'a>",
		"request",
		"key:material.key().as_bytes(),",
		"key:&[0;AEAD_KEY_SIZE],",
		"record effects",
	),
	(
		"ratchet_driver_send_seals_with_wrong_sequence",
		"records",
		"impl<'a> SealAead<'a>",
		"resume",
		"self.seal.sequence(),",
		"self.seal.sequence().wrapping_add(1),",
		"record effects",
	),
	(
		"ratchet_driver_send_seals_with_rebuilt_context",
		"records",
		"impl<'a> SealAead<'a>",
		"request",
		"associated_data:&context.associated_data,",
		"associated_data:&[0;ASSOCIATED_DATA_SIZE],",
		"record effects",
	),
	(
		"ratchet_driver_send_omits_seal",
		"ratchet",
		"",
		"execute_record_send",
		"letdetached=execute_seal_request(aead.request());",
		"letdetached:Option<(Vec<u8>,[u8;AEAD_TAG_LEN])>=None;",
		"record effects",
	),
	(
		"ratchet_driver_send_finishes_with_none",
		"ratchet",
		"",
		"execute_record_send",
		"writer.finish(written)",
		"writer.finish(None)",
		"record effects",
	),
	(
		"ratchet_driver_send_omits_finish",
		"ratchet",
		"",
		"execute_record_send",
		"let(kernel,output)=writer.finish(written);",
		"let(kernel,output)=panic!(\"finishomitted\");",
		"record effects",
	),
	(
		"ratchet_driver_send_drops_finished_kernel",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"ratchet.refined.put(kernel);sealed",
		"drop(kernel);sealed",
		"record effects",
	),
	(
		"ratchet_driver_send_returns_before_put",
		"ratchet",
		"",
		"encrypt_with_ratchet",
		"ratchet.refined.put(kernel);sealed",
		"returnsealed;ratchet.refined.put(kernel);",
		"record effects",
	),
	(
		"ratchet_driver_receive_context_uses_expected_sender",
		"records",
		"",
		"begin_record_receive",
		"OpenFrameContext::from_frame(ciphertext,associated_data,sender)",
		"OpenFrameContext::from_frame(ciphertext,associated_data,0)",
		"record effects",
	),
	(
		"ratchet_driver_receive_context_replaces_ciphertext",
		"records",
		"",
		"begin_record_receive",
		"OpenFrameContext::from_frame(ciphertext,associated_data,sender)",
		"OpenFrameContext::from_frame(&[],associated_data,sender)",
		"record effects",
	),
	(
		"ratchet_driver_receive_context_replaces_associated_data",
		"records",
		"",
		"begin_record_receive",
		"OpenFrameContext::from_frame(ciphertext,associated_data,sender)",
		"OpenFrameContext::from_frame(ciphertext,&[0;ASSOCIATED_DATA_SIZE],sender)",
		"record effects",
	),
	(
		"ratchet_driver_receive_duplicates_kernel_take",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.take()",
		"{letkernel=ratchet.refined.take();ratchet.refined.put(kernel);ratchet.refined.take()}",
		"record effects",
	),
	(
		"ratchet_driver_receive_begins_with_wrong_sequence",
		"records",
		"",
		"begin_record_receive",
		"begin_receive(kernel,sequence,context)",
		"begin_receive(kernel,sequence.wrapping_add(1),context)",
		"record effects",
	),
	(
		"ratchet_driver_receive_begins_with_rebuilt_context",
		"records",
		"",
		"begin_record_receive",
		"normalize_receive(begin_receive(kernel,sequence,context))",
		"normalize_receive(begin_receive(kernel,sequence,OpenFrameContext::from_frame(ciphertext,associated_data,0).unwrap()))",
		"record effects",
	),
	(
		"ratchet_driver_receive_rejected_drops_kernel",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.put(kernel);opened",
		"drop(kernel);opened",
		"record effects",
	),
	(
		"ratchet_driver_receive_rejected_puts_after_return",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.put(kernel);opened",
		"returnopened;ratchet.refined.put(kernel);",
		"record effects",
	),
	(
		"ratchet_driver_receive_fixes_loop_iteration_count",
		"ratchet",
		"",
		"execute_record_receive",
		"loop{effect=matcheffect{",
		"letmutremaining_iterations=1usize;loop{ifremaining_iterations==0{returnNone;}remaining_iterations-=1;effect=matcheffect{",
		"record effects",
	),
	(
		"ratchet_driver_receive_uses_fixed_kdf_request",
		"ratchet",
		"",
		"execute_record_receive",
		"ratchet_hkdf(pending.request())",
		"ratchet_hkdf(&verified_ratchet::SymmetricRatchetKdfRequest::new([0;KDF_STATE_SIZE]))",
		"record effects",
	),
	(
		"ratchet_driver_receive_omits_kdf_request",
		"ratchet",
		"",
		"execute_record_receive",
		"letresponse=ratchet_hkdf(pending.request());",
		"letresponse=verified_ratchet::RatchetKdfResponse::from_bytes([0;verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]);",
		"record effects",
	),
	(
		"ratchet_driver_receive_resumes_with_wrong_response",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.resume(response)",
		"pending.resume(verified_ratchet::RatchetKdfResponse::from_bytes([0;verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]))",
		"record effects",
	),
	(
		"ratchet_driver_receive_resumes_different_pending",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.resume(response)",
		"unsafe{std::hint::unreachable_unchecked()}.resume(response)",
		"record effects",
	),
	(
		"ratchet_driver_receive_omits_pending_resume",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.resume(response)",
		"panic!(\"pendingresumeomitted\")",
		"record effects",
	),
	(
		"ratchet_driver_receive_kdf_publishes_slot",
		"ratchet",
		"",
		"execute_record_receive",
		"letresponse=ratchet_hkdf(pending.request());",
		"ratchet.refined.put(panic!(\"prematurepublication\"));letresponse=ratchet_hkdf(pending.request());",
		"record effects",
	),
	(
		"ratchet_driver_receive_no_material_drops_kernel",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.put(kernel);opened",
		"drop(kernel);opened",
		"record effects",
	),
	(
		"ratchet_driver_receive_no_material_puts_after_return",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.put(kernel);opened",
		"returnopened;ratchet.refined.put(kernel);",
		"record effects",
	),
	(
		"ratchet_driver_receive_opens_with_wrong_material",
		"ratchet",
		"",
		"execute_open_request",
		"letkey:AeadKey=(*request.key).into();",
		"letkey:AeadKey=[0;AEAD_KEY_LEN].into();",
		"record effects",
	),
	(
		"ratchet_driver_receive_omits_open",
		"ratchet",
		"",
		"execute_record_receive",
		"execute_open_request(pending.request())",
		"None::<Vec<u8>>",
		"record effects",
	),
	(
		"ratchet_driver_receive_finishes_with_none",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.finish(plaintext)",
		"pending.finish(None::<Vec<u8>>)",
		"record effects",
	),
	(
		"ratchet_driver_receive_omits_finish",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.finish(plaintext)",
		"panic!(\"openfinishomitted\")",
		"record effects",
	),
	(
		"ratchet_driver_receive_drops_finished_kernel",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"ratchet.refined.put(kernel);opened",
		"drop(kernel);opened",
		"record effects",
	),
	(
		"ratchet_driver_receive_questions_result_before_put",
		"ratchet",
		"",
		"decrypt_payload_with_ratchet",
		"let(kernel,opened)=execute_record_receive(effect);ratchet.refined.put(kernel);opened",
		"let(kernel,opened)=execute_record_receive(effect);letopened=opened?;ratchet.refined.put(kernel);Some(opened)",
		"record effects",
	),
	(
		"ratchet_driver_receive_returns_expected_sender_metadata",
		"ratchet",
		"",
		"execute_record_receive",
		"key_id:opened.key_id,",
		"key_id:expected_sender_kid,",
		"record effects",
	),
	(
		"ratchet_driver_receive_returns_wrong_sequence_metadata",
		"ratchet",
		"",
		"execute_record_receive",
		"seq:opened.seq,",
		"seq:opened.seq.wrapping_add(1),",
		"record effects",
	),
	(
		"ratchet_driver_receive_moves_sender_gate_after_take",
		"ratchet",
		"",
		"decrypt_message_with_ratchet",
		"letadmitted=beaconcrypt_core::transport::admit_frame(frame.seq,frame.key_id,frame.cipher_text,expected_sender_kid,)?;decrypt_payload_with_ratchet(admitted.ciphertext,admitted.sequence,admitted.sender,associated_data,ratchet,)",
		"letopened=decrypt_payload_with_ratchet(frame.cipher_text,frame.seq,frame.key_id,associated_data,ratchet)?;let_admitted=beaconcrypt_core::transport::admit_frame(frame.seq,frame.key_id,frame.cipher_text,expected_sender_kid,)?;Some(opened)",
		"record effects",
	),
	(
		"ratchet_driver_receive_moves_length_gate_after_take",
		"records",
		"",
		"begin_record_receive",
		"letSome(context)=OpenFrameContext::from_frame(ciphertext,associated_data,sender)else{returnRecordReceiveEffect::Rejected(kernel);};normalize_receive(begin_receive(kernel,sequence,context))",
		"normalize_receive(begin_receive(kernel,sequence,OpenFrameContext::from_frame(ciphertext,associated_data,sender).unwrap()))",
		"record effects",
	),
	(
		"native_hash_failure_short_circuits",
		"ratchet",
		"",
		"execute_commitment_hash",
		"letcommitment=crypto_generichash::generichash(transcript.as_bytes(),None,COMMITMENT_SIZE).ok();transcript.as_mut_bytes().zeroize();commitment?.as_slice().try_into().ok()",
		"letcommitment=crypto_generichash::generichash(transcript.as_bytes(),None,COMMITMENT_SIZE).ok()?;transcript.as_mut_bytes().zeroize();commitment.as_slice().try_into().ok()",
		"record effects",
	),
	(
		"native_hash_uses_wrong_transcript",
		"ratchet",
		"",
		"execute_commitment_hash",
		"generichash(transcript.as_bytes(),None,COMMITMENT_SIZE)",
		"generichash(&[0;229],None,COMMITMENT_SIZE)",
		"record effects",
	),
	(
		"native_hash_omits_erase",
		"ratchet",
		"",
		"execute_commitment_hash",
		"transcript.as_mut_bytes().zeroize();",
		"",
		"record effects",
	),
	(
		"native_hash_none_passes",
		"ratchet",
		"",
		"execute_record_receive",
		"None=>false,",
		"None=>true,",
		"record effects",
	),
	(
		"native_compare_result_ignored",
		"ratchet",
		"",
		"execute_record_receive",
		"Some(actual)=>memcmp(&actual,pending.supplied_commitment()),",
		"Some(actual)=>true,",
		"record effects",
	),
	(
		"native_resume_forced_true",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.resume(matches)",
		"pending.resume(true)",
		"record effects",
	),
	(
		"native_rejected_commitment_drops_kernel",
		"ratchet",
		"",
		"execute_record_receive",
		"RecordReceiveEffect::Rejected(kernel)=>return(kernel,None)",
		"RecordReceiveEffect::Rejected(kernel)=>return(RatchetKernel::new(verified_ratchet::RatchetChain::from_bytes([0;32]),verified_ratchet::RatchetChain::from_bytes([0;32])),None)",
		"record effects",
	),
	(
		"native_aead_request_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"execute_open_request(pending.request())",
		"execute_open_request(None)",
		"record effects",
	),
	(
		"native_optional_plaintext_substituted",
		"ratchet",
		"",
		"execute_record_receive",
		"pending.finish(plaintext)",
		"pending.finish(Some(vec![0]))",
		"record effects",
	),
];

#[test]
fn every_moved_record_operand_failure_and_bypass_control_is_rejected() {
	let baseline = Snapshot::production();
	super::validate(&baseline).unwrap();
	let mut checked = 0;
	for &(name, source, scope, function, from, to, diagnostic) in MIGRATED {
		let mut changed = baseline.clone();
		super::registration_effects::replace_contract(
			&mut changed,
			source,
			scope,
			function,
			from,
			to,
		);
		let error = super::validate(&changed).unwrap_err();
		assert!(
			error.contains(diagnostic),
			"moved record control {name}: {error}"
		);
		checked += 1;
	}
	assert_eq!(checked, MIGRATED_CONTROL_COUNT);
}

const MIGRATED_CONTROL_COUNT: usize = 87;
