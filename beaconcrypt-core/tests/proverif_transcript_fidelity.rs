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
	ConcreteRatchetKernel, RATCHET_KDF_OUTPUT_SIZE, RatchetChain, RatchetKdfResponse,
	ReceiveEffect, SYM_RATCHET_INFO, SendStart, begin_receive, begin_send,
	split_ratchet_kdf_output,
};

const INTERFACE: &str = include_str!("../proofs/pro-verif/production-transcript-interface.pvl");
const CRYPTO_MODEL: &str = include_str!("../proofs/pro-verif/crypto.pvl");
const ENVIRONMENT_MODEL: &str = include_str!("../proofs/pro-verif/environment.pvl");
const ACTIVE_QUANTUM_WITNESS: &str = include_str!("../proofs/pro-verif/active-quantum-witness.pvl");
const EXTRACTION_MODEL: &str = include_str!("../proofs/pro-verif/extraction/lib.pvl");
const MLKEM_REENCAPSULATION_CONTROL: &str =
	include_str!("../proofs/pro-verif/mlkem-reencapsulation-control.pvl");
const CORE_MAKEFILE: &str = include_str!("../Makefile");
const FORMAL_WORKFLOW: &str = include_str!("../../.github/workflows/formal-verification.yml");
const ADAPTER_PQXDH: &str = include_str!("../../beaconcrypt/src/pqxdh.rs");
const ADAPTER_RATCHET: &str = include_str!("../../beaconcrypt/src/ratchet.rs");
const ADAPTER_SHARED: &str = include_str!("../../beaconcrypt/src/shared.rs");
const ADAPTER_SERVER: &str = include_str!("../../beaconcrypt/src/server.rs");
const ADAPTER_BEACON: &str = include_str!("../../beaconcrypt/src/beacon.rs");
const CORE_COMMITMENT: &str = include_str!("../src/commitment.rs");
const CORE_PQXDH: &str = include_str!("../src/pqxdh.rs");
const CORE_PQXDH_CONCRETE: &str = include_str!("../src/pqxdh/concrete.rs");
const CORE_RATCHET: &str = include_str!("../src/ratchet.rs");
const CORE_RATCHET_CONCRETE: &str = include_str!("../src/ratchet/concrete.rs");
const CORE_RATCHET_CONTROL: &str = include_str!("../src/ratchet/control.rs");
const CORE_RATCHET_REFINED: &str = include_str!("../src/ratchet/refined.rs");
const LEAN_RATCHET_EFFECT: &str =
	include_str!("../proofs/lean/BeaconcryptCore/Refinement/RatchetEffect.lean");
const LEAN_RATCHET_EFFECT_REFINEMENT: &str =
	include_str!("../proofs/lean/BeaconcryptCore/Refinement/RatchetEffectRefinement.lean");
const LEAN_PQXDH_KDF: &str = include_str!("../proofs/lean/BeaconcryptCore/Model/Pqxdh/Kdf.lean");
const LEAN_PQXDH_THEOREMS: &str =
	include_str!("../proofs/lean/BeaconcryptCore/Model/Pqxdh/Theorems.lean");
const CRYPTOFRAME_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/cryptoframe.capnp");
const PHASE1_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/phase1.capnp");
const PHASE2_SCHEMA: &str = include_str!("../../beaconcrypt/src/schema/phase2.capnp");
const FAILED_RECEIVE_QUERIES: &str = include_str!("../proofs/pro-verif/failed-receive-queries.pvl");
const FAILED_RECEIVE_REACHABILITY_QUERIES: &str =
	include_str!("../proofs/pro-verif/failed-receive-reachability-queries.pvl");
const LATER_REGISTRATION_CONTROL: &str =
	include_str!("../proofs/pro-verif/later-sequence-registration-control.pvl");
const LATER_REGISTRATION_QUERIES: &str =
	include_str!("../proofs/pro-verif/later-sequence-registration-queries.pvl");
const LATER_REGISTRATION_MAIN: &str =
	include_str!("../proofs/pro-verif/later-sequence-registration.pv");
const PROVERIF_RESULT_CHECKER: &str = include_str!("../proofs/pro-verif/check-results.awk");
const LEAN_RATCHET_CONTROL: &str =
	include_str!("../proofs/lean/BeaconcryptCore/Refinement/RatchetControl.lean");
const LEAN_RATCHET_REFINEMENT: &str =
	include_str!("../proofs/lean/BeaconcryptCore/Refinement/RatchetRefinement.lean");

const FACT_PREFIX: &str = "(* @beaconcrypt-fidelity-v1 ";
const FACT_SUFFIX: &str = " *)";
const LATER_REGISTRATION_QUERY_HASHES: [u64; 18] = [
	17_193_186_413_467_823_408,
	9_977_621_451_872_089_083,
	1_859_662_740_831_841_734,
	6_185_069_684_262_088_586,
	1_202_361_603_546_247_583,
	3_455_186_719_080_634_235,
	676_668_089_077_458_887,
	14_740_752_099_764_896_718,
	2_295_576_426_332_104_103,
	11_236_771_169_740_860_269,
	1_026_471_539_442_063_085,
	4_537_599_263_751_259_124,
	1_360_721_314_336_953_706,
	4_484_615_328_937_149_544,
	17_363_979_669_924_787_267,
	15_927_833_979_560_930_765,
	7_422_622_837_596_238_938,
	4_051_337_733_113_411_667,
];
const LATER_REGISTRATION_CHECKER_HASH: u64 = 6_902_455_048_869_219_859;
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
	"endpoint.server.send.target=peer_key_id",
	"endpoint.server.send.sender=local_identity_key_id",
	"endpoint.server.send.associated_data=server_identity,peer_identity",
	"endpoint.server.send.ratchet=peer_key_id",
	"endpoint.server.receive.sender_source=parsed_wire_key_id",
	"endpoint.server.receive.lookup_id.trust=untrusted_before_open",
	"endpoint.server.receive.peer_lookup=parsed_wire_key_id",
	"endpoint.server.receive.associated_data=server_identity,selected_peer_identity",
	"endpoint.server.receive.ratchet=parsed_wire_key_id",
	"endpoint.server.receive.expected_sender=parsed_wire_key_id",
	"endpoint.server.receive.acceptance_control=open_returns_some",
	"endpoint.server.receive.order=parsed_sender,peer_associated_data,peer_ratchet,open,accept",
	"endpoint.server.established.associated_data=recomputed_server_identity,stored_selected_peer_identity",
	"endpoint.beacon.send.target=control.server_key_id",
	"endpoint.beacon.send.sender=assigned_identity_key_id",
	"endpoint.beacon.send.associated_data=stored_establishment",
	"endpoint.beacon.send.ratchet=single_established",
	"endpoint.beacon.receive.expected_sender=control.server_key_id",
	"endpoint.beacon.receive.associated_data=stored_establishment",
	"endpoint.beacon.receive.ratchet=single_established",
	"endpoint.registration.server.initial.target=assigned_remote_key_id",
	"endpoint.registration.server.initial.sender=candidate.server_identity_key_id",
	"endpoint.registration.server.initial.associated_data=candidate.associated_data",
	"endpoint.registration.server.initial.ratchet=candidate_initial",
	"endpoint.registration.server.initial.returned_target_metadata=assigned_remote_key_id",
	"endpoint.registration.server.commit.peer_map=assigned_remote_key_id,peer_identity,candidate_ratchet_after_initial_send",
	"endpoint.registration.server.order=initial_seal,serialize_response,commit_candidate,insert_peer,publish_control,return",
	"endpoint.registration.beacon.initial.expected_sender=candidate.server_key_id",
	"endpoint.registration.beacon.initial.associated_data=candidate.associated_data",
	"endpoint.registration.beacon.initial.ratchet=candidate_initial",
	"endpoint.registration.beacon.commit.associated_data=same_candidate_value",
	"endpoint.registration.beacon.commit.ratchet=candidate_ratchet_after_successful_initial_open",
	"endpoint.registration.beacon.commit.local_sender=authenticated_assigned_key_id",
	"endpoint.registration.beacon.order=initial_open,key_id_binding_authentication,pinned_server_id,pinned_server_identity,assign_local_id,store_established",
	"endpoint.symbolic.main_honest.server_to_beacon.sender=SERVER_KEY_ID",
	"endpoint.symbolic.main_honest.server_to_beacon.event_receiver=assigned_key_id",
	"endpoint.symbolic.main_honest.beacon_to_server.sender=assigned_key_id",
	"endpoint.symbolic.main_honest.beacon_to_server.event_receiver=SERVER_KEY_ID",
	"endpoint.symbolic.main_honest.associated_data=server_identity,beacon_identity",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.server_open.count=4",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.server_open.calls=server_material_1,associated_data,first_sequence(),SERVER_KEY_ID,initial_frame;server_material_3,associated_data,next_sequence(next_sequence(first_sequence())),SERVER_KEY_ID,third_frame;server_material_2,associated_data,next_sequence(first_sequence()),SERVER_KEY_ID,second_frame;ratchet_material(ratchet_next(server_chain_3)),associated_data,next_sequence(next_sequence(next_sequence(first_sequence()))),SERVER_KEY_ID,fourth_frame",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.beacon_seal.count=1",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.beacon_seal.calls=beacon_material_1,associated_data,first_sequence(),assigned_key_id,beacon_record_secret",
	"endpoint.symbolic.main_honest.fixture.server.server_seal.count=4",
	"endpoint.symbolic.main_honest.fixture.server.server_seal.calls=server_material_1,associated_data,first_sequence(),SERVER_KEY_ID,registration_payload(binding,initial_secret);server_material_2,associated_data,next_sequence(first_sequence()),SERVER_KEY_ID,cached_secret;server_material_3,associated_data,next_sequence(next_sequence(first_sequence())),SERVER_KEY_ID,advance_secret;server_material_4,associated_data,next_sequence(next_sequence(next_sequence(first_sequence()))),SERVER_KEY_ID,future_secret",
	"endpoint.symbolic.main_honest.fixture.server.beacon_open.count=1",
	"endpoint.symbolic.main_honest.fixture.server.beacon_open.calls=beacon_material_1,associated_data,first_sequence(),assigned_key_id,beacon_frame",
	"endpoint.symbolic.main_honest.fixture.events.fields=session,direction,sequence,sender,event_receiver,plaintext",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.received_events.calls=session,server_to_beacon(),first_sequence(),SERVER_KEY_ID,assigned_key_id,initial_plaintext;session,server_to_beacon(),next_sequence(next_sequence(first_sequence())),SERVER_KEY_ID,assigned_key_id,third_plaintext;session,server_to_beacon(),next_sequence(first_sequence()),SERVER_KEY_ID,assigned_key_id,second_plaintext;session,server_to_beacon(),next_sequence(next_sequence(next_sequence(first_sequence()))),SERVER_KEY_ID,assigned_key_id,fourth_plaintext",
	"endpoint.symbolic.main_honest.fixture.honest_beacon.sent_events.calls=session,beacon_to_server(),first_sequence(),assigned_key_id,SERVER_KEY_ID,beacon_record_secret",
	"endpoint.symbolic.main_honest.fixture.server.sent_events.calls=session,server_to_beacon(),first_sequence(),SERVER_KEY_ID,assigned_key_id,initial_secret;session,server_to_beacon(),next_sequence(first_sequence()),SERVER_KEY_ID,assigned_key_id,cached_secret;session,server_to_beacon(),next_sequence(next_sequence(first_sequence())),SERVER_KEY_ID,assigned_key_id,advance_secret;session,server_to_beacon(),next_sequence(next_sequence(next_sequence(first_sequence()))),SERVER_KEY_ID,assigned_key_id,future_secret",
	"endpoint.symbolic.main_honest.fixture.server.received_events.calls=session,beacon_to_server(),first_sequence(),assigned_key_id,SERVER_KEY_ID,beacon_plaintext",
	"endpoint.symbolic.malicious_registration.initial.sender=SERVER_KEY_ID",
	"endpoint.symbolic.malicious_registration.associated_data=server_identity,beacon_identity",
	"endpoint.symbolic.malicious_registration.fixture.initial_seal.count=1",
	"endpoint.symbolic.malicious_registration.fixture.initial_seal.calls=server_material_1,associated_data,first_sequence(),SERVER_KEY_ID,registration_payload(binding,MALICIOUS_TASK_SECRET)",
	"ratchet.driver.kind=synchronous_affine_interpreter",
	"ratchet.driver.slot.take=Option::take:once_per_encrypt_or_decrypt_helper_after_prechecks",
	"ratchet.driver.slot.put=assert_empty_then_store_returned_kernel",
	"ratchet.driver.kdf.reply=ratchet_hkdf(SymmetricRatchetKdfRequest)->RatchetKdfResponse",
	"ratchet.driver.send.precheck=empty_input_rejected_before_take",
	"ratchet.driver.send.context=SealFrameContext(bytes,target_kid,sender_kid,associated_data)",
	"ratchet.driver.send.take=ratchet.refined.take():once",
	"ratchet.driver.send.begin=begin_send(kernel,same_context):once",
	"ratchet.driver.send.exhausted=put(returned_kernel),return_none",
	"ratchet.driver.send.kdf.request=ratchet_hkdf(same_pending.request()):once",
	"ratchet.driver.send.kdf.resume=same_pending.resume(same_response)",
	"ratchet.driver.send.seal=seal_frame(seal.material(),seal.sequence(),seal.context())",
	"ratchet.driver.send.finish=seal.finish(sealed)",
	"ratchet.driver.send.put=finish_returned_kernel_before_returned_sealed",
	"ratchet.driver.send.failure=seal.finish(None):advanced_kernel_then_slot_put",
	"ratchet.driver.send.cancel=not_invoked_in_encrypt_helper",
	"ratchet.driver.receive.prechecks=empty,typed_parse,sender_match,payload_length:before_take",
	"ratchet.driver.receive.context=OpenFrameContext(ciphertext,associated_data,parsed_sender)",
	"ratchet.driver.receive.take=ratchet.refined.take():once",
	"ratchet.driver.receive.begin=begin_receive(kernel,parsed_sequence,same_context):once",
	"ratchet.driver.receive.loop=effect_match_without_fixed_iteration_count",
	"ratchet.driver.receive.rejected=put(returned_kernel),return_none",
	"ratchet.driver.receive.kdf.request=ratchet_hkdf(same_pending.request()):per_arm",
	"ratchet.driver.receive.kdf.resume=same_pending.resume(same_response)",
	"ratchet.driver.receive.kdf.slot_put=none_in_ReceiveKdfRequested_arm",
	"ratchet.driver.receive.no_material=open.reject(),put(returned_kernel),return_none",
	"ratchet.driver.receive.open=open_frame(material,open.sequence(),open.context())",
	"ratchet.driver.receive.finish=open.finish(opened)",
	"ratchet.driver.receive.put=finish_returned_kernel_before_opened_question",
	"ratchet.driver.receive.success=plaintext,parsed_sender,parsed_sequence",
	"ratchet.driver.receive.failure=open.finish(None):entry_kernel_then_slot_put",
	"ratchet.driver.receive.cancel=not_invoked_in_decrypt_helper",
	"ratchet.driver.core.phase_api=SendStart,SendKdf,SendSeal,ReceiveEffect,ReceiveKdf,ReceiveOpen",
	"ratchet.driver.core.receive.publication=staged_until_ReceiveOpen.finish(Some)",
	"ratchet.driver.lean.structural=begin_send_nonexhausted_exact,begin_send_exhausted_restores_entry,SendKdf.request_exact,SendKdf.resume_exact,SendSeal.finish_returns_interpreter_result,begin_receive_rejected_plan_restores_entry,begin_receive_cached_exact,begin_receive_future_request_exact,ReceiveKdf.request_exact,ReceiveOpen.reject_exact,ReceiveOpen.context_exact,ReceiveOpen.future_sequence_exact,ReceiveOpen.future_material_exact,ReceiveOpen.finish_failure_restores_entry,ReceiveOpen.finish_future_success_publishes_same_plaintext,ReceiveOpen.finish_cached_success_publishes_same_plaintext,ReceiveFailureTrace.result_eq_entry",
	"ratchet.driver.lean.refinement_anchors=conditional:ResponseRefines,begin_send_refines,SendKdf.resume_refines,SendSeal.finish_refines_ideal_send,ReceiveOpen.failure_preserves_refinement,ReceiveFailureTrace.preserves_refinement,OpenReplyRefines,begin_receive_cached_refines,CachedOpenRefines.finish_success_matches_ideal,CachedOpenRefines.finish_success_refines_of_publication",
	"ratchet.driver.proverif.abstraction=atomic_seal_frame,ideal_exact_open_frame",
	"ratchet.driver.bridge=text_checker_only:not_semantic_Rust_to_Lean_or_ProVerif_refinement",
	"ratchet.receive_fixture.scope=finite_StateNeutralFutureReceive_and_StateNeutralCapacityReceive",
	"ratchet.receive_fixture.bridge=deterministic_text_synchronization:not_semantic_Rust_to_Lean_or_ProVerif_refinement",
	"ratchet.receive_fixture.schedule=two_nonreplicated_fixed_server_to_beacon_legs:not_arbitrary_schedule",
	"ratchet.receive_fixture.cache.representation=core_slots_oldest_first,proverif_nested_newest_first:membership_and_count_only",
	"ratchet.receive_fixture.core.max_gap=50",
	"ratchet.receive_fixture.core.cache_capacity=50:max_gap",
	"ratchet.receive_fixture.core.plan.future.derivations=target-receive_sequence",
	"ratchet.receive_fixture.core.plan.future.skipped=derivations-1",
	"ratchet.receive_fixture.core.plan.future.admission=skipped<=50,cached<=50-skipped",
	"ratchet.receive_fixture.core.plan.future.rejection=over_gap_or_capacity:none,zero_derivations",
	"ratchet.receive_fixture.core.target_advance=increment_counter_without_cache_append",
	"ratchet.receive_fixture.core.future.pending=skipped_in_staged_slots,target_material_separate",
	"ratchet.receive_fixture.core.future.validity=target_not_in_committed_cache,committed_len=first_slot+skipped",
	"ratchet.receive_fixture.core.future.failure=ReceiveOpen.finish(None):exact_entry",
	"ratchet.receive_fixture.core.future.success=publish_staged_skipped,final_receive_chain,committed_control",
	"ratchet.receive_fixture.core.cached.prepare=lookup_target,preflight_target_and_last,successful_removal_plan",
	"ratchet.receive_fixture.core.cached.failure=ReceiveOpen.finish(None):exact_entry_no_swap",
	"ratchet.receive_fixture.core.cached.success=swap_remove_whole_target_with_last,publish_committed_control",
	"ratchet.receive_fixture.core.replay=old_or_equal_target_missing_from_cache:entry_rejected",
	"ratchet.receive_fixture.proverif.state=receive_state(counter,chain,cache)",
	"ratchet.receive_fixture.proverif.cache=receive_cache_entry(sequence,material,tail):newest_first",
	"ratchet.receive_fixture.proverif.short.rejection=exact_candidate_equality_then_open_frame_destructor_failure",
	"ratchet.receive_fixture.short.sequences=first:1,skipped:2,target:3",
	"ratchet.receive_fixture.short.ready_state=receive_state(1,chain_2,empty_cache)",
	"ratchet.receive_fixture.short.rejections=2:same_forged_target_frame,same_ready_state",
	"ratchet.receive_fixture.short.success.cache=sequence_2_only:target_3_absent",
	"ratchet.receive_fixture.short.success.state=receive_state(3,chain_4,cache_2)",
	"ratchet.receive_fixture.short.replay=accepted_target_3_rejected_from_committed_state",
	"ratchet.receive_fixture.short.cached_consume=sequence_2:last_slot_case,empty_cache_after",
	"ratchet.receive_fixture.short.sent=sequence_1:past,sequence_2:skipped,sequence_3:target",
	"ratchet.receive_fixture.short.received=sequence_1:first_plaintext,sequence_3:accepted_plaintext,sequence_2:delayed_plaintext",
	"ratchet.receive_fixture.capacity.sequences=entry:1,boundary:52,cached_release:51,overflow:54,postrelease_skipped:53",
	"ratchet.receive_fixture.capacity.ready_state=receive_state(1,chain_2,empty_cache)",
	"ratchet.receive_fixture.capacity.boundary=target_52:51_derivations,50_skipped",
	"ratchet.receive_fixture.capacity.boundary.cache=sequences_2_through_51:length_50,target_52_absent",
	"ratchet.receive_fixture.capacity.boundary.state=receive_state(52,chain_53,cache_2_through_51)",
	"ratchet.receive_fixture.capacity.overflow=target_54:one_skipped_plus_full_cache,reject_same_state",
	"ratchet.receive_fixture.capacity.release=consume_cached_51:last_slot_case,length_49",
	"ratchet.receive_fixture.capacity.released_state=receive_state(52,chain_53,cache_2_through_50)",
	"ratchet.receive_fixture.capacity.after_release=target_54:2_derivations,cache_53,length_50,target_54_absent",
	"ratchet.receive_fixture.capacity.after_release.state=receive_state(54,chain_55,cache_2_through_50_plus_53)",
	"ratchet.receive_fixture.capacity.sent=sequence_1:first,sequence_52:maximum_gap,sequence_51:cached,sequence_54:after_release",
	"ratchet.receive_fixture.capacity.received=sequence_1:first,sequence_52:maximum_gap,sequence_51:cached,sequence_54:after_release",
	"ratchet.receive_fixture.queries.secrecy=6_application_canaries",
	"ratchet.receive_fixture.queries.correspondence=11_state_and_origin_queries",
	"ratchet.receive_fixture.queries.reachability=10_receive_state_events",
	"registration.lifecycle.scope=deterministic_source_and_finite_symbolic_synchronization:not_semantic_Rust_to_ProVerif_refinement",
	"registration.lifecycle.claim=at_most_one_Some_return_from_get_registration_bundle_per_live_honest_Beacon_object",
	"registration.lifecycle.randomness=key_generation_and_public_key_uniqueness_not_proved",
	"registration.lifecycle.beacon.object.new=Fresh",
	"registration.lifecycle.beacon.object.materials=generated_identity,generated_prekey,generated_mlkem768_keypair",
	"registration.lifecycle.beacon.bundle.eligible=Fresh,FreshWithCoins",
	"registration.lifecycle.beacon.bundle.ineligible=InitSent,Established,Aborted:return_None",
	"registration.lifecycle.beacon.bundle.fresh.one_time=generated_for_current_attempt",
	"registration.lifecycle.beacon.bundle.fresh_with_coins.one_time=stored_current_key",
	"registration.lifecycle.beacon.bundle.start=beacon_start(control,identity,prekey,pq,one_time)",
	"registration.lifecycle.beacon.bundle.serialization=typed_InitKex,four_fields,write_message",
	"registration.lifecycle.beacon.bundle.transition_order=successful_write_message_before_state_replace",
	"registration.lifecycle.beacon.bundle.success.fresh=InitSent(started_state,same_prekey,generated_one_time,same_pq)",
	"registration.lifecycle.beacon.bundle.success.fresh_with_coins=InitSent(started_state,same_prekey,same_one_time,same_pq)",
	"registration.lifecycle.beacon.bundle.success.return=Some(serialized_buffer)",
	"registration.lifecycle.beacon.bundle.post_success=InitSent_subsequent_call_returns_None",
	"registration.lifecycle.beacon.post_init.finish=Established_or_Aborted:not_eligible",
	"registration.lifecycle.beacon.post_init.delete_one_time=Aborted",
	"registration.lifecycle.beacon.post_init.delete_pq=Aborted",
	"registration.lifecycle.beacon.post_init.new_one_time=None",
	"registration.lifecycle.beacon.bundle.pretransition_failure=eligible_state_unchanged,retry_possible,no_retry_byte_equality_claim",
	"registration.lifecycle.beacon.bundle.fresh_retry=may_regenerate_one_time_key",
	"registration.lifecycle.beacon.bundle.generated_take_failure=restore_Fresh_then_return_None",
	"registration.lifecycle.core.beacon_start=BeaconFresh_input_to_BeaconInitSent_output",
	"registration.lifecycle.core.beacon_start.scope=structural_typestate_not_runtime_affinity_or_uniqueness",
	"registration.lifecycle.replay_id.size=64:32_byte_identity_plus_32_byte_one_time",
	"registration.lifecycle.replay_id.layout=bytes_0_31_identity,bytes_32_63_one_time",
	"registration.lifecycle.replay_id.fields=identity,one_time",
	"registration.lifecycle.replay_id.excludes=prekey,pq",
	"registration.lifecycle.replay_id.equality=exact_bytes:not_hash_or_collision_assumption",
	"registration.lifecycle.replay_id.wrapper=registration_id_calls_VerifiedInitKex.registration_id",
	"registration.lifecycle.replay_id.proverif=RegistrationId(registration_identifier(identity,one_time))",
	"registration.lifecycle.server.storage=consumed_registrations:HashSet_of_64_byte_registration_ids",
	"registration.lifecycle.server.id_source=validated_InitKex_registration_id",
	"registration.lifecycle.server.status=contains_true:Consumed,contains_false:Fresh",
	"registration.lifecycle.server.status_gate=validate_before_ephemeral_generation,MLKEM_encapsulation,and_DH_work",
	"registration.lifecycle.server.reserve=consumed_set_try_reserve_before_ephemeral_generation,MLKEM_encapsulation,and_DH_work",
	"registration.lifecycle.server.accept=server_accept_same_verified_registration_and_status",
	"registration.lifecycle.server.order=post_validation_PQXDH_response_crypto,server_accept,derive_root,insert_consumed,return_output",
	"registration.lifecycle.server.insert=exact_registration_id_after_root_derivation",
	"registration.lifecycle.server.output=RegistrationOutput_after_successful_insert",
	"registration.lifecycle.server.preinsert_failure=not_consumed_and_may_retry",
	"registration.lifecycle.server.response=separate_later_build_registration_response_call",
	"registration.lifecycle.server.response_failure=consumed_id_not_removed",
	"registration.lifecycle.server.known_ids=assigned_numeric_peer_map:not_registration_identity_uniqueness",
	"registration.lifecycle.proverif.honest_guard.scope=one_nonreplicated_owner_for_one_fresh_honest_identity",
	"registration.lifecycle.proverif.honest_guard.first_input=public_parsed_identity,InitKex,registration_id",
	"registration.lifecycle.proverif.honest_guard.first_transition=RegistrationConsumed_event_before_replay_fresh_reply",
	"registration.lifecycle.proverif.honest_guard.replay=replicated_same_identity_inputs_reply_consumed",
	"registration.lifecycle.proverif.server.order=root_derivation_before_guard_fresh_before_accept_or_abort",
	"registration.lifecycle.proverif.server.accept=only_after_replay_fresh",
	"registration.lifecycle.proverif.server.abort=consumption_precedes_ServerResponseAborted",
	"registration.lifecycle.proverif.honest_beacon=bundle_and_guard_once_in_finite_role",
	"registration.lifecycle.proverif.malicious_server=bypasses_honest_replay_guard",
	"registration.lifecycle.proverif.malicious_scope=every_attacker_owned_request_fresh:deliberate_overapproximation",
	"registration.lifecycle.proverif.scope=not_global_replay,persistence,multi_owner,rollback_or_crash",
	"registration.lifecycle.hb49.bundles=same_identity,same_prekey,same_one_time,different_mlkem_keys",
	"registration.lifecycle.hb49.replay_id=same_identity_and_one_time_imply_equal_source_id",
	"registration.lifecycle.hb49.production=second_registration_consumed_after_first_successful_get_shared_secret",
	"registration.lifecycle.hb49.scope=isolated_unsupported_control:not_production_rotation_or_attack",
	"initial_ratchet.scope=deterministic_source_and_finite_symbolic_synchronization:not_semantic_Rust_to_Lean_or_ProVerif_refinement",
	"initial_ratchet.claim=exact_root_handoff_to_typed_64_byte_response_and_role_ordered_initial_kernel",
	"initial_ratchet.condition=complementarity_requires_equal_local_roots_and_equal_outputs_from_the_same_faithful_deterministic_response_function",
	"initial_ratchet.source.server.output=RegistrationOutput(derived_secret,control)",
	"initial_ratchet.source.server.root=derive_root_key_input(pending.root_key_input_mut())",
	"initial_ratchet.source.server.cross_method=get_shared_secret_returns_by_value_and_build_registration_response_consumes_caller_supplied_value",
	"initial_ratchet.source.server.provenance=RegistrationOutput_not_indexed_by_producer_or_Server_instance",
	"initial_ratchet.source.derived_root.output_width=KEX_KDF_OUT_LEN:usize=32",
	"initial_ratchet.source.derived_root.width_link=KEX_KDF_OUT_LEN==KDF_STATE_SIZE",
	"initial_ratchet.source.derived_root.alias=SecretArr<KDF_STATE_SIZE,systems::Pqxdh,roles::DerivedSecret>",
	"initial_ratchet.source.derived_root.accessor.signature=&[u8;S]",
	"initial_ratchet.source.derived_root.accessor.body=&self.data",
	"initial_ratchet.source.server.destructure=derived_secret,control:pending",
	"initial_ratchet.source.server.start=start_server_candidate_ratchet_kdf(candidate,derived_secret.as_array())",
	"initial_ratchet.source.server.finish=finish_initial_ratchet_kdf(same_pending)",
	"initial_ratchet.source.server.wrap=RatchetManager::from_kernel(returned_kernel)",
	"initial_ratchet.source.server.initial_use=wrapped_kernel_before_encrypt_message_with_ratchet",
	"initial_ratchet.source.beacon.root=derive_root_key_input(candidate.root_key_input_mut())",
	"initial_ratchet.source.beacon.start=start_beacon_candidate_ratchet_kdf(candidate,derived_secret.as_array())",
	"initial_ratchet.source.beacon.finish=finish_initial_ratchet_kdf(same_pending)",
	"initial_ratchet.source.beacon.wrap=RatchetManager::from_kernel(returned_kernel)",
	"initial_ratchet.source.beacon.initial_use=wrapped_kernel_before_decrypt_message_with_ratchet",
	"initial_ratchet.core.pending.fields=request,initialization",
	"initial_ratchet.core.pending.affine=neither_Clone_nor_Copy",
	"initial_ratchet.core.pending.request_accessor=&self.request",
	"initial_ratchet.core.response.type=InitialRatchetKdfResponse",
	"initial_ratchet.core.response.output=64",
	"initial_ratchet.core.response.constructor=Self{bytes}",
	"initial_ratchet.core.response.distinct=RatchetKdfResponse_is_76_bytes",
	"initial_ratchet.core.response.provenance=not_tied_to_particular_pending_by_type",
	"initial_ratchet.core.response.bytes_accessor=&self.bytes",
	"initial_ratchet.core.request.input=exact_32_byte_root",
	"initial_ratchet.core.request.label=SYM_RATCHET_INFO",
	"initial_ratchet.core.request.fields=input:[u8;32],info:[u8;41]",
	"initial_ratchet.core.request.accessors=input:&self.input,info:&self.info",
	"initial_ratchet.core.start.signatures=root:&[u8;32],candidate:role_specific_reference,return:InitialRatchetKdfPending",
	"initial_ratchet.core.start.server=candidate.ratchet_initialization()",
	"initial_ratchet.core.start.beacon=candidate.ratchet_initialization()",
	"initial_ratchet.core.initialization.server=send_offset:0,receive_offset:32",
	"initial_ratchet.core.initialization.beacon=send_offset:32,receive_offset:0",
	"initial_ratchet.core.split.left=output[0..32]",
	"initial_ratchet.core.split.right=output[32..64]",
	"initial_ratchet.core.resume=split_response_with_same_pending.initialization",
	"initial_ratchet.core.kernel=ConcreteRatchetKernel::new(send_chain,receive_chain)",
	"initial_ratchet.core.kernel.initialization=ConcreteRatchetKernel::from_counters(0,0,send_chain,receive_chain)",
	"initial_ratchet.adapter.initial_hkdf.output=64",
	"initial_ratchet.adapter.executor=input:request.input(),label:request.info(),output:OUTPUT_SIZE_bytes",
	"initial_ratchet.adapter.finish.hkdf=initial_ratchet_hkdf(same_pending.request()):once",
	"initial_ratchet.adapter.finish.response=InitialRatchetKdfResponse::from_bytes(exact_hkdf_bytes)",
	"initial_ratchet.adapter.finish.resume=resume_initial_ratchet_kdf(same_pending,same_response):once",
	"initial_ratchet.adapter.finish.provenance=checked_local_dataflow:not_response_type",
	"initial_ratchet.lean.structural=start_initial_ratchet_kdf_exact,initial_request_accessor_exact,start_beacon_ratchet_kdf_exact,start_server_ratchet_kdf_exact,resume_initial_ratchet_kdf_is_core_partition",
	"initial_ratchet.lean.ideal=Pqxdh.rootChains,Pqxdh.HonestRun.chain_agreement",
	"initial_ratchet.lean.scope=checked_interpretation_anchors_and_ideal_model:text_link_only",
	"initial_ratchet.proverif.definition.server_to_beacon=first32(HKDF(root,SYM))",
	"initial_ratchet.proverif.definition.beacon_to_server=second32(HKDF(root,SYM))",
	"initial_ratchet.proverif.honest_beacon.root=pqxdh_root(RootKeyInput_to_bitstring(root_input))",
	"initial_ratchet.proverif.server.root=pqxdh_root(RootKeyInput_to_bitstring(root_input))",
	"initial_ratchet.proverif.malicious_server.root=pqxdh_root(RootKeyInput_to_bitstring(root_input))",
	"initial_ratchet.proverif.server.initial_seal=server_to_beacon_chain(root)",
	"initial_ratchet.proverif.server.initial_open=beacon_to_server_chain(root)",
	"initial_ratchet.proverif.honest_beacon.initial_open=server_to_beacon_chain(root)",
	"initial_ratchet.proverif.honest_beacon.outgoing=beacon_to_server_chain(root)",
	"initial_ratchet.proverif.malicious_server.initial_seal=server_to_beacon_chain(root)",
	"initial_ratchet.proverif.honest_beacon.initial_material=ratchet_material(server_chain_1)",
	"initial_ratchet.proverif.honest_beacon.outgoing_material=ratchet_material(beacon_send_chain_1)",
	"initial_ratchet.proverif.server.initial_material=ratchet_material(server_chain_1)",
	"initial_ratchet.proverif.scoped_occurrences=5",
	"initial_ratchet.proverif.complementarity=conditional_on_equal_roots_and_equal_outputs_from_the_same_faithful_deterministic_response_function",
	"initial_ratchet.bridge=source_Lean_and_ProVerif_text_synchronization_only",
	"initial_ratchet.excludes=HKDF_security,totality,correctness,noncollision,root_agreement,RegistrationOutput_origin,same_Server_instance_provenance,response_type_provenance,array_term_equality,extraction,compiler,AEAD,CTX,nonce,arbitrary_schedules,persistence,multiuser,crash,erasure",
	"later_registration.scope=source_and_finite_ProVerif_synchronization:not_semantic_Rust_to_ProVerif_or_Lean_refinement",
	"later_registration.claim=finite_ideal_fixture_accepts_genuine_sequence_3;source_has_matching_general_receive_and_no_first_sequence_gate_shape",
	"later_registration.source.reference=production_source_is_ultimate_reference:no_behavior_change",
	"later_registration.source.beacon.entry=finish_registration_requires_InitSent_control",
	"later_registration.source.beacon.response=reads_identityKey,ephemeralKey,kemCipherText,keyId,and_appCipherText_from_one_KexResponse",
	"later_registration.source.beacon.decrypt=decrypt_message_with_ratchet(response.appCipherText,candidate.server_key_id,associated_data,same_candidate_ratchet)",
	"later_registration.source.beacon.sender=authenticated_server_key_id_is_decrypted.key_id",
	"later_registration.source.beacon.binding=authenticated_plaintext_prefix_is_authenticated_against_response_assigned_key_id",
	"later_registration.source.beacon.staged=successful_general_receive_returns_the_advanced_ratchet_in_staged",
	"later_registration.source.beacon.commit=Established_stores_the_same_staged_ratchet_after_server_binding_checks",
	"later_registration.source.beacon.return=Some_returns_authenticated_plaintext_after_the_binding_prefix",
	"later_registration.source.beacon.no_first_gate=finish_registration_does_not_read_decrypted.seq_or_require_sequence_1",
	"later_registration.adapter.sequence=key_seq_is_frame.get_seq",
	"later_registration.adapter.begin=begin_receive(same_taken_kernel,key_seq,same_OpenFrameContext)",
	"later_registration.adapter.loop=each_ReceiveKdfRequested_uses_ratchet_hkdf(same_pending.request)_then_same_pending.resume",
	"later_registration.adapter.open=open_frame(open.material,open.sequence,open.context)",
	"later_registration.adapter.finish=same_open.finish(opened)_then_returned_kernel_is_put_before_plaintext_return",
	"later_registration.adapter.result=Decrypted(plaintext,kid,key_seq)",
	"later_registration.adapter.no_first_gate=generic_receive_has_no_first_sequence_special_case",
	"later_registration.core.max_gap=RATCHET_MAX_GAP:50",
	"later_registration.core.plan=future_derivations=target-receive_sequence;skipped=derivations-1",
	"later_registration.core.plan_bounds=reject_if_skipped_gt_50_or_cached_gt_50_minus_skipped",
	"later_registration.core.skipped=advance_receive_increments_receive_sequence_and_appends_that_sequence_to_cache",
	"later_registration.core.target=advance_receive_target_increments_receive_sequence_without_allocating_a_cache_slot",
	"later_registration.core.begin=begin_receive_uses_plan_receive_until_and_preserves_the_entry_kernel_during_future_preparation",
	"later_registration.core.remaining=remaining_is_exact_future_derivation_count;skipped_starts_0",
	"later_registration.core.request=first_future_request_uses_entry_receive_chain",
	"later_registration.core.nonfinal=remaining_gt_1_uses_advance_receive_for_one_skipped_sequence",
	"later_registration.core.cache_pair=each_nonfinal_step_stages_exact_sequence_with_that_step_material",
	"later_registration.core.next=nonfinal_step_decrements_remaining_and_requests_the_returned_next_chain",
	"later_registration.core.final=remaining_eq_1_uses_advance_receive_target_and_the_final_step",
	"later_registration.core.pending=PendingReceive_separates_final_receive_chain,target_sequence,target_material,and_skipped_slots",
	"later_registration.core.validation=pending_requires_target_counter_exact_skipped_relation_and_target_lookup_absent",
	"later_registration.core.open=ReceiveOpen_future_sequence_and_material_are_pending.target_sequence_and_pending.target_material",
	"later_registration.core.finish=successful_future_open_calls_publish_future_receive_and_returns_same_plaintext",
	"later_registration.refined.pending=target_material_is_separate_from_staged_skipped_slots",
	"later_registration.refined.validation=committed_send_counter_unchanged;receive_counter_target;cache_length_first_slot_plus_skipped;target_absent",
	"later_registration.refined.slots=staged_slots_pair_each_expected_skipped_sequence_with_material_and_require_live_destinations_empty",
	"later_registration.refined.publish=move_exact_skipped_slots_then_publish_final_receive_chain_then_committed_control",
	"later_registration.refined.target=target_material_remains_in_consumed_pending_and_is_not_inserted_into_live_cache",
	"later_registration.lean.structural=begin_receive_future_request_exact,ReceiveOpen.future_sequence_exact,ReceiveOpen.future_material_exact,ReceiveOpen.finish_future_success_publishes_same_plaintext",
	"later_registration.lean.control=max_gap_eq,plan_receive_until_accept,plan_receive_until_bound,advance_receive_ok,advance_receive_target_ok",
	"later_registration.lean.refinement=receiveMessage_refines,receiveMessage_state_neutral",
	"later_registration.lean.scope=existing_general_receive_anchors_only:no_sequence_3_specialization_or_cross_language_theorem",
	"later_registration.proverif.scope=one_finite_same_session_sequence_1_to_sequence_3_witness_and_one_identical_counterfactual_gate",
	"later_registration.proverif.session=one_genuine_Server_and_fresh_Beacon_reconstruct_equal_root,associated_data,session,and_initial_role_chains",
	"later_registration.proverif.original=sequence_1_response_contains_registration_payload(assigned_binding,SEQ1_PAYLOAD)",
	"later_registration.proverif.order=original_response_event_and_output_precede_genuine_sequence_2_and_sequence_3_frame_events_and_outputs",
	"later_registration.proverif.payloads=SEQ1,SEQ2,SEQ3_are_distinct_private_names;sequence_1_and_sequence_3_share_assigned_binding",
	"later_registration.proverif.substitution=original_and_candidate_KexResponse_fields_equal_except_appCipherText:first_frame_to_third_frame",
	"later_registration.proverif.candidate=one_attacker_candidate_equals_substituted_response_then_the_same_term_is_fanned_to_both_branches",
	"later_registration.proverif.response=both_branches_parse_all_five_fields_from_their_same_candidate_response",
	"later_registration.proverif.root_ad=both_branches_reconstruct_the_same_session_root_and_server_first_associated_data_from_the_candidate_fields",
	"later_registration.proverif.sender=inner_crypto_frame_sender_must_equal_genuine_Server_key_id",
	"later_registration.proverif.sequence=parsed_inner_sequence_is_passed_to_open_and_stored_in_poststate;exact_candidate_uses_material_3",
	"later_registration.proverif.payload=opened_registration_payload_is_exact_binding_plus_SEQ3_PAYLOAD;return_is_exact_SEQ3_PAYLOAD",
	"later_registration.proverif.poststate_send=counter_0_and_initial_beacon_to_server_chain_unchanged",
	"later_registration.proverif.poststate_receive=counter_sequence_3_and_live_server_chain_4",
	"later_registration.proverif.poststate_cache=newest_first_sequence_2_material_2_then_sequence_1_material_1_then_empty",
	"later_registration.proverif.poststate_target=sequence_3_material_3_is_used_for_open_and_is_not_inserted_into_the_exact_cache_constructor",
	"later_registration.proverif.binding=phase2_assigned_id_binding_gate_precedes_commit",
	"later_registration.proverif.faithful=successful_generic_open_flows_directly_to_shared_commit_without_a_sequence_gate",
	"later_registration.proverif.counterfactual=after_the_same_finite_successful_open_only_sequence_1_may_reach_shared_commit;sequence_3_cannot",
	"later_registration.proverif.events=opened_full_payload,returned_remainder,exact_ratchet_poststate,target_absence,substitution,and_server_origin_are_separate",
	"later_registration.proverif.queries=18:positive_witnesses,negative_first_only_commit_and_canary,and_injective_origin_order_correspondences",
	"later_registration.proverif.origin=faithful_commit_implies_selected_exact_substitution_and_same_session_root_genuine_sequence_3_Server_send_after_original_response",
	"later_registration.proverif.constructor_condition=exact_cache_and_chain_equations_hold_in_the_ideal_free_constructor_model;HB54_collision_conditioning_is_separate",
	"later_registration.excludes=arbitrary_schedules,semantic_refinement,parser_compiler_or_serialization_theorems,liveness,primitive_security_correctness_or_totality,HKDF_correctness,CTX_or_AEAD_security,production_sequence_gate,full_BeaconState_or_PQXDH_control_poststate,persistence,multiuser,crash,erasure",
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
	extraction: String,
	mlkem_reencapsulation_control: String,
	makefile: String,
	adapter_ratchet: String,
	adapter_shared: String,
	core_commitment: String,
	core_pqxdh: String,
	core_pqxdh_concrete: String,
	core_ratchet: String,
	core_ratchet_concrete: String,
	core_ratchet_control: String,
	core_ratchet_refined: String,
	lean_ratchet_effect: String,
	lean_ratchet_effect_refinement: String,
	lean_pqxdh_kdf: String,
	lean_pqxdh_theorems: String,
	cryptoframe_schema: String,
	phase1_schema: String,
	phase2_schema: String,
	adapter_server: String,
	adapter_beacon: String,
	failed_receive_queries: String,
	failed_receive_reachability_queries: String,
	later_registration_control: String,
	later_registration_queries: String,
	later_registration_main: String,
	proverif_result_checker: String,
	lean_ratchet_control: String,
	lean_ratchet_refinement: String,
}

impl Snapshot {
	fn production() -> Self {
		Self {
			interface: INTERFACE.to_owned(),
			crypto: CRYPTO_MODEL.to_owned(),
			environment: ENVIRONMENT_MODEL.to_owned(),
			active_quantum_witness: ACTIVE_QUANTUM_WITNESS.to_owned(),
			extraction: EXTRACTION_MODEL.to_owned(),
			mlkem_reencapsulation_control: MLKEM_REENCAPSULATION_CONTROL.to_owned(),
			makefile: CORE_MAKEFILE.to_owned(),
			adapter_ratchet: ADAPTER_RATCHET.to_owned(),
			adapter_shared: ADAPTER_SHARED.to_owned(),
			core_commitment: CORE_COMMITMENT.to_owned(),
			core_pqxdh: CORE_PQXDH.to_owned(),
			core_pqxdh_concrete: CORE_PQXDH_CONCRETE.to_owned(),
			core_ratchet: CORE_RATCHET.to_owned(),
			core_ratchet_concrete: CORE_RATCHET_CONCRETE.to_owned(),
			core_ratchet_control: CORE_RATCHET_CONTROL.to_owned(),
			core_ratchet_refined: CORE_RATCHET_REFINED.to_owned(),
			lean_ratchet_effect: LEAN_RATCHET_EFFECT.to_owned(),
			lean_ratchet_effect_refinement: LEAN_RATCHET_EFFECT_REFINEMENT.to_owned(),
			lean_pqxdh_kdf: LEAN_PQXDH_KDF.to_owned(),
			lean_pqxdh_theorems: LEAN_PQXDH_THEOREMS.to_owned(),
			cryptoframe_schema: CRYPTOFRAME_SCHEMA.to_owned(),
			phase1_schema: PHASE1_SCHEMA.to_owned(),
			phase2_schema: PHASE2_SCHEMA.to_owned(),
			adapter_server: ADAPTER_SERVER.to_owned(),
			adapter_beacon: ADAPTER_BEACON.to_owned(),
			failed_receive_queries: FAILED_RECEIVE_QUERIES.to_owned(),
			failed_receive_reachability_queries: FAILED_RECEIVE_REACHABILITY_QUERIES.to_owned(),
			later_registration_control: LATER_REGISTRATION_CONTROL.to_owned(),
			later_registration_queries: LATER_REGISTRATION_QUERIES.to_owned(),
			later_registration_main: LATER_REGISTRATION_MAIN.to_owned(),
			proverif_result_checker: PROVERIF_RESULT_CHECKER.to_owned(),
			lean_ratchet_control: LEAN_RATCHET_CONTROL.to_owned(),
			lean_ratchet_refinement: LEAN_RATCHET_REFINEMENT.to_owned(),
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

fn stable_text_hash(source: &str) -> u64 {
	source
		.as_bytes()
		.iter()
		.fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
			(hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
		})
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

fn require_ordered(source: &str, wanted: &[&str], label: &str) -> Result<(), String> {
	let mut cursor = 0usize;
	for item in wanted {
		let relative = source[cursor..]
			.find(item)
			.ok_or_else(|| format!("{label} changed: {item} is missing or out of order"))?;
		cursor += relative + item.len();
	}
	Ok(())
}

fn section_between<'a>(
	source: &'a str,
	start_marker: &str,
	end_marker: &str,
	label: &str,
) -> Result<&'a str, String> {
	let start = source
		.find(start_marker)
		.ok_or_else(|| format!("missing {label} start: {start_marker}"))?;
	let relative_end = source[start + start_marker.len()..]
		.find(end_marker)
		.ok_or_else(|| format!("missing {label} end: {end_marker}"))?;
	let end = start + start_marker.len() + relative_end;
	Ok(&source[start..end])
}

fn require_exact_calls(
	source: &str,
	function: &str,
	expected: &[Vec<String>],
	label: &str,
) -> Result<(), String> {
	let calls = all_arguments(source, function)?;
	if calls != expected {
		return Err(format!("{label} changed: {calls:?}"));
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

fn validate_endpoint_frame_context_wiring(snapshot: &Snapshot) -> Result<(), String> {
	let parsed_sender = rust_body(&snapshot.adapter_ratchet, "encrypted_frame_sender")?;
	require_once(
		&parsed_sender,
		"letreader=capnp::serialize::read_message(data,ReaderOptions::new()).ok()?;",
		"endpoint Server wire-sender Cap'n Proto read",
	)?;
	require_once(
		&parsed_sender,
		"lettyped_reader=TypedReader::<_,cryptoframe_capnp::crypto_frame::Owned>::new(reader);",
		"endpoint Server wire-sender typed CryptoFrame reader",
	)?;
	require_once(
		&parsed_sender,
		"Some(typed_reader.get().ok()?.get_key_id())",
		"endpoint Server wire-sender keyId getter",
	)?;
	require_ordered_once(
		&parsed_sender,
		&[
			"capnp::serialize::read_message(data,ReaderOptions::new())",
			"TypedReader::<_,cryptoframe_capnp::crypto_frame::Owned>::new(reader)",
			"typed_reader.get().ok()?.get_key_id()",
		],
		"endpoint Server wire-sender parse source order",
	)?;

	let server_associated_data = rust_body(&snapshot.adapter_server, "associated_data")?;
	require_one_call(
		&server_associated_data,
		"build_associated_data",
		&[
			"self.identity_pk().clone()",
			"self.pk_by_kid(k)?.clone()",
			"",
		],
		"endpoint Server server-first associated-data mapping",
	)?;

	let server_send = rust_body(&snapshot.adapter_server, "encrypt_message")?;
	require_once(
		&server_send,
		"letad=self.associated_data(k)?;",
		"endpoint Server send peer-associated data",
	)?;
	require_once(
		&server_send,
		"letsender=self.identity_key_kid;",
		"endpoint Server send local sender",
	)?;
	require_one_call(
		&server_send,
		"encrypt_message_with_ratchet",
		&["b", "k", "sender", "&ad", "self.ratchet_manager_mut(k)?"],
		"endpoint Server send target/sender/context/ratchet mapping",
	)?;
	let server_receive = rust_body(&snapshot.adapter_server, "decrypt_message_transition")?;
	require_once(
		&server_receive,
		"letSome(k)=crate::ratchet::encrypted_frame_sender(b)else{returnReceiveTransition::Rejected;};",
		"endpoint Server parsed sender selector",
	)?;
	require_once(
		&server_receive,
		"letSome(ad)=self.associated_data(k)else{returnReceiveTransition::Rejected;};",
		"endpoint Server receive selected-peer associated data",
	)?;
	require_once(
		&server_receive,
		"letSome(ratchet)=self.ratchet_manager_mut(k)else{returnReceiveTransition::Rejected;};",
		"endpoint Server receive selected-peer ratchet",
	)?;
	require_one_call(
		&server_receive,
		"decrypt_message_with_ratchet",
		&["b", "k", "&ad", "ratchet"],
		"endpoint Server receive expected-sender/context/ratchet mapping",
	)?;
	require_once(
		&server_receive,
		"Some(decrypted)=>ReceiveTransition::Accepted(decrypted),None=>ReceiveTransition::Rejected,",
		"endpoint Server acceptance only after successful open",
	)?;
	require_ordered_once(
		&server_receive,
		&[
			"crate::ratchet::encrypted_frame_sender(b)",
			"self.associated_data(k)",
			"self.ratchet_manager_mut(k)",
			"decrypt_message_with_ratchet(b,k,&ad,ratchet)",
			"Some(decrypted)=>ReceiveTransition::Accepted(decrypted)",
		],
		"endpoint Server receive source order",
	)?;

	let beacon_send = rust_body(&snapshot.adapter_beacon, "encrypt_message")?;
	require_once(
		&beacon_send,
		"letsender=self.identity_key_kid;",
		"endpoint Beacon assigned sender snapshot",
	)?;
	require_once(
		&beacon_send,
		"letBeaconState::Established{control,associated_data,ratchet,}=&mutself.stateelse{returnNone;};",
		"endpoint Beacon send stored establishment state",
	)?;
	require_one_call(
		&beacon_send,
		"encrypt_message_with_ratchet",
		&[
			"b",
			"control.server_key_id()",
			"sender",
			"associated_data",
			"ratchet",
		],
		"endpoint Beacon send target/sender/stored context mapping",
	)?;
	let beacon_receive = rust_body(&snapshot.adapter_beacon, "decrypt_message")?;
	require_once(
		&beacon_receive,
		"letBeaconState::Established{control,associated_data,ratchet,}=&mutself.stateelse{returnNone;};",
		"endpoint Beacon receive stored establishment state",
	)?;
	require_one_call(
		&beacon_receive,
		"decrypt_message_with_ratchet",
		&["b", "control.server_key_id()", "associated_data", "ratchet"],
		"endpoint Beacon receive expected-sender/stored context mapping",
	)?;

	let server_initial = rust_body(&snapshot.adapter_server, "build_registration_response")?;
	require_once(
		&server_initial,
		"letremote_kid=candidate.key_id();",
		"endpoint registration assigned remote key ID",
	)?;
	require_one_call(
		&server_initial,
		"start_server_candidate_ratchet_kdf",
		&["&candidate", "derived_secret.as_array()"],
		"endpoint registration Server candidate ratchet",
	)?;
	require_once(
		&server_initial,
		"letmutratchet=RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending));",
		"endpoint registration Server initial ratchet materialization",
	)?;
	require_once(
		&server_initial,
		"letassociated_data=*candidate.associated_data();",
		"endpoint registration Server candidate associated data",
	)?;
	require_once(
		&server_initial,
		"letpublic_key=crypto_sign::PublicKey::from_bytes(candidate.beacon_identity_public_key()).ok()?;",
		"endpoint registration Server candidate peer identity",
	)?;
	require_one_call(
		&server_initial,
		"encrypt_message_with_ratchet",
		&[
			"&authenticated_plaintext",
			"remote_kid",
			"candidate.server_identity_key_id()",
			"&associated_data",
			"&mutratchet",
			"",
		],
		"endpoint registration Server initial target/sender/context/ratchet mapping",
	)?;
	require_once(
		&server_initial,
		"Some(RegResponse{serialized:buffer,kid:remote_kid,})",
		"endpoint registration Server returned target metadata",
	)?;
	require_once(
		&server_initial,
		"letold=self.known_ids.insert(remote_kid,EstablishedRemote::new(public_key,ratchet));",
		"endpoint registration Server committed peer identity and candidate ratchet",
	)?;
	require_ordered_once(
		&server_initial,
		&[
			"crypto_sign::PublicKey::from_bytes(candidate.beacon_identity_public_key())",
			"start_server_candidate_ratchet_kdf(&candidate,derived_secret.as_array())",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"letassociated_data=*candidate.associated_data();",
			"encrypt_message_with_ratchet(",
			"letencrypted=encrypted?;",
			"bundle.set_key_id(remote_kid)",
			"capnp::serialize_packed::write_message(&mutbuffer,msg.borrow_inner()).ok()?;",
			"let(next_control,established_peer)=verified_pqxdh::server_commit(candidate);",
			"self.known_ids.insert(remote_kid,EstablishedRemote::new(public_key,ratchet))",
			"self.control=next_control;",
			"Some(RegResponse{serialized:buffer,kid:remote_kid,})",
		],
		"endpoint registration Server initial source order",
	)?;

	let beacon_initial = rust_body(&snapshot.adapter_beacon, "finish_registration")?;
	require_one_call(
		&beacon_initial,
		"start_beacon_candidate_ratchet_kdf",
		&["&candidate", "derived_secret.as_array()"],
		"endpoint registration Beacon candidate ratchet",
	)?;
	require_once(
		&beacon_initial,
		"letmutratchet=RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending));",
		"endpoint registration Beacon initial ratchet materialization",
	)?;
	require_once(
		&beacon_initial,
		"letassociated_data=*candidate.associated_data();",
		"endpoint registration Beacon candidate associated data",
	)?;
	require_one_call(
		&beacon_initial,
		"decrypt_message_with_ratchet",
		&[
			"response.get_app_cipher_text().ok()?",
			"candidate.server_key_id()",
			"&associated_data",
			"&mutratchet",
			"",
		],
		"endpoint registration Beacon initial expected-sender/context/ratchet mapping",
	)?;
	require_once(
		&beacon_initial,
		"Some((authenticated,associated_data,ratchet,plaintext))})();",
		"endpoint registration Beacon candidate context handoff",
	)?;
	require_once(
		&beacon_initial,
		"self.identity_key_kid=authenticated.assigned_key_id();",
		"endpoint registration Beacon assigned local sender",
	)?;
	require_once(
		&beacon_initial,
		"self.state=BeaconState::Established{control:verified_pqxdh::beacon_commit(authenticated),associated_data,ratchet,};",
		"endpoint registration Beacon stores candidate context",
	)?;
	require_ordered_once(
		&beacon_initial,
		&[
			"start_beacon_candidate_ratchet_kdf(&candidate,derived_secret.as_array())",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"letassociated_data=*candidate.associated_data();",
			"decrypt_message_with_ratchet(",
			"verified_pqxdh::authenticate_registration_key_id_binding(",
			"Some((authenticated,associated_data,ratchet,plaintext))})();",
			"letserver_binding=authenticated.server_binding();",
			"ifself.server_kid()!=server_kid",
			"ifself.server_id.as_bytes()!=&server_binding.identity_public_key",
			"self.identity_key_kid=authenticated.assigned_key_id();",
			"self.state=BeaconState::Established",
		],
		"endpoint registration Beacon initial source order",
	)?;

	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	let honest_beacon = section_between(
		&environment,
		"letHonestBeacon(",
		"letMaliciousBeacon(",
		"symbolic HonestBeacon endpoint",
	)?;
	let server = section_between(
		&environment,
		"letServer(",
		"letMaliciousServer(",
		"symbolic Server endpoint",
	)?;
	let malicious_server = section_between(
		&environment,
		"letMaliciousServer(",
		"letKeepBeaconStatePrivate(",
		"symbolic MaliciousServer endpoint",
	)?;

	let honest_open_calls = all_arguments(honest_beacon, "open_frame")?;
	let expected_honest_open_calls = [
		[
			"server_material_1",
			"associated_data",
			"first_sequence()",
			"SERVER_KEY_ID",
			"initial_frame",
		],
		[
			"server_material_3",
			"associated_data",
			"next_sequence(next_sequence(first_sequence()))",
			"SERVER_KEY_ID",
			"third_frame",
		],
		[
			"server_material_2",
			"associated_data",
			"next_sequence(first_sequence())",
			"SERVER_KEY_ID",
			"second_frame",
		],
		[
			"ratchet_material(ratchet_next(server_chain_3))",
			"associated_data",
			"next_sequence(next_sequence(next_sequence(first_sequence())))",
			"SERVER_KEY_ID",
			"fourth_frame",
		],
	]
	.map(|call| call.map(str::to_owned).to_vec());
	if honest_open_calls != expected_honest_open_calls {
		return Err(format!(
			"symbolic server-to-Beacon open wiring changed: {honest_open_calls:?}"
		));
	}
	require_one_call(
		honest_beacon,
		"seal_frame",
		&[
			"beacon_material_1",
			"associated_data",
			"first_sequence()",
			"assigned_key_id",
			"beacon_record_secret",
		],
		"symbolic Beacon-to-Server seal wiring",
	)?;

	let server_seal_calls = all_arguments(server, "seal_frame")?;
	let expected_server_seal_calls = [
		[
			"server_material_1",
			"associated_data",
			"first_sequence()",
			"SERVER_KEY_ID",
			"registration_payload(binding,initial_secret)",
		],
		[
			"server_material_2",
			"associated_data",
			"next_sequence(first_sequence())",
			"SERVER_KEY_ID",
			"cached_secret",
		],
		[
			"server_material_3",
			"associated_data",
			"next_sequence(next_sequence(first_sequence()))",
			"SERVER_KEY_ID",
			"advance_secret",
		],
		[
			"server_material_4",
			"associated_data",
			"next_sequence(next_sequence(next_sequence(first_sequence())))",
			"SERVER_KEY_ID",
			"future_secret",
		],
	]
	.map(|call| call.map(str::to_owned).to_vec());
	if server_seal_calls != expected_server_seal_calls {
		return Err(format!(
			"symbolic Server-to-Beacon seal wiring changed: {server_seal_calls:?}"
		));
	}
	require_one_call(
		server,
		"open_frame",
		&[
			"beacon_material_1",
			"associated_data",
			"first_sequence()",
			"assigned_key_id",
			"beacon_frame",
		],
		"symbolic Server Beacon-frame open wiring",
	)?;
	require_one_call(
		malicious_server,
		"seal_frame",
		&[
			"server_material_1",
			"associated_data",
			"first_sequence()",
			"SERVER_KEY_ID",
			"registration_payload(binding,MALICIOUS_TASK_SECRET)",
		],
		"symbolic malicious-registration initial-frame wiring",
	)?;

	let honest_received_events = [
		[
			"session",
			"server_to_beacon()",
			"first_sequence()",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"initial_plaintext",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(next_sequence(first_sequence()))",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"third_plaintext",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(first_sequence())",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"second_plaintext",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(next_sequence(next_sequence(first_sequence())))",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"fourth_plaintext",
		],
	]
	.map(|call| call.map(str::to_owned).to_vec());
	require_exact_calls(
		honest_beacon,
		"MessageReceived",
		&honest_received_events,
		"symbolic HonestBeacon received-event fixture",
	)?;
	let honest_sent_events = [[
		"session",
		"beacon_to_server()",
		"first_sequence()",
		"assigned_key_id",
		"SERVER_KEY_ID",
		"beacon_record_secret",
	]]
	.map(|call| call.map(str::to_owned).to_vec());
	require_exact_calls(
		honest_beacon,
		"MessageSent",
		&honest_sent_events,
		"symbolic HonestBeacon sent-event fixture",
	)?;
	let server_sent_events = [
		[
			"session",
			"server_to_beacon()",
			"first_sequence()",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"initial_secret",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(first_sequence())",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"cached_secret",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(next_sequence(first_sequence()))",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"advance_secret",
		],
		[
			"session",
			"server_to_beacon()",
			"next_sequence(next_sequence(next_sequence(first_sequence())))",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"future_secret",
		],
	]
	.map(|call| call.map(str::to_owned).to_vec());
	require_exact_calls(
		server,
		"MessageSent",
		&server_sent_events,
		"symbolic Server sent-event fixture",
	)?;
	let server_received_events = [[
		"session",
		"beacon_to_server()",
		"first_sequence()",
		"assigned_key_id",
		"SERVER_KEY_ID",
		"beacon_plaintext",
	]]
	.map(|call| call.map(str::to_owned).to_vec());
	require_exact_calls(
		server,
		"MessageReceived",
		&server_received_events,
		"symbolic Server received-event fixture",
	)?;
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
	if ad_calls
		!= [
			vec!["server_identity", "beacon_identity"],
			vec!["server_identity", "beacon_identity"],
			vec!["server_identity", "beacon_identity"],
			vec!["main_server_identity", "main_beacon_identity"],
			vec!["main_server_identity", "main_beacon_identity"],
		] {
		return Err(format!(
			"associated-data identity order changed: {ad_calls:?}"
		));
	}

	let extraction = compact(&uncommented_pv(&snapshot.extraction)?);
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
	if scenarios.len() != 29 {
		return Err(format!(
			"expected 29 ProVerif scenarios, found {}",
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
	let later_registration = section_between(
		makefile,
		"check-proverif-later-sequence-registration:",
		"check-proverif-passive-classical-equivalence:",
		"later-sequence registration Make target",
	)?;
	for (wanted, label) in [
		(
			"check-proverif-later-sequence-registration: check-proverif-extraction",
			"later-sequence registration extraction prerequisite",
		),
		(
			"-lib $(PROVERIF_DIR)/phase2-assigned-id-strong-theory.pvl",
			"later-sequence registration binding theory",
		),
		(
			"-lib $(PROVERIF_DIR)/later-sequence-registration-control.pvl",
			"later-sequence registration control loader",
		),
		(
			"-lib $(PROVERIF_DIR)/later-sequence-registration-queries.pvl",
			"later-sequence registration query loader",
		),
		(
			"$(PROVERIF_DIR)/later-sequence-registration.pv",
			"later-sequence registration main model",
		),
		(
			"awk -v scenario=later-sequence-registration -f '$(PROVERIF_CHECKER)'",
			"later-sequence registration result checker",
		),
	] {
		require_once(later_registration, wanted, label)?;
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

fn validate_ratchet_effect_driver(snapshot: &Snapshot) -> Result<(), String> {
	let adapter_source = uncommented_rust(&snapshot.adapter_ratchet)?;
	let adapter = compact(&adapter_source);
	let slot = section_between(
		&adapter_source,
		"impl RatchetKernelSlot {",
		"impl Deref for RatchetKernelSlot",
		"ratchet kernel slot implementation",
	)?;
	let take = rust_body(slot, "take")?;
	require_once(
		&take,
		"self.kernel.take()",
		"ratchet driver affine slot take",
	)?;
	let put = rust_body(slot, "put")?;
	require_ordered_once(
		&put,
		&["assert!(self.kernel.is_none()", "self.kernel=Some(kernel);"],
		"ratchet driver returned-kernel slot put",
	)?;
	require_once(
		&adapter,
		"pub(crate)fnratchet_hkdf(request:&verified_ratchet::SymmetricRatchetKdfRequest,)->verified_ratchet::RatchetKdfResponse{verified_ratchet::RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))}",
		"ratchet driver typed KDF reply",
	)?;

	let send = rust_body(&snapshot.adapter_ratchet, "encrypt_message_with_ratchet")?;
	require_once(
		&send,
		"ifbytes.is_empty(){returnNone;}",
		"ratchet send empty-input precheck",
	)?;
	require_once(
		&send,
		"letcontext=SealFrameContext{bytes,target_kid,sender_kid,associated_data,};",
		"ratchet send exact frame context",
	)?;
	require_one_call(
		&send,
		"ratchet.refined.take",
		&[""],
		"ratchet send affine kernel take",
	)?;
	require_one_call(
		&send,
		"verified_ratchet::begin_send",
		&["kernel", "context"],
		"ratchet send begin effect",
	)?;
	require_once(
		&send,
		"verified_ratchet::SendStart::SendExhausted{kernel,..}=>{ratchet.refined.put(kernel);returnNone;}verified_ratchet::SendStart::SendKdfRequested(pending)=>pending,",
		"ratchet send exhausted and KDF branches",
	)?;
	require_one_call(
		&send,
		"ratchet_hkdf",
		&["pending.request()"],
		"ratchet send exact pending request interpretation",
	)?;
	require_one_call(
		&send,
		"pending.resume",
		&["response"],
		"ratchet send same-pending resume",
	)?;
	require_one_call(
		&send,
		"seal_frame",
		&["seal.material()", "seal.sequence()", "seal.context()"],
		"ratchet send seal capability handoff",
	)?;
	require_one_call(
		&send,
		"seal.finish",
		&["sealed"],
		"ratchet send capability finish",
	)?;
	let send_puts = all_arguments(&send, "ratchet.refined.put")?;
	if send_puts != [vec!["kernel".to_owned()], vec!["kernel".to_owned()]] {
		return Err(format!(
			"ratchet send returned-kernel puts changed: {send_puts:?}"
		));
	}
	require_once(
		&send,
		"ratchet.refined.put(kernel);sealed",
		"ratchet send returned-kernel put before result",
	)?;
	require_ordered(
		&send,
		&[
			"ifbytes.is_empty(){returnNone;}",
			"letcontext=SealFrameContext",
			"letkernel=ratchet.refined.take();",
			"verified_ratchet::begin_send(kernel,context)",
			"letresponse=ratchet_hkdf(pending.request());",
			"letseal=pending.resume(response);",
			"letsealed=seal_frame(seal.material(),seal.sequence(),seal.context());",
			"let(kernel,sealed)=seal.finish(sealed);",
			"ratchet.refined.put(kernel);",
		],
		"ratchet send synchronous effect order",
	)?;
	if !send.ends_with("sealed") {
		return Err("ratchet send returned sealed result changed".to_owned());
	}
	forbid(&send, ".cancel(", "ratchet send production cancellation")?;

	let concrete = compact(&uncommented_rust(&snapshot.core_ratchet_concrete)?);
	for phase in [
		"pubenumSendStart<Context>{",
		"pubstructSendKdf<Context>{",
		"pubstructSendSeal<Context>{",
		"pubenumReceiveEffect<Context>{",
		"pubstructReceiveKdf<Context>{",
		"pubstructReceiveOpen<Context>{",
	] {
		require_once(&concrete, phase, "ratchet core affine phase API")?;
	}
	let send_seal = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> SendSeal<Context>",
		"/// One phase of an owned receive transaction.",
		"ratchet core send seal phase",
	)?;
	let send_finish = rust_body(send_seal, "finish")?;
	require_once(
		&send_finish,
		"let_=finish_send(self.logical);(self.advanced,sealed)",
		"ratchet send finish preserves interpreter result on advanced kernel",
	)?;

	let receive = rust_body(&snapshot.adapter_ratchet, "decrypt_message_with_ratchet")?;
	require_ordered(
		&receive,
		&[
			"ifdata.is_empty(){returnNone;}",
			"capnp::serialize::read_message(data,ReaderOptions::new())",
			"TypedReader::<_,cryptoframe_capnp::crypto_frame::Owned>::new(reader)",
			"letkid=frame.get_key_id();",
			"ifkid!=expected_sender_kid{returnNone;}",
			"letciphertext=frame.get_cipher_text().ok()?;",
			"ifct_len<=MESSAGE_OVERHEAD{returnNone;}",
			"letcontext=OpenFrameContext{ciphertext,associated_data,sender_kid:kid,};",
			"letkey_seq=frame.get_seq();",
			"letkernel=ratchet.refined.take();",
			"letmuteffect=verified_ratchet::begin_receive(kernel,key_seq,context);",
			"letplaintext=loop{",
		],
		"ratchet receive prechecks and effect start order",
	)?;
	require_one_call(
		&receive,
		"ratchet.refined.take",
		&[""],
		"ratchet receive affine kernel take",
	)?;
	require_one_call(
		&receive,
		"verified_ratchet::begin_receive",
		&["kernel", "key_seq", "context"],
		"ratchet receive begin effect",
	)?;
	require_once(
		&receive,
		"verified_ratchet::ReceiveEffect::ReceiveRejected{kernel,..}=>{ratchet.refined.put(kernel);returnNone;}",
		"ratchet receive rejected branch",
	)?;
	require_once(
		&receive,
		"letmuteffect=verified_ratchet::begin_receive(kernel,key_seq,context);letplaintext=loop{effect=matcheffect{",
		"ratchet receive effect loop without fixed iteration count",
	)?;
	let receive_kdf_arm = section_between(
		&receive,
		"verified_ratchet::ReceiveEffect::ReceiveKdfRequested(pending)=>{",
		"verified_ratchet::ReceiveEffect::ReceiveOpenRequested(open)=>{",
		"ratchet receive KDF arm",
	)?;
	forbid(
		receive_kdf_arm,
		"ratchet.refined.put(",
		"ratchet receive KDF-arm live publication",
	)?;
	forbid(
		&receive,
		".cancel(",
		"ratchet receive production cancellation",
	)?;
	require_one_call(
		&receive,
		"ratchet_hkdf",
		&["pending.request()"],
		"ratchet receive exact pending request interpretation",
	)?;
	require_one_call(
		&receive,
		"pending.resume",
		&["response"],
		"ratchet receive same-pending resume",
	)?;
	require_once(
		&receive,
		"verified_ratchet::ReceiveEffect::ReceiveKdfRequested(pending)=>{letresponse=ratchet_hkdf(pending.request());pending.resume(response)}",
		"ratchet receive private KDF loop arm",
	)?;
	require_once(
		&receive,
		"letSome(material)=open.material()else{let(kernel,_)=open.reject();ratchet.refined.put(kernel);returnNone;};",
		"ratchet receive no-material rejection",
	)?;
	require_one_call(
		&receive,
		"open_frame",
		&["material", "open.sequence()", "open.context()"],
		"ratchet receive open capability handoff",
	)?;
	require_one_call(
		&receive,
		"open.finish",
		&["opened"],
		"ratchet receive capability finish",
	)?;
	let receive_puts = all_arguments(&receive, "ratchet.refined.put")?;
	if receive_puts
		!= [
			vec!["kernel".to_owned()],
			vec!["kernel".to_owned()],
			vec!["kernel".to_owned()],
		] {
		return Err(format!(
			"ratchet receive returned-kernel puts changed: {receive_puts:?}"
		));
	}
	require_ordered(
		&receive,
		&[
			"letSome(material)=open.material()else{",
			"let(kernel,_)=open.reject();",
			"ratchet.refined.put(kernel);",
			"returnNone;",
			"letopened=open_frame(material,open.sequence(),open.context());",
			"let(kernel,opened)=open.finish(opened);",
			"ratchet.refined.put(kernel);",
			"breakopened?;",
		],
		"ratchet receive open and terminal publication order",
	)?;
	require_once(
		&receive,
		"Some(Decrypted{plaintext,key_id:kid,seq:key_seq,})",
		"ratchet receive parsed result metadata",
	)?;
	let receive_open = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveOpen<Context>",
		"/// Checked restoration builder",
		"ratchet core receive open phase",
	)?;
	let receive_finish = rust_body(receive_open, "finish")?;
	require_once(
		&receive_finish,
		"None=>return(self.entry,None)",
		"ratchet receive finish failure restores entry",
	)?;
	require_once(
		&receive_finish,
		"PreparedReceive::PreparedReceiveCachedCase(prepared)=>{publish_cached_receive(&mutentry.refined,prepared);}",
		"ratchet core cached receive publication branch",
	)?;
	require_once(
		&receive_finish,
		"PreparedReceive::PreparedReceiveFutureCase(pending)=>{publish_future_receive(&mutentry.refined,pending);}",
		"ratchet core future receive publication branch",
	)?;
	let begin_receive = rust_body(&snapshot.core_ratchet_concrete, "begin_receive")?;
	for absent in [
		"publish_cached_receive",
		"publish_future_receive",
		"kernel.refined.control=",
		"kernel.refined.send_chain=",
		"kernel.refined.receive_chain=",
		"kernel.refined.receive_slots=",
	] {
		forbid(
			&begin_receive,
			absent,
			"ratchet core begin_receive live publication",
		)?;
	}
	let receive_kdf = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveKdf<Context>",
		"impl<Context> ReceiveOpen<Context>",
		"ratchet core receive KDF phase",
	)?;
	let receive_resume = rust_body(receive_kdf, "resume")?;
	forbid(
		&receive_resume,
		"publish_cached_receive",
		"ratchet core receive KDF cached publication",
	)?;
	forbid(
		&receive_resume,
		"publish_future_receive",
		"ratchet core receive KDF future publication",
	)?;
	require_ordered(
		&receive_finish,
		&[
			"letplaintext=matchopened{",
			"None=>return(self.entry,None)",
			"letmutentry=self.entry;",
			"publish_cached_receive(&mutentry.refined,prepared)",
			"publish_future_receive(&mutentry.refined,pending)",
			"(entry,Some(plaintext))",
		],
		"ratchet core receive publication after successful open",
	)?;

	for theorem in [
		"theorem ratchet.concrete.begin_send_nonexhausted_exact",
		"theorem ratchet.concrete.begin_send_exhausted_restores_entry",
		"theorem ratchet.concrete.SendKdf.request_exact",
		"theorem ratchet.concrete.SendKdf.resume_exact",
		"theorem ratchet.concrete.SendSeal.finish_returns_interpreter_result",
		"theorem ratchet.concrete.begin_receive_rejected_plan_restores_entry",
		"theorem ratchet.concrete.begin_receive_cached_exact",
		"theorem ratchet.concrete.begin_receive_future_request_exact",
		"theorem ratchet.concrete.ReceiveKdf.request_exact",
		"theorem ratchet.concrete.ReceiveOpen.reject_exact",
		"theorem ratchet.concrete.ReceiveOpen.context_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_sequence_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_material_exact",
		"theorem ratchet.concrete.ReceiveOpen.finish_failure_restores_entry",
		"theorem ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext",
		"theorem ratchet.concrete.ReceiveOpen.finish_cached_success_publishes_same_plaintext",
	] {
		require_once(
			&snapshot.lean_ratchet_effect,
			theorem,
			"ratchet checked structural Lean anchor",
		)?;
	}
	require_once(
		&snapshot.lean_ratchet_effect_refinement,
		"theorem ReceiveFailureTrace.result_eq_entry",
		"ratchet checked structural failure-trace anchor",
	)?;
	for theorem in [
		"def ResponseRefines",
		"theorem begin_send_refines",
		"theorem SendKdf.resume_refines",
		"theorem SendSeal.finish_refines_ideal_send",
		"theorem ReceiveOpen.failure_preserves_refinement",
		"theorem ReceiveFailureTrace.preserves_refinement",
		"def OpenReplyRefines",
		"theorem begin_receive_cached_refines",
		"theorem CachedOpenRefines.finish_success_matches_ideal",
		"theorem CachedOpenRefines.finish_success_refines_of_publication",
	] {
		require_once(
			&snapshot.lean_ratchet_effect_refinement,
			theorem,
			"ratchet conditional Lean refinement anchor",
		)?;
	}

	let crypto = compact(&uncommented_pv(&snapshot.crypto)?);
	require_once(
		&crypto,
		"letfunseal_frame(",
		"ratchet ProVerif atomic seal abstraction",
	)?;
	require_once(
		&crypto,
		";open_frame(",
		"ratchet ProVerif ideal exact open abstraction",
	)?;
	let symbolic = format!(
		"{}{}",
		crypto,
		compact(&uncommented_pv(&snapshot.environment)?)
	);
	for absent in [
		"RatchetKernelSlot",
		"begin_send",
		"begin_receive",
		"ratchet_hkdf",
		"SendKdfRequested",
		"ReceiveKdfRequested",
	] {
		forbid(
			&symbolic,
			absent,
			"concrete ratchet driver step in atomic ProVerif model",
		)?;
	}
	Ok(())
}

fn validate_finite_receive_state_fixture(snapshot: &Snapshot) -> Result<(), String> {
	let control = compact(&uncommented_rust(&snapshot.core_ratchet_control)?);
	require_once(
		&control,
		"pubconstRATCHET_MAX_GAP:u64=50;",
		"finite receive core maximum gap",
	)?;
	require_once(
		&control,
		"pubconstRECEIVE_CACHE_CAPACITY:usize=RATCHET_MAX_GAPasusize;",
		"finite receive core cache capacity",
	)?;

	let plan = rust_body(&snapshot.core_ratchet_control, "plan_receive_until")?;
	require_ordered_once(
		&plan,
		&[
			"iftarget<=state.receive_sequence{returnReceivePlan{sequence:Some(target),derivations:0,};}",
			"letderivations=target-state.receive_sequence;",
			"letskipped=derivations-1;",
			"letcached=state.receive_cache.lenasu64;",
			"ifskipped>RATCHET_MAX_GAP||cached>RATCHET_MAX_GAP-skipped",
			"ReceivePlan{sequence:None,derivations:0,}",
			"ReceivePlan{sequence:Some(target),derivations,}",
		],
		"finite receive core admission plan",
	)?;

	let advance_target = rust_body(&snapshot.core_ratchet_control, "advance_receive_target")?;
	require_once(
		&advance_target,
		"letnext=state.receive_sequence+1;",
		"finite receive target counter advance",
	)?;
	require_once(
		&advance_target,
		"state:RatchetState{receive_sequence:next,..state},sequence:Some(next)",
		"finite receive target result",
	)?;
	forbid(
		&advance_target,
		".append(",
		"finite receive target cache allocation",
	)?;

	let advance_skipped_source = section_between(
		&snapshot.core_ratchet_control,
		"pub(crate) fn advance_receive(",
		"/// Outcome of authenticating a cached receive key.",
		"finite receive skipped-key advance",
	)?;
	let advance_skipped = rust_body(advance_skipped_source, "advance_receive")?;
	require_one_call(
		&advance_skipped,
		"state.receive_cache.append",
		&["next"],
		"finite receive skipped-key cache append",
	)?;
	require_once(
		&advance_skipped,
		"receive_sequence:next,receive_cache,..state",
		"finite receive skipped-key control update",
	)?;

	let finish_control = rust_body(
		&snapshot.core_ratchet_control,
		"finish_receive_with_removal",
	)?;
	require_once(
		&finish_control,
		"if!authenticated{returnReceiveFinishWithRemoval{state,disposition:ReceiveDisposition::Retained,removal:None,};}",
		"finite receive cached authentication failure neutrality",
	)?;
	require_ordered_once(
		&finish_control,
		&[
			"letlast_slot=len-1;",
			"entries[slot_index]=entries[last_slotasusize];",
			"entries[last_slotasusize]=0;",
			"len:last_slot",
			"disposition:ReceiveDisposition::Consumed",
			"target_slot:slot,last_slot",
		],
		"finite receive cached swap removal",
	)?;

	let begin_receive = rust_body(&snapshot.core_ratchet_concrete, "begin_receive")?;
	require_once(
		&begin_receive,
		"ifplan.derivations==0{letprepared=matchprepare_cached_receive(&kernel.refined,sequence){Some(prepared)=>prepared,None=>returnreceive_rejected(kernel,context),};returnReceiveEffect::ReceiveOpenRequested(ReceiveOpen{entry:kernel,context,prepared:PreparedReceive::PreparedReceiveCachedCase(prepared),});}",
		"finite receive replay and cached lookup branch",
	)?;
	require_once(
		&begin_receive,
		"letskipped=plan.derivations-1;",
		"finite receive future skipped count",
	)?;
	require_once(
		&begin_receive,
		"staged_slots:empty_material_slots(),first_slot,skipped:0,remaining,request",
		"finite receive private future staging start",
	)?;

	let receive_kdf = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveKdf<Context>",
		"impl<Context> ReceiveOpen<Context>",
		"finite receive KDF phase",
	)?;
	let resume_receive = rust_body(receive_kdf, "resume")?;
	require_once(
		&resume_receive,
		"staged_slots:self.staged_slots,target_sequence:sequence,target_material:stepped.material,first_slot:self.first_slot,skipped:self.skipped",
		"finite receive separate future target",
	)?;
	require_once(
		&resume_receive,
		"self.staged_slots[slot_index]=Some(CachedReceiveKey{sequence,material:stepped.material,});",
		"finite receive staged skipped material",
	)?;

	let pending_valid = rust_body(&snapshot.core_ratchet_refined, "pending_receive_is_valid")?;
	require_once(
		&pending_valid,
		"iflookup_receive_key(pending.committed_control,requested).is_some(){returnfalse;}",
		"finite receive target absent from committed cache",
	)?;
	require_once(
		&pending_valid,
		"letcommitted_len=pending.first_slotasusize+pending.skippedasusize;",
		"finite receive committed skipped-cache length",
	)?;
	require_once(
		&pending_valid,
		"if!(pending.committed_control.receive_cache_len()asusize==committed_len){returnfalse;}",
		"finite receive committed cache length check",
	)?;

	let prepare_cached = rust_body(&snapshot.core_ratchet_refined, "prepare_cached_receive")?;
	require_ordered_once(
		&prepare_cached,
		&[
			"lettarget_slot=matchlookup_receive_key(state.control,sequence)",
			"letlast_slot=len-1;",
			"letfinished=finish_receive_with_removal(state.control,sequence,target_slot,true);",
			"if!(removal.target_slot==target_slot){returnNone;}",
			"if!(removal.last_slot==last_slot){returnNone;}",
			"Some(PreparedCachedReceive{sequence,target_slot,last_slot,committed_control:finished.state,})",
		],
		"finite receive cached preflight",
	)?;

	let receive_open = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveOpen<Context>",
		"/// Checked restoration builder",
		"finite receive open phase",
	)?;
	let finish_open = rust_body(receive_open, "finish")?;
	require_ordered_once(
		&finish_open,
		&[
			"None=>return(self.entry,None)",
			"letmutentry=self.entry;",
			"publish_cached_receive(&mutentry.refined,prepared);",
			"publish_future_receive(&mutentry.refined,pending);",
			"(entry,Some(plaintext))",
		],
		"finite receive success-only publication",
	)?;

	let publish_cached = rust_body(&snapshot.core_ratchet_refined, "publish_cached_receive")?;
	require_ordered_once(
		&publish_cached,
		&[
			"iftarget_index==last_index{let_=state.receive_slots[last_index].take();}else{letmoved=state.receive_slots[last_index].take();state.receive_slots[target_index]=moved;}",
			"state.control=prepared.committed_control;",
		],
		"finite receive cached whole-entry publication",
	)?;

	let publish_future_source = section_between(
		&snapshot.core_ratchet_refined,
		"pub(super) fn publish_future_receive<",
		"/// Commit an already-preflighted suffix of receive steps.",
		"finite receive future publisher",
	)?;
	let publish_future = rust_body(publish_future_source, "publish_future_receive")?;
	require_ordered_once(
		&publish_future,
		&[
			"publish_future_receive_slots(state,&mutpending.staged_slots,pending.first_slot,pending.skipped,);",
			"state.receive_chain=pending.final_receive_chain;",
			"state.control=pending.committed_control;",
		],
		"finite receive future publication",
	)?;
	forbid(
		&publish_future,
		"target_material",
		"finite receive target publication",
	)?;

	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	require_once(
		&environment,
		"funreceive_cache_empty():receive_cache[data].",
		"finite receive ProVerif empty cache constructor",
	)?;
	require_once(
		&environment,
		"funreceive_cache_entry(sequence,bitstring,receive_cache):receive_cache[data].",
		"finite receive ProVerif cache-entry constructor",
	)?;
	require_once(
		&environment,
		"funreceive_state(sequence,bitstring,receive_cache):bitstring[data].",
		"finite receive ProVerif state constructor",
	)?;
	let short = section_between(
		&environment,
		"letStateNeutralFutureReceive()=",
		"letStateNeutralCapacityReceive()=",
		"finite receive short fixture",
	)?;
	let capacity = section_between(
		&environment,
		"letStateNeutralCapacityReceive()=",
		"letFailedReceiveScenario()=",
		"finite receive capacity fixture",
	)?;
	require_once(
		&environment,
		"letFailedReceiveScenario()=(StateNeutralFutureReceive()|StateNeutralCapacityReceive()).",
		"finite receive two-leg scenario composition",
	)?;

	require_once(
		short,
		"letfirst=first_sequence()inletskipped_sequence=next_sequence(first)inlettarget_sequence=next_sequence(skipped_sequence)in",
		"finite receive short sequence prefix",
	)?;
	require_once(
		short,
		"letchain_1=server_to_beacon_chain(root)inletchain_2=ratchet_next(chain_1)inletchain_3=ratchet_next(chain_2)inletchain_4=ratchet_next(chain_3)in",
		"finite receive short ratchet chain",
	)?;
	require_once(
		short,
		"letmaterial_1=ratchet_material(chain_1)inletskipped_material=ratchet_material(chain_2)inlettarget_material=ratchet_material(chain_3)in",
		"finite receive short material chain",
	)?;
	for (frame, material, sequence, plaintext) in [
		("first_frame", "material_1", "first", "RECEIVE_PAST_SECRET"),
		(
			"skipped_frame",
			"skipped_material",
			"skipped_sequence",
			"RECEIVE_SKIPPED_SECRET",
		),
		(
			"target_frame",
			"target_material",
			"target_sequence",
			"RECEIVE_TARGET_SECRET",
		),
	] {
		require_once(
			short,
			&format!(
				"let{frame}=seal_frame({material},associated_data,{sequence},sender_id,{plaintext})in"
			),
			"finite receive short honest frame",
		)?;
	}
	require_once(
		short,
		"letready_state=receive_state(first,chain_2,empty_cache)in",
		"finite receive short entry state",
	)?;
	require_once(
		short,
		"letforged_target_frame=crypto_frame(forged_frame_component(),forged_frame_component(),forged_frame_component(),target_sequence,sender_id)in",
		"finite receive short forged target frame",
	)?;
	for (sequence, plaintext) in [
		("first", "RECEIVE_PAST_SECRET"),
		("skipped_sequence", "RECEIVE_SKIPPED_SECRET"),
		("target_sequence", "RECEIVE_TARGET_SECRET"),
	] {
		require_once(
			short,
			&format!(
				"eventMessageSent(session,server_to_beacon(),{sequence},sender_id,receiver_id,{plaintext});"
			),
			"finite receive short sent message",
		)?;
	}
	require_once(
		short,
		"eventMessageReceived(session,server_to_beacon(),first,sender_id,receiver_id,first_plaintext);",
		"finite receive short first delivery",
	)?;
	require_once(
		short,
		"letfirst_plaintext=open_frame(material_1,associated_data,first,sender_id,first_candidate)in",
		"finite receive short initial open",
	)?;
	require_once(
		short,
		"ifforged_candidate=forged_target_framethen(letforged_plaintext=open_frame(target_material,associated_data,target_sequence,sender_id,forged_candidate)ineventMessageReceived(session,server_to_beacon(),target_sequence,sender_id,receiver_id,forged_plaintext)else(eventReceiveRejectedNeutral(session,target_sequence,forged_target_frame,ready_state);",
		"finite receive first exact-frame destructor rejection",
	)?;
	require_once(
		short,
		"ifrepeated_candidate=forged_target_framethen(letrepeated_plaintext=open_frame(target_material,associated_data,target_sequence,sender_id,repeated_candidate)ineventMessageReceived(session,server_to_beacon(),target_sequence,sender_id,receiver_id,repeated_plaintext)else(eventReceiveRejectionRetried(session,target_sequence,forged_target_frame,ready_state);",
		"finite receive repeated exact-frame destructor rejection",
	)?;
	require_once(
		short,
		"out(receive_snapshots,(session,target_sequence,ready_state,ready_state,chain_2,empty_cache,compromise_ack))",
		"finite receive unchanged rejection snapshot",
	)?;
	require_once(
		short,
		"letaccepted_plaintext=open_frame(target_material,associated_data,target_sequence,sender_id,accepted_candidate)in",
		"finite receive short future open",
	)?;
	require_once(
		short,
		"letcommitted_cache=receive_cache_entry(skipped_sequence,skipped_material,empty_cache)inletcommitted_state=receive_state(target_sequence,chain_4,committed_cache)in",
		"finite receive short successful skipped publication",
	)?;
	require_once(
		short,
		"eventMessageKeyCached(session,beacon_role(),server_to_beacon(),skipped_sequence,skipped_material);",
		"finite receive short skipped-key cache event",
	)?;
	require_once(
		short,
		"eventMessageReceived(session,server_to_beacon(),target_sequence,sender_id,receiver_id,accepted_plaintext);",
		"finite receive short future delivery",
	)?;
	require_once(
		short,
		"eventMessageKeyUnavailable(session,beacon_role(),server_to_beacon(),target_sequence,target_material);",
		"finite receive short target consumption",
	)?;
	require_once(
		short,
		"eventReceiveFutureAccepted(session,target_sequence,sender_id,receiver_id,accepted_plaintext,accepted_candidate,target_material,forged_target_frame,ready_state,committed_state);",
		"finite receive future acceptance",
	)?;
	require_once(
		short,
		"ifaccepted_candidate=target_framethen(eventReceiveHonestFutureDelivered(session,target_sequence,sender_id,receiver_id,accepted_plaintext,accepted_candidate,target_material,forged_target_frame,ready_state,committed_state);",
		"finite receive honest future selection and delivery",
	)?;
	require_once(
		short,
		"ifreplay_candidate=accepted_candidatethen(eventReceiveReplayRejected(session,target_sequence,sender_id,receiver_id,accepted_plaintext,accepted_candidate,target_material,forged_target_frame,ready_state,committed_state);",
		"finite receive exact accepted-frame replay",
	)?;
	require_once(
		short,
		"letdelayed_plaintext=open_frame(skipped_material,associated_data,skipped_sequence,sender_id,delayed_candidate)inletdelayed_state=receive_state(target_sequence,chain_4,empty_cache)in",
		"finite receive delayed cached-key consumption",
	)?;
	require_once(
		short,
		"eventMessageKeyUnavailable(session,beacon_role(),server_to_beacon(),skipped_sequence,skipped_material);",
		"finite receive delayed key unavailability",
	)?;
	require_once(
		short,
		"eventMessageReceived(session,server_to_beacon(),skipped_sequence,sender_id,receiver_id,delayed_plaintext);",
		"finite receive delayed delivery",
	)?;
	require_once(
		short,
		"eventReceiveDelayedCachedAccepted(session,skipped_sequence,sender_id,receiver_id,delayed_plaintext,delayed_candidate,skipped_material,committed_state,delayed_state)",
		"finite receive delayed cached acceptance",
	)?;
	forbid(
		short,
		"receive_cache_entry(target_sequence,",
		"finite receive short target retained in cache",
	)?;

	for sequence in 2..=54 {
		let previous = sequence - 1;
		require_once(
			capacity,
			&format!(
				"letcapacity_sequence_{sequence}=next_sequence(capacity_sequence_{previous})in"
			),
			"finite receive capacity sequence chain",
		)?;
	}
	for chain in 2..=55 {
		let previous = chain - 1;
		require_once(
			capacity,
			&format!("letcapacity_chain_{chain}=ratchet_next(capacity_chain_{previous})in"),
			"finite receive capacity ratchet chain",
		)?;
	}
	for material in 1..=54 {
		require_once(
			capacity,
			&format!(
				"letcapacity_material_{material}=ratchet_material(capacity_chain_{material})in"
			),
			"finite receive capacity material chain",
		)?;
	}
	for (frame, material, sequence, plaintext) in [
		(
			"capacity_first_frame",
			"capacity_material_1",
			"capacity_sequence_1",
			"capacity_first_plaintext",
		),
		(
			"maximum_gap_frame",
			"capacity_material_52",
			"capacity_sequence_52",
			"RECEIVE_MAX_GAP_SECRET",
		),
		(
			"cached_frame",
			"capacity_material_51",
			"capacity_sequence_51",
			"RECEIVE_CACHED_SECRET",
		),
		(
			"after_release_frame",
			"capacity_material_54",
			"capacity_sequence_54",
			"RECEIVE_AFTER_RELEASE_SECRET",
		),
	] {
		require_once(
			capacity,
			&format!(
				"let{frame}=seal_frame({material},capacity_associated_data,{sequence},capacity_sender_id,{plaintext})in"
			),
			"finite receive capacity honest frame",
		)?;
	}
	for (sequence, plaintext) in [
		("capacity_sequence_1", "capacity_first_plaintext"),
		("capacity_sequence_52", "RECEIVE_MAX_GAP_SECRET"),
		("capacity_sequence_51", "RECEIVE_CACHED_SECRET"),
		("capacity_sequence_54", "RECEIVE_AFTER_RELEASE_SECRET"),
	] {
		require_once(
			capacity,
			&format!(
				"eventMessageSent(capacity_session,server_to_beacon(),{sequence},capacity_sender_id,capacity_receiver_id,{plaintext});"
			),
			"finite receive capacity sent message",
		)?;
	}
	require_once(
		capacity,
		"letcapacity_rejected_frame=crypto_frame(forged_frame_component(),forged_frame_component(),forged_frame_component(),capacity_sequence_54,capacity_sender_id)in",
		"finite receive capacity rejected frame",
	)?;
	require_once(
		capacity,
		"letcapacity_first_opened=open_frame(capacity_material_1,capacity_associated_data,capacity_sequence_1,capacity_sender_id,capacity_first_candidate)in",
		"finite receive capacity initial open",
	)?;
	require_once(
		capacity,
		"letcapacity_ready_state=receive_state(capacity_sequence_1,capacity_chain_2,capacity_cache_empty)in",
		"finite receive capacity entry state",
	)?;
	require_once(
		capacity,
		"eventMessageReceived(capacity_session,server_to_beacon(),capacity_sequence_1,capacity_sender_id,capacity_receiver_id,capacity_first_opened);",
		"finite receive capacity first delivery",
	)?;
	require_once(
		capacity,
		"letmaximum_gap_plaintext=open_frame(capacity_material_52,capacity_associated_data,capacity_sequence_52,capacity_sender_id,maximum_gap_candidate)in",
		"finite receive maximum-gap open",
	)?;
	for skipped in 2..=51 {
		let previous_cache = if skipped == 2 {
			"capacity_cache_empty".to_owned()
		} else {
			format!("capacity_cache_{}", skipped - 1)
		};
		require_once(
			capacity,
			&format!(
				"eventMessageKeyCached(capacity_session,beacon_role(),server_to_beacon(),capacity_sequence_{skipped},capacity_material_{skipped});"
			),
			"finite receive maximum-gap cached-key event",
		)?;
		require_once(
			capacity,
			&format!(
				"letcapacity_cache_{skipped}=receive_cache_entry(capacity_sequence_{skipped},capacity_material_{skipped},{previous_cache})in"
			),
			"finite receive maximum-gap cache construction",
		)?;
	}
	require_once(
		capacity,
		"letmaximum_gap_state=receive_state(capacity_sequence_52,capacity_chain_53,capacity_cache_51)in",
		"finite receive maximum-gap state",
	)?;
	require_once(
		capacity,
		"eventMessageKeyUnavailable(capacity_session,beacon_role(),server_to_beacon(),capacity_sequence_52,capacity_material_52);",
		"finite receive maximum-gap target consumption",
	)?;
	require_once(
		capacity,
		"eventReceiveMaximumGapAccepted(capacity_session,capacity_sequence_52,capacity_sender_id,capacity_receiver_id,maximum_gap_plaintext,maximum_gap_candidate,capacity_material_52,capacity_ready_state,maximum_gap_state);",
		"finite receive maximum-gap acceptance",
	)?;
	require_once(
		capacity,
		"eventMessageReceived(capacity_session,server_to_beacon(),capacity_sequence_52,capacity_sender_id,capacity_receiver_id,maximum_gap_plaintext);",
		"finite receive maximum-gap delivery",
	)?;
	require_once(
		capacity,
		"eventReceiveCapacityRejected(capacity_session,capacity_sequence_54,capacity_rejected_frame,maximum_gap_state);",
		"finite receive full-cache rejection",
	)?;
	require_once(
		capacity,
		"ifcapacity_rejected_candidate=capacity_rejected_framethen(eventReceiveCapacityRejected",
		"finite receive full-cache exact-frame gate",
	)?;
	require_once(
		capacity,
		"letcached_plaintext=open_frame(capacity_material_51,capacity_associated_data,capacity_sequence_51,capacity_sender_id,cached_candidate)in",
		"finite receive cached release open",
	)?;
	require_once(
		capacity,
		"letreleased_state=receive_state(capacity_sequence_52,capacity_chain_53,capacity_cache_50)in",
		"finite receive cached capacity release",
	)?;
	require_once(
		capacity,
		"eventReceiveCachedKeyConsumed(capacity_session,capacity_sequence_51,capacity_material_51,maximum_gap_state,released_state);",
		"finite receive cached last-slot consumption event",
	)?;
	require_once(
		capacity,
		"eventMessageKeyUnavailable(capacity_session,beacon_role(),server_to_beacon(),capacity_sequence_51,capacity_material_51);",
		"finite receive cached key unavailability",
	)?;
	require_once(
		capacity,
		"eventMessageReceived(capacity_session,server_to_beacon(),capacity_sequence_51,capacity_sender_id,capacity_receiver_id,cached_plaintext);",
		"finite receive cached delivery",
	)?;
	require_once(
		capacity,
		"letafter_release_plaintext=open_frame(capacity_material_54,capacity_associated_data,capacity_sequence_54,capacity_sender_id,after_release_candidate)in",
		"finite receive after-release open",
	)?;
	require_once(
		capacity,
		"letafter_release_cache=receive_cache_entry(capacity_sequence_53,capacity_material_53,capacity_cache_50)inletafter_release_state=receive_state(capacity_sequence_54,capacity_chain_55,after_release_cache)in",
		"finite receive after-release state",
	)?;
	require_once(
		capacity,
		"eventMessageKeyCached(capacity_session,beacon_role(),server_to_beacon(),capacity_sequence_53,capacity_material_53);",
		"finite receive after-release skipped-key event",
	)?;
	require_once(
		capacity,
		"eventMessageKeyUnavailable(capacity_session,beacon_role(),server_to_beacon(),capacity_sequence_54,capacity_material_54);",
		"finite receive after-release target consumption",
	)?;
	require_once(
		capacity,
		"eventReceiveAfterCapacityReleaseAccepted(capacity_session,capacity_sequence_54,capacity_sender_id,capacity_receiver_id,after_release_plaintext,after_release_candidate,capacity_material_54,maximum_gap_state,released_state,after_release_state)",
		"finite receive after-release acceptance",
	)?;
	require_once(
		capacity,
		"eventMessageReceived(capacity_session,server_to_beacon(),capacity_sequence_54,capacity_sender_id,capacity_receiver_id,after_release_plaintext);",
		"finite receive after-release delivery",
	)?;
	for forbidden_target in ["capacity_sequence_52", "capacity_sequence_54"] {
		forbid(
			capacity,
			&format!("receive_cache_entry({forbidden_target},"),
			"finite receive target retained in capacity cache",
		)?;
	}

	let queries = compact(&uncommented_pv(&snapshot.failed_receive_queries)?);
	if snapshot
		.failed_receive_queries
		.lines()
		.filter(|line| line.trim_start().starts_with("query "))
		.count()
		!= 17
	{
		return Err("finite receive query count changed".to_owned());
	}
	for secret in [
		"RECEIVE_PAST_SECRET",
		"RECEIVE_SKIPPED_SECRET",
		"RECEIVE_TARGET_SECRET",
		"RECEIVE_MAX_GAP_SECRET",
		"RECEIVE_CACHED_SECRET",
		"RECEIVE_AFTER_RELEASE_SECRET",
	] {
		require_once(
			&queries,
			&format!("queryattacker({secret})."),
			"finite receive secrecy query",
		)?;
	}
	if count(&queries, "==>inj-event(") != 11 {
		return Err("finite receive correspondence query count changed".to_owned());
	}
	for correspondence in [
		"inj-event(ReceiveRejectionRetried(session,target_sequence,forged_frame,entry_state))==>inj-event(ReceiveRejectedNeutral(session,target_sequence,forged_frame,entry_state)).",
		"inj-event(ReceiveFutureAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state))==>inj-event(ReceiveRejectionRetried(session,target_sequence,forged_frame,entry_state)).",
		"inj-event(ReceiveHonestFutureDelivered(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state))==>inj-event(ReceiveFutureAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state)).",
		"inj-event(ReceiveFutureAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state))==>inj-event(MessageKeyUnavailable(session,beacon_role(),server_to_beacon(),target_sequence,target_material)).",
		"inj-event(ReceiveReplayRejected(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state))==>inj-event(ReceiveFutureAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,forged_frame,entry_state,committed_state)).",
		"inj-event(ReceiveDelayedCachedAccepted(session,delayed_sequence,sender,receiver,plaintext,delayed_frame,delayed_material,committed_state,final_state))==>inj-event(MessageKeyCached(session,beacon_role(),server_to_beacon(),delayed_sequence,delayed_material)).",
		"inj-event(ReceiveDelayedCachedAccepted(session,delayed_sequence,sender,receiver,plaintext,delayed_frame,delayed_material,committed_state,final_state))==>inj-event(MessageKeyUnavailable(session,beacon_role(),server_to_beacon(),delayed_sequence,delayed_material)).",
		"inj-event(ReceiveMaximumGapAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,entry_state,committed_state))==>inj-event(MessageKeyUnavailable(session,beacon_role(),server_to_beacon(),target_sequence,target_material)).",
		"inj-event(ReceiveCachedKeyConsumed(session,cached_sequence,cached_material,full_state,released_state))==>inj-event(MessageKeyUnavailable(session,beacon_role(),server_to_beacon(),cached_sequence,cached_material)).",
		"inj-event(ReceiveAfterCapacityReleaseAccepted(session,target_sequence,sender,receiver,plaintext,accepted_frame,target_material,rejected_state,released_state,committed_state))==>inj-event(MessageKeyUnavailable(session,beacon_role(),server_to_beacon(),target_sequence,target_material)).",
		"inj-event(MessageReceived(session,message_direction,message_sequence,sender,receiver,plaintext))==>inj-event(MessageSent(session,message_direction,message_sequence,sender,receiver,plaintext)).",
	] {
		require_once(
			&queries,
			correspondence,
			"finite receive exact correspondence query",
		)?;
	}

	let reachability = compact(&uncommented_pv(
		&snapshot.failed_receive_reachability_queries,
	)?);
	if snapshot
		.failed_receive_reachability_queries
		.lines()
		.filter(|line| line.trim_start().starts_with("query "))
		.count()
		!= 12
	{
		return Err("finite receive reachability query count changed".to_owned());
	}
	for event in [
		"event(ReceiveRejectedNeutral(session,target_sequence,forged_frame,entry_state)).",
		"event(ReceiveRejectionRetried(session,target_sequence,forged_frame,entry_state)).",
		"event(ReceiveFutureAccepted(session,target_sequence,sender,receiver,RECEIVE_TARGET_SECRET,accepted_frame,target_material,forged_frame,entry_state,committed_state)).",
		"event(ReceiveHonestFutureDelivered(session,target_sequence,sender,receiver,RECEIVE_TARGET_SECRET,accepted_frame,target_material,forged_frame,entry_state,committed_state)).",
		"event(ReceiveReplayRejected(session,target_sequence,sender,receiver,RECEIVE_TARGET_SECRET,accepted_frame,target_material,forged_frame,entry_state,committed_state)).",
		"event(ReceiveDelayedCachedAccepted(session,delayed_sequence,sender,receiver,RECEIVE_SKIPPED_SECRET,delayed_frame,delayed_material,committed_state,final_state)).",
		"event(ReceiveMaximumGapAccepted(session,target_sequence,sender,receiver,RECEIVE_MAX_GAP_SECRET,accepted_frame,target_material,entry_state,committed_state)).",
		"event(ReceiveCapacityRejected(session,target_sequence,rejected_frame,rejected_state)).",
		"event(ReceiveCachedKeyConsumed(session,cached_sequence,cached_material,full_state,released_state)).",
		"event(ReceiveAfterCapacityReleaseAccepted(session,target_sequence,sender,receiver,RECEIVE_AFTER_RELEASE_SECRET,accepted_frame,target_material,rejected_state,released_state,committed_state)).",
	] {
		require_once(
			&reachability,
			event,
			"finite receive exact event reachability query",
		)?;
	}

	Ok(())
}

fn validate_registration_lifecycle(snapshot: &Snapshot) -> Result<(), String> {
	let core = compact(&uncommented_rust(&snapshot.core_pqxdh)?);
	for (wanted, label) in [
		(
			"pubconstSIGN_PUBLIC_KEY_SIZE:usize=32;",
			"registration replay identity width",
		),
		(
			"pubconstX25519_PUBLIC_KEY_SIZE:usize=32;",
			"registration replay one-time-key width",
		),
		(
			"pubconstREGISTRATION_ID_SIZE:usize=SIGN_PUBLIC_KEY_SIZE+X25519_PUBLIC_KEY_SIZE;",
			"registration replay identifier width expression",
		),
		(
			"const_:()=assert!(REGISTRATION_ID_SIZE==64);",
			"registration replay identifier 64-byte assertion",
		),
		(
			"pubfnregistration_id(&self)->RegistrationId{letbytes:[u8;REGISTRATION_ID_SIZE]=core::array::from_fn(|i|{ifi<SIGN_PUBLIC_KEY_SIZE{self.beacon_identity_public_key[i]}else{self.beacon_one_time_public_key[i-SIGN_PUBLIC_KEY_SIZE]}});RegistrationId{bytes}}",
			"registration replay identity-then-one-time layout",
		),
		(
			"pubfnregistration_id(registration:&VerifiedInitKex)->RegistrationId{registration.registration_id()}",
			"registration replay identifier wrapper",
		),
		(
			"pubstructBeaconStart{pubstate:BeaconInitSent,pubmessage:InitKex,}",
			"registration beacon-start result typestate",
		),
	] {
		require_once(&core, wanted, label)?;
	}
	let core_start = rust_body(&snapshot.core_pqxdh, "beacon_start")?;
	require_once(
		&core_start,
		"state:BeaconInitSent{expected_server_binding:state.expected_server_binding,beacon_identity_public_key:inputs.identity_public_key,}",
		"registration beacon-start Fresh-to-InitSent mapping",
	)?;

	let extraction = compact(&uncommented_pv(&snapshot.extraction)?);
	require_once(
		&extraction,
		"reducforallidentity:bitstring,prekey:bitstring,one_time:bitstring,pq:bitstring;beaconcrypt_core__pqxdh__registration_id(beaconcrypt_core__pqxdh__VerifiedInitKex(identity,prekey,one_time,pq))=beaconcrypt_core__pqxdh__RegistrationId(registration_identifier(identity,one_time)).",
		"registration replay ProVerif identity/one-time projection",
	)?;

	let beacon_source = compact(&uncommented_rust(&snapshot.adapter_beacon)?);
	let beacon_new = rust_body(&snapshot.adapter_beacon, "new")?;
	for (wanted, label) in [
		(
			"identity_key:crypto_sign::KeyPair::generate().unwrap()",
			"registration Beacon identity generation",
		),
		(
			"state:BeaconState::Fresh{control:verified_pqxdh::BeaconFresh::new(verified_pqxdh::ServerBinding{identity_public_key:*id.as_bytes(),identity_key_id:server_kid,}),prekey:crypto_kx::KeyPair::generate().unwrap(),pq_key:crypto_kem::mlkem768::KeyPair::generate().unwrap(),}",
			"registration Beacon Fresh material co-location",
		),
	] {
		require_once(&beacon_new, wanted, label)?;
	}
	for variant in [
		"Fresh",
		"FreshWithCoins",
		"InitSent",
		"Established",
		"Aborted",
	] {
		require(
			&beacon_source,
			&format!("{variant}{{"),
			"registration Beacon state variant",
		)?;
	}

	let bundle = rust_body(&snapshot.adapter_beacon, "get_registration_bundle")?;
	for (wanted, label) in [
		(
			"letmutgenerated_onetime=ifmatches!(&self.state,BeaconState::Fresh{..}){Some(crypto_kx::KeyPair::generate().ok()?)}else{None};",
			"registration Fresh one-time generation",
		),
		(
			"BeaconState::Fresh{control,prekey,pq_key,}=>(*control,prekey.public_key.as_bytes().try_into().ok()?,*pq_key.public_key.as_bytes(),generated_onetime.as_ref()?.public_key.as_bytes().try_into().ok()?,)",
			"registration Fresh material selection",
		),
		(
			"BeaconState::FreshWithCoins{control,prekey,onetime_key,pq_key,}=>(*control,prekey.public_key.as_bytes().try_into().ok()?,*pq_key.public_key.as_bytes(),onetime_key.public_key.as_bytes().try_into().ok()?,)",
			"registration FreshWithCoins material selection",
		),
		("_=>returnNone,", "registration ineligible-state rejection"),
		(
			"letstarted=verified_pqxdh::beacon_start(control,verified_pqxdh::BeaconStartInputs{identity_public_key:*self.identity_pk().as_bytes(),prekey_public_key:prekey_public,pq_public_key:pq_public,},verified_pqxdh::BeaconCoins{one_time_public_key:onetime_public,},);",
			"registration Beacon-start input mapping",
		),
		(
			"letmutmsg=TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();",
			"registration typed InitKex builder",
		),
		(
			"bundle.set_identity_key(started.message.identity_key());",
			"registration serialized identity field",
		),
		(
			"bundle.set_pre_key(&prekey_sig);",
			"registration serialized prekey field",
		),
		(
			"bundle.set_one_time_key(&onetime_sig);",
			"registration serialized one-time field",
		),
		(
			"bundle.set_pq_key(&pq_sig);",
			"registration serialized PQ field",
		),
		(
			"capnp::serialize::write_message(&mutbuffer,msg.borrow_inner()).ok()?;",
			"registration completed InitKex serialization",
		),
		(
			"BeaconState::Fresh{prekey,pq_key,..}=>{letSome(onetime_key)=generated_onetime.take()else{self.state=BeaconState::Fresh{control,prekey,pq_key,};returnNone;};self.state=BeaconState::InitSent{control:started.state,prekey,onetime_key,pq_key,};}",
			"registration Fresh success transition and restoration",
		),
		(
			"BeaconState::FreshWithCoins{prekey,onetime_key,pq_key,..}=>{self.state=BeaconState::InitSent{control:started.state,prekey,onetime_key,pq_key,};}",
			"registration FreshWithCoins success transition",
		),
		("Some(buffer)", "registration serialized bundle return"),
	] {
		require_once(&bundle, wanted, label)?;
	}
	require_ordered(
		&bundle,
		&[
			"capnp::serialize::write_message(&mutbuffer,msg.borrow_inner()).ok()?;",
			"letprevious=std::mem::replace(&mutself.state,fallback);",
			"self.state=BeaconState::InitSent{",
			"Some(buffer)",
		],
		"registration serialization-to-InitSent order",
	)?;
	let replace = bundle
		.find("letprevious=std::mem::replace(&mutself.state,fallback);")
		.ok_or_else(|| "missing registration Beacon state replacement".to_owned())?;
	if bundle[..replace].contains("self.state=BeaconState::") {
		return Err("registration Beacon state changed before successful serialization".to_owned());
	}
	if bundle[replace..].contains('?') {
		return Err("registration fallible work moved after state replacement".to_owned());
	}
	for (constructor, expected) in [
		("self.state=BeaconState::Fresh{", 1),
		("self.state=BeaconState::FreshWithCoins{", 1),
		("self.state=BeaconState::InitSent{", 2),
		("self.state=BeaconState::Established{", 1),
	] {
		if count(&beacon_source, constructor) != expected {
			return Err(format!(
				"registration Beacon eligible-state publication graph changed: {constructor}"
			));
		}
	}
	let new_one_time = rust_body(&snapshot.adapter_beacon, "new_onetime_keypair")?;
	require_once(
		&new_one_time,
		"letcontrol=match&self.state{BeaconState::Fresh{control,..}=>*control,_=>returnNone,};",
		"registration post-Init one-time regeneration rejection",
	)?;
	let abort = rust_body(&snapshot.adapter_beacon, "abort_registration")?;
	require_once(
		&abort,
		"self.state=BeaconState::Aborted{control:verified_pqxdh::beacon_abort_init(control),};",
		"registration InitSent abort transition",
	)?;
	let delete_one_time = rust_body(&snapshot.adapter_beacon, "delete_onetime_keypair")?;
	require_once(
		&delete_one_time,
		"BeaconState::InitSent{control,..}=>BeaconState::Aborted{control:verified_pqxdh::beacon_abort_init(control),}",
		"registration InitSent one-time deletion transition",
	)?;
	let delete_pq = rust_body(&snapshot.adapter_beacon, "delete_pq_keypair")?;
	require_once(
		&delete_pq,
		"BeaconState::InitSent{control,..}=>{Some(verified_pqxdh::beacon_abort_init(*control))}",
		"registration InitSent PQ deletion transition",
	)?;
	require_once(
		&delete_pq,
		"self.state=BeaconState::Aborted{control};",
		"registration PQ deletion terminal state",
	)?;
	let finish = rust_body(&snapshot.adapter_beacon, "finish_registration")?;
	for (wanted, label) in [
		(
			"letcontrol=match&self.state{BeaconState::InitSent{control,..}=>*control,_=>returnNone,};",
			"registration finish InitSent gate",
		),
		(
			"letSome((authenticated,associated_data,ratchet,plaintext))=stagedelse{self.abort_registration(control);returnNone;};",
			"registration failed finish abort",
		),
		(
			"ifself.server_kid()!=server_kid{self.abort_registration(control);returnNone;}",
			"registration server-key-ID mismatch abort",
		),
		(
			"ifself.server_id.as_bytes()!=&server_binding.identity_public_key{self.abort_registration(control);returnNone;}",
			"registration server-identity mismatch abort",
		),
		(
			"self.state=BeaconState::Established{control:verified_pqxdh::beacon_commit(authenticated),associated_data,ratchet,};",
			"registration successful finish Established transition",
		),
	] {
		require_once(&finish, wanted, label)?;
	}
	forbid(
		&finish,
		"self.state=BeaconState::Fresh",
		"registration finish reset to eligible state",
	)?;

	let server_source = compact(&uncommented_rust(&snapshot.adapter_server)?);
	for (wanted, label) in [
		(
			"known_ids:HashMap<u64,EstablishedRemote<crypto_sign::PublicKey>>",
			"registration numeric peer map",
		),
		(
			"consumed_registrations:HashSet<[u8;verified_pqxdh::REGISTRATION_ID_SIZE]>",
			"registration consumed-ID set",
		),
	] {
		require_once(&server_source, wanted, label)?;
	}
	let server = rust_body(&snapshot.adapter_server, "get_shared_secret")?;
	for (wanted, label) in [
		(
			"letregistration_id=*verified_pqxdh::registration_id(&verified_registration).as_bytes();",
			"registration Server ID source",
		),
		(
			"letregistration_status=ifself.consumed_registrations.contains(&registration_id){verified_pqxdh::RegistrationStatus::Consumed}else{verified_pqxdh::RegistrationStatus::Fresh};",
			"registration Server replay-status polarity",
		),
		(
			"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
			"registration Server replay-status gate",
		),
		(
			"self.consumed_registrations.try_reserve(1).ok()?;",
			"registration Server consumed-set reservation",
		),
		(
			"letinserted=self.consumed_registrations.insert(registration_id);",
			"registration Server exact-ID consumption",
		),
		(
			"letmutsecrets=shared_secrets(dh1,dh2,dh3,dh4,&kem_shared)?;",
			"registration Server complete post-validation PQXDH inputs",
		),
		(
			"Some(RegistrationOutput{derived_secret,control:pending,})",
			"registration Server pending output",
		),
	] {
		require_once(&server, wanted, label)?;
	}
	require_ordered_once(
		&server,
		&[
			"letregistration_id=*verified_pqxdh::registration_id(&verified_registration).as_bytes();",
			"letregistration_status=ifself.consumed_registrations.contains(&registration_id)",
			"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
			"self.consumed_registrations.try_reserve(1).ok()?;",
			"letephemeral=crypto_kx::KeyPair::generate().ok()?;",
			"let(kem_ciphertext,kem_shared)=crypto_kem::mlkem768::encapsulate(&pq_pub).ok()?;",
			"letdh1:DhSecret=crypto_scalarmult::scalarmult(",
			"letdh2:DhSecret=crypto_scalarmult::scalarmult(",
			"letdh3:DhSecret=crypto_scalarmult::scalarmult(",
			"letdh4:DhSecret=crypto_scalarmult::scalarmult(",
			"letmutsecrets=shared_secrets(dh1,dh2,dh3,dh4,&kem_shared)?;",
			"letaccepted=verified_pqxdh::server_accept(",
			"letderived_secret=derive_root_key_input(pending.root_key_input_mut())?;",
			"letinserted=self.consumed_registrations.insert(registration_id);",
			"Some(RegistrationOutput{",
		],
		"registration Server validate-reserve-derive-consume order",
	)?;
	let accept_calls = all_arguments(&server, "verified_pqxdh::server_accept")?;
	if accept_calls.len() != 1
		|| accept_calls[0].get(1).map(String::as_str) != Some("verified_registration")
		|| accept_calls[0].get(2).map(String::as_str) != Some("registration_status")
	{
		return Err(format!(
			"registration Server accepted registration/status mapping changed: {accept_calls:?}"
		));
	}
	let insert = server
		.find("letinserted=self.consumed_registrations.insert(registration_id);")
		.ok_or_else(|| "missing registration Server consumption insertion".to_owned())?;
	if count(&server, "self.consumed_registrations.insert(") != 1 {
		return Err("registration Server consumed-ID insertion family count changed".to_owned());
	}
	if server[insert..].contains('?') {
		return Err("registration fallible work moved after consumption insertion".to_owned());
	}
	if server[insert..].contains("returnNone") {
		return Err("registration explicit failure moved after consumption insertion".to_owned());
	}
	let response = rust_body(&snapshot.adapter_server, "build_registration_response")?;
	forbid(
		&response,
		"consumed_registrations",
		"registration replay-set mutation during later response construction",
	)?;

	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	let guard = section_between(
		&environment,
		"letRegistrationReplayGuard(",
		"letHonestBeacon(",
		"registration replay guard",
	)?;
	for (wanted, label) in [
		(
			"in(replay_requests,(=beacon_identity,accepted_init:beaconcrypt_core__pqxdh__t_InitKex,accepted_registration_id:beaconcrypt_core__pqxdh__t_RegistrationId,first_reply:channel));",
			"registration replay first public input",
		),
		(
			"eventRegistrationConsumed(server_identity,beacon_identity,accepted_init,accepted_registration_id,origin);",
			"registration replay consumed event",
		),
		(
			"out(first_reply,replay_fresh());",
			"registration replay first Fresh reply",
		),
		(
			"!in(replay_requests,(=beacon_identity,replay_init:beaconcrypt_core__pqxdh__t_InitKex,replay_registration_id:beaconcrypt_core__pqxdh__t_RegistrationId,replay_reply:channel));",
			"registration replay replicated later input",
		),
		(
			"out(replay_reply,replay_consumed()).",
			"registration replay later Consumed reply",
		),
	] {
		require_once(guard, wanted, label)?;
	}
	forbid(
		guard,
		"!in(replay_requests,(=beacon_identity,accepted_init",
		"registration replay first input replication",
	)?;
	require_ordered(
		guard,
		&[
			"in(replay_requests,(",
			"eventRegistrationConsumed(",
			"out(first_reply,replay_fresh());",
			"!in(replay_requests,(",
			"out(replay_reply,replay_consumed()).",
		],
		"registration replay Fresh-to-Consumed owner order",
	)?;

	let honest = section_between(
		&environment,
		"letHonestBeacon(",
		"letMaliciousBeacon(",
		"registration honest Beacon role",
	)?;
	require_once(
		honest,
		"RegistrationReplayGuard(server_identity,beacon_identity,registration_session)",
		"registration honest replay owner",
	)?;
	forbid(
		honest,
		"!RegistrationReplayGuard",
		"registration replicated honest replay owner",
	)?;
	require_once(
		honest,
		"out(c,signed_init_kex(tag_ed25519(beacon_identity),sign(tag_x25519_prekey(beacon_prekey),beacon_identity_secret),sign(tag_x25519_one_time(beacon_one_time),beacon_identity_secret),sign(tag_mlkem768(beacon_pq),beacon_identity_secret)));",
		"registration honest single signed bundle",
	)?;
	forbid(
		honest,
		"!out(c,signed_init_kex(",
		"registration replicated honest signed bundle",
	)?;
	require_once(
		honest,
		"RegistrationReplayGuard(server_identity,beacon_identity,registration_session)|out(c,signed_init_kex(",
		"registration honest parallel bundle-and-guard topology",
	)?;
	if count(honest, "RegistrationReplayGuard(") != 1 {
		return Err("registration honest replay-owner family count changed".to_owned());
	}
	if count(honest, "out(c,signed_init_kex(") != 1 {
		return Err("registration honest signed-bundle family count changed".to_owned());
	}

	let server_role = section_between(
		&environment,
		"letServer(",
		"letMaliciousServer()",
		"registration honest Server role",
	)?;
	require_once(
		server_role,
		"out(replay_requests,(beacon_identity,core_init,registration_id,replay_reply));",
		"registration Server public replay request",
	)?;
	require_ordered_once(
		server_role,
		&[
			"letroot=pqxdh_root(",
			"out(replay_requests,(beacon_identity,core_init,registration_id,replay_reply));",
			"in(replay_reply,replay_result:replay_status);",
			"ifreplay_result=replay_fresh()then",
			"eventServerAccepted(",
			"in(c,registration_control:bitstring);",
			"ifregistration_control=registration_abort(registration_id)then",
			"eventServerResponseAborted(",
		],
		"registration symbolic derive-consume-accept-abort order",
	)?;

	let malicious_server = section_between(
		&environment,
		"letMaliciousServer()",
		"letKeepBeaconStatePrivate()",
		"registration malicious Server role",
	)?;
	for forbidden in [
		"replay_requests",
		"RegistrationReplayGuard",
		"replay_fresh",
		"replay_consumed",
		"RegistrationConsumed",
	] {
		forbid(
			malicious_server,
			forbidden,
			"registration malicious replay guard",
		)?;
	}
	require_once(
		malicious_server,
		"letregistration_continue(=registration_id)=registration_controlin",
		"registration malicious direct response path",
	)?;

	let hb49 = compact(&uncommented_pv(&snapshot.mlkem_reencapsulation_control)?);
	let epoch_calls = [
		(
			"letbundle_old=kem_epoch_bundle(",
			"pqpk_old",
			"registration HB-49 old bundle",
		),
		(
			"letbundle_new=kem_epoch_bundle(",
			"pqpk_new",
			"registration HB-49 new bundle",
		),
	];
	for (marker, pq_key, label) in epoch_calls {
		let arguments = arguments_after(&hb49, marker)?;
		let expected = [
			"tag_ed25519(beacon_identity)".to_owned(),
			"sign(tag_x25519_prekey(beacon_prekey),beacon_identity_secret)".to_owned(),
			"sign(tag_x25519_one_time(beacon_one_time),beacon_identity_secret)".to_owned(),
			format!("sign(tag_mlkem768({pq_key}),beacon_identity_secret)"),
		];
		if arguments != expected {
			return Err(format!("{label} changed: {arguments:?}"));
		}
	}
	require_ordered_once(
		&hb49,
		&[
			"newpqsk_old:bitstring;",
			"newpqsk_new:bitstring;",
			"letpqpk_old=mlkem_public(pqsk_old)in",
			"letpqpk_new=mlkem_public(pqsk_new)in",
			"letbundle_old=kem_epoch_bundle(",
			"letbundle_new=kem_epoch_bundle(",
			"out(kem_multi_epoch_channel,bundle_old);",
			"out(kem_multi_epoch_channel,bundle_new);",
		],
		"registration HB-49 same-classical-material PQ-only rotation fixture",
	)?;

	Ok(())
}

fn validate_initial_ratchet_fidelity(snapshot: &Snapshot) -> Result<(), String> {
	let shared_source = compact(&uncommented_rust(&snapshot.adapter_shared)?);
	for (wanted, label) in [
		(
			"pubconstKEX_KDF_OUT_LEN:usize=32usize;",
			"initial ratchet derived-root output width",
		),
		(
			"const_:()=assert!(KEX_KDF_OUT_LEN==KDF_STATE_SIZE);",
			"initial ratchet derived-root width link",
		),
		(
			"pubtypeKexDerivedSecret=SecretArr<KDF_STATE_SIZE,systems::Pqxdh,roles::DerivedSecret>;",
			"initial ratchet derived-root alias",
		),
		(
			"pubfnas_array(&self)->&[u8;S]{",
			"initial ratchet derived-root accessor signature",
		),
	] {
		require_once(&shared_source, wanted, label)?;
	}
	let as_array = rust_body(&snapshot.adapter_shared, "as_array")?;
	if as_array != "&self.data" {
		return Err(format!(
			"initial ratchet derived-root accessor body changed: {as_array}"
		));
	}

	let server_source = compact(&uncommented_rust(&snapshot.adapter_server)?);
	require_once(
		&server_source,
		"pubstructRegistrationOutput{pub(crate)derived_secret:KexDerivedSecret,pub(crate)control:beaconcrypt_core::pqxdh::PendingServerRegistration,}",
		"initial ratchet RegistrationOutput storage",
	)?;
	for (wanted, label) in [
		(
			"fnget_shared_secret(&mutself,buffer:&[u8])->Option<RegistrationOutput>{",
			"initial ratchet Server RegistrationOutput return signature",
		),
		(
			"fnbuild_registration_response(&mutself,reg_out:RegistrationOutput,data:Option<&[u8]>,)->Option<RegResponse>{",
			"initial ratchet Server RegistrationOutput by-value consumer signature",
		),
	] {
		require_once(&server_source, wanted, label)?;
	}
	let get_shared_secret = rust_body(&snapshot.adapter_server, "get_shared_secret")?;
	require_ordered_once(
		&get_shared_secret,
		&[
			"letderived_secret=derive_root_key_input(pending.root_key_input_mut())?;",
			"Some(RegistrationOutput{derived_secret,control:pending,})",
		],
		"initial ratchet Server derived-root output",
	)?;
	if count(&get_shared_secret, "letderived_secret=") != 1 {
		return Err("initial ratchet Server derived-root binding count changed".to_owned());
	}
	let server_response = rust_body(&snapshot.adapter_server, "build_registration_response")?;
	require_once(
		&server_response,
		"letRegistrationOutput{derived_secret,control:pending,}=reg_out;",
		"initial ratchet Server RegistrationOutput destructure",
	)?;
	require_one_call(
		&server_response,
		"start_server_candidate_ratchet_kdf",
		&["&candidate", "derived_secret.as_array()"],
		"initial ratchet Server root and candidate handoff",
	)?;
	require_one_call(
		&server_response,
		"finish_initial_ratchet_kdf",
		&["pending"],
		"initial ratchet Server pending completion",
	)?;
	require_one_call(
		&server_response,
		"RatchetManager::from_kernel",
		&["finish_initial_ratchet_kdf(pending)"],
		"initial ratchet Server kernel wrapper",
	)?;
	require_ordered_once(
		&server_response,
		&[
			"letRegistrationOutput{derived_secret,control:pending,}=reg_out;",
			"letpending=start_server_candidate_ratchet_kdf(&candidate,derived_secret.as_array());",
			"letmutratchet=RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending));",
			"letencrypted=encrypt_message_with_ratchet(",
		],
		"initial ratchet Server cross-method root-to-seal flow",
	)?;
	if count(&server_response, "letderived_secret=") != 0 {
		return Err("initial ratchet Server derived root was shadowed after handoff".to_owned());
	}
	if count(&server_response, "letpending=") != 1 {
		return Err("initial ratchet Server KDF pending binding count changed".to_owned());
	}

	let beacon_finish = rust_body(&snapshot.adapter_beacon, "finish_registration")?;
	require_one_call(
		&beacon_finish,
		"derive_root_key_input",
		&["candidate.root_key_input_mut()"],
		"initial ratchet Beacon candidate-root derivation",
	)?;
	require_one_call(
		&beacon_finish,
		"start_beacon_candidate_ratchet_kdf",
		&["&candidate", "derived_secret.as_array()"],
		"initial ratchet Beacon root and candidate handoff",
	)?;
	require_one_call(
		&beacon_finish,
		"finish_initial_ratchet_kdf",
		&["pending"],
		"initial ratchet Beacon pending completion",
	)?;
	require_one_call(
		&beacon_finish,
		"RatchetManager::from_kernel",
		&["finish_initial_ratchet_kdf(pending)"],
		"initial ratchet Beacon kernel wrapper",
	)?;
	require_ordered_once(
		&beacon_finish,
		&[
			"letderived_secret=derive_root_key_input(candidate.root_key_input_mut())?;",
			"letpending=start_beacon_candidate_ratchet_kdf(&candidate,derived_secret.as_array());",
			"letmutratchet=RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending));",
			"letdecrypted=decrypt_message_with_ratchet(",
		],
		"initial ratchet Beacon root-to-open flow",
	)?;
	if count(&beacon_finish, "letderived_secret=") != 1 {
		return Err("initial ratchet Beacon derived-root binding count changed".to_owned());
	}
	if count(&beacon_finish, "letpending=") != 1 {
		return Err("initial ratchet Beacon KDF pending binding count changed".to_owned());
	}

	let core_pqxdh = compact(&uncommented_rust(&snapshot.core_pqxdh)?);
	for (wanted, label) in [
		(
			"pubconstRATCHET_CHAIN_SIZE:usize=crate::ratchet::RATCHET_CHAIN_SIZE;",
			"initial ratchet root and chain width",
		),
		(
			"pubconstINITIAL_RATCHET_KDF_OUTPUT_SIZE:usize=RATCHET_CHAIN_SIZE*2;",
			"initial ratchet output-width expression",
		),
		(
			"const_:()=assert!(INITIAL_RATCHET_KDF_OUTPUT_SIZE==64);",
			"initial ratchet output 64-byte assertion",
		),
		(
			"constBEACON_RATCHETS:RatchetInitialization=RatchetInitialization{send_offset:RATCHET_CHAIN_SIZEasu8,receive_offset:0,};",
			"initial ratchet Beacon role offsets",
		),
		(
			"constSERVER_RATCHETS:RatchetInitialization=RatchetInitialization{send_offset:0,receive_offset:RATCHET_CHAIN_SIZEasu8,};",
			"initial ratchet Server role offsets",
		),
	] {
		require_once(&core_pqxdh, wanted, label)?;
	}
	let beacon_candidate = section_between(
		&core_pqxdh,
		"implBeaconRegistrationCandidate{",
		"pubstructBeaconFinishInputs",
		"initial ratchet Beacon candidate impl",
	)?;
	require_once(
		beacon_candidate,
		"pubconstfnratchet_initialization(&self)->RatchetInitialization{BEACON_RATCHETS}",
		"initial ratchet Beacon candidate role",
	)?;
	let server_candidate = section_between(
		&core_pqxdh,
		"implServerRegistrationCandidate{",
		"pubenumKeyIdAvailability",
		"initial ratchet Server candidate impl",
	)?;
	require_once(
		server_candidate,
		"pubconstfnratchet_initialization(&self)->RatchetInitialization{SERVER_RATCHETS}",
		"initial ratchet Server candidate role",
	)?;
	let split = rust_body(&snapshot.core_pqxdh, "split_initial_ratchet_kdf_output")?;
	for (wanted, label) in [
		(
			"letleft=core::array::from_fn(|i|output[i]);",
			"initial ratchet left 0..32 slice",
		),
		(
			"letright=core::array::from_fn(|i|output[i+RATCHET_CHAIN_SIZE]);",
			"initial ratchet right 32..64 slice",
		),
		(
			"ifinitialization.send_offset==0{InitialRatchetChains{send_chain:crate::ratchet::RatchetChain::from_bytes(left),receive_chain:crate::ratchet::RatchetChain::from_bytes(right),}}else{InitialRatchetChains{send_chain:crate::ratchet::RatchetChain::from_bytes(right),receive_chain:crate::ratchet::RatchetChain::from_bytes(left),}}",
			"initial ratchet role-ordered split",
		),
	] {
		require_once(&split, wanted, label)?;
	}

	let core_ratchet = compact(&uncommented_rust(&snapshot.core_ratchet)?);
	for (wanted, label) in [
		(
			"pubconstRATCHET_CHAIN_SIZE:usize=32;",
			"initial ratchet request input width",
		),
		(
			"pubconstSYM_RATCHET_INFO_SIZE:usize=41;",
			"initial ratchet request label width",
		),
		(
			"pubconstSYM_RATCHET_INFO:&[u8;SYM_RATCHET_INFO_SIZE]=b\"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305\";",
			"initial ratchet request label",
		),
		(
			"pubconstRATCHET_KDF_OUTPUT_SIZE:usize=crate::commitment::AEAD_KEY_SIZE+RATCHET_CHAIN_SIZE+crate::commitment::AEAD_NONCE_SIZE;",
			"initial ratchet distinct step-response width expression",
		),
		(
			"const_:()=assert!(RATCHET_KDF_OUTPUT_SIZE==76);",
			"initial ratchet distinct 76-byte step response",
		),
		(
			"pubstructSymmetricRatchetKdfRequest{input:[u8;RATCHET_CHAIN_SIZE],info:[u8;SYM_RATCHET_INFO_SIZE],}",
			"initial ratchet request field types",
		),
		(
			"pubstructRatchetKdfResponse{bytes:[u8;RATCHET_KDF_OUTPUT_SIZE],}",
			"initial ratchet distinct step-response type",
		),
	] {
		require_once(&core_ratchet, wanted, label)?;
	}
	let request_new = rust_body(&snapshot.core_ratchet, "new")?;
	require_once(
		&request_new,
		"Self{input,info:*SYM_RATCHET_INFO,}",
		"initial ratchet exact fixed-domain request construction",
	)?;
	let request_input = rust_body(&snapshot.core_ratchet, "input")?;
	if request_input != "&self.input" {
		return Err(format!(
			"initial ratchet request input accessor changed: {request_input}"
		));
	}
	let request_info = rust_body(&snapshot.core_ratchet, "info")?;
	if request_info != "&self.info" {
		return Err(format!(
			"initial ratchet request info accessor changed: {request_info}"
		));
	}

	let core_concrete = compact(&uncommented_rust(&snapshot.core_pqxdh_concrete)?);
	let pending_declaration = section_between(
		&core_concrete,
		"#[must_use=\"theinitialratchetKDFrequestmustbeperformedorthephaseexplicitlydropped\"]",
		"implInitialRatchetKdfPending",
		"initial ratchet pending declaration",
	)?;
	require_once(
		pending_declaration,
		"pubstructInitialRatchetKdfPending{request:SymmetricRatchetKdfRequest,initialization:RatchetInitialization,}",
		"initial ratchet pending fields",
	)?;
	for forbidden in [
		"derive(Clone",
		"derive(Copy",
		"derive(Clone,Copy",
		"derive(Copy,Clone",
	] {
		forbid(
			pending_declaration,
			forbidden,
			"initial ratchet pending Clone/Copy derivation",
		)?;
	}
	for forbidden in [
		"implCloneforInitialRatchetKdfPending",
		"implCopyforInitialRatchetKdfPending",
	] {
		forbid(
			&core_concrete,
			forbidden,
			"initial ratchet pending Clone/Copy implementation",
		)?;
	}
	let response_declaration = section_between(
		&core_concrete,
		"#[must_use=\"theinitialratchetKDFresponsemustresumeitspendingphase\"]",
		"implInitialRatchetKdfResponse",
		"initial ratchet response declaration",
	)?;
	for forbidden in ["pending:", "request:", "initialization:"] {
		forbid(
			response_declaration,
			forbidden,
			"initial ratchet response falsely gains type-level provenance",
		)?;
	}
	require_once(
		response_declaration,
		"pubstructInitialRatchetKdfResponse{bytes:[u8;INITIAL_RATCHET_KDF_OUTPUT_SIZE],}",
		"initial ratchet distinct 64-byte response type",
	)?;
	let pending_request = rust_body(&snapshot.core_pqxdh_concrete, "request")?;
	if pending_request != "&self.request" {
		return Err(format!(
			"initial ratchet pending request accessor changed: {pending_request}"
		));
	}
	let response_from_bytes = rust_body(&snapshot.core_pqxdh_concrete, "from_bytes")?;
	if response_from_bytes != "Self{bytes}" {
		return Err(format!(
			"initial ratchet response byte constructor changed: {response_from_bytes}"
		));
	}
	let response_bytes = rust_body(&snapshot.core_pqxdh_concrete, "as_bytes")?;
	if response_bytes != "&self.bytes" {
		return Err(format!(
			"initial ratchet response bytes accessor changed: {response_bytes}"
		));
	}
	let start_initial = rust_body(&snapshot.core_pqxdh_concrete, "start_initial_ratchet_kdf")?;
	require_once(
		&start_initial,
		"InitialRatchetKdfPending{request:SymmetricRatchetKdfRequest::new(*root),initialization,}",
		"initial ratchet exact root request and initialization",
	)?;
	for (wanted, label) in [
		(
			"pubfnstart_initial_ratchet_kdf(root:&[u8;RATCHET_CHAIN_SIZE],initialization:RatchetInitialization,)->InitialRatchetKdfPending{",
			"initial ratchet typed base start signature",
		),
		(
			"pubfnstart_beacon_candidate_ratchet_kdf(candidate:&BeaconRegistrationCandidate,root:&[u8;RATCHET_CHAIN_SIZE],)->InitialRatchetKdfPending{",
			"initial ratchet typed Beacon candidate start signature",
		),
		(
			"pubfnstart_server_candidate_ratchet_kdf(candidate:&ServerRegistrationCandidate,root:&[u8;RATCHET_CHAIN_SIZE],)->InitialRatchetKdfPending{",
			"initial ratchet typed Server candidate start signature",
		),
	] {
		require_once(&core_concrete, wanted, label)?;
	}
	let resume_initial = rust_body(&snapshot.core_pqxdh_concrete, "resume_initial_ratchet_kdf")?;
	require_one_call(
		&resume_initial,
		"split_initial_ratchet_kdf_output",
		&["response.as_bytes()", "pending.initialization"],
		"initial ratchet response split with same pending plan",
	)?;
	require_one_call(
		&resume_initial,
		"ConcreteRatchetKernel::new",
		&["send_chain", "receive_chain"],
		"initial ratchet kernel chain order",
	)?;
	require_ordered_once(
		&resume_initial,
		&[
			"letchains=split_initial_ratchet_kdf_output(response.as_bytes(),pending.initialization);",
			"let(send_chain,receive_chain)=chains.into_parts();",
			"ConcreteRatchetKernel::new(send_chain,receive_chain)",
		],
		"initial ratchet response-to-kernel flow",
	)?;
	for (function, expected, label) in [
		(
			"start_beacon_ratchet_kdf",
			"start_initial_ratchet_kdf(root,BEACON_RATCHETS)",
			"initial ratchet direct Beacon role start",
		),
		(
			"start_server_ratchet_kdf",
			"start_initial_ratchet_kdf(root,SERVER_RATCHETS)",
			"initial ratchet direct Server role start",
		),
		(
			"start_beacon_candidate_ratchet_kdf",
			"start_initial_ratchet_kdf(root,candidate.ratchet_initialization())",
			"initial ratchet Beacon candidate role start",
		),
		(
			"start_server_candidate_ratchet_kdf",
			"start_initial_ratchet_kdf(root,candidate.ratchet_initialization())",
			"initial ratchet Server candidate role start",
		),
	] {
		let body = rust_body(&snapshot.core_pqxdh_concrete, function)?;
		require_once(&body, expected, label)?;
	}

	let finish = rust_body(&snapshot.adapter_ratchet, "finish_initial_ratchet_kdf")?;
	require_one_call(
		&finish,
		"initial_ratchet_hkdf",
		&["pending.request()"],
		"initial ratchet adapter exact pending request",
	)?;
	require_one_call(
		&finish,
		"InitialRatchetKdfResponse::from_bytes",
		&["initial_ratchet_hkdf(pending.request())", ""],
		"initial ratchet adapter exact response bytes",
	)?;
	require_one_call(
		&finish,
		"resume_initial_ratchet_kdf",
		&["pending", "response"],
		"initial ratchet adapter same pending response resume",
	)?;
	require_ordered_once(
		&finish,
		&[
			"letresponse=beaconcrypt_core::pqxdh::InitialRatchetKdfResponse::from_bytes(initial_ratchet_hkdf(pending.request()),);",
			"beaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(pending,response)",
		],
		"initial ratchet adapter local response provenance",
	)?;
	if count(&finish, "letresponse=") != 1 {
		return Err("initial ratchet adapter response binding count changed".to_owned());
	}
	if count(&finish, "letpending=") != 0 {
		return Err("initial ratchet adapter pending parameter was shadowed".to_owned());
	}
	let adapter_ratchet = compact(&uncommented_rust(&snapshot.adapter_ratchet)?);
	require_once(
		&adapter_ratchet,
		"pub(crate)fninitial_ratchet_hkdf(request:&verified_ratchet::SymmetricRatchetKdfRequest,)->[u8;INITIAL_RATCHET_KDF_OUTPUT_SIZE]{",
		"initial ratchet adapter 64-byte HKDF signature",
	)?;
	let initial_hkdf = rust_body(&snapshot.adapter_ratchet, "initial_ratchet_hkdf")?;
	require_once(
		&initial_hkdf,
		"symmetric_ratchet_hkdf(request)",
		"initial ratchet adapter HKDF executor",
	)?;
	let symmetric_hkdf = rust_body(&snapshot.adapter_ratchet, "symmetric_ratchet_hkdf")?;
	require_one_call(
		&symmetric_hkdf,
		"crypto_kdf::hkdf::sha512::extract",
		&["None", "request.input()"],
		"initial ratchet adapter executor input",
	)?;
	require_one_call(
		&symmetric_hkdf,
		"crypto_kdf::hkdf::sha512::expand",
		&["OUTPUT_SIZE", "Some(request.info())", "&prk"],
		"initial ratchet adapter executor label",
	)?;
	require_once(
		&symmetric_hkdf,
		"letmutoutput=[0u8;OUTPUT_SIZE];output.copy_from_slice(&expanded);output",
		"initial ratchet adapter executor output",
	)?;
	let step_hkdf = rust_body(&snapshot.adapter_ratchet, "ratchet_hkdf")?;
	require_once(
		&step_hkdf,
		"verified_ratchet::RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))",
		"initial ratchet distinct 76-byte adapter response",
	)?;
	let kernel_new = rust_body(&snapshot.core_ratchet_concrete, "new")?;
	require_once(
		&kernel_new,
		"Self::from_counters(0,0,send_chain,receive_chain)",
		"initial ratchet zero-counter kernel initialization",
	)?;

	let lean_effect = compact(&snapshot.lean_ratchet_effect);
	let lean_initial = section_between(
		&lean_effect,
		"theorempqxdh.concrete.start_initial_ratchet_kdf_exact",
		"theorempqxdh.concrete.initial_request_accessor_exact",
		"initial ratchet Lean exact start anchor",
	)?;
	require_once(
		lean_initial,
		"request:={input:=root,info:=ratchet.SYM_RATCHET_INFO},initialization:=initialization",
		"initial ratchet Lean exact request interpretation",
	)?;
	let lean_accessor = section_between(
		&lean_effect,
		"theorempqxdh.concrete.initial_request_accessor_exact",
		"theorempqxdh.concrete.start_beacon_ratchet_kdf_exact",
		"initial ratchet Lean request accessor anchor",
	)?;
	require_once(
		lean_accessor,
		"pqxdh.concrete.InitialRatchetKdfPending.impl.requestpending=okpending.request",
		"initial ratchet Lean exact request accessor",
	)?;
	let lean_beacon = section_between(
		&lean_effect,
		"theorempqxdh.concrete.start_beacon_ratchet_kdf_exact",
		"theorempqxdh.concrete.start_server_ratchet_kdf_exact",
		"initial ratchet Lean Beacon role anchor",
	)?;
	require_once(
		lean_beacon,
		"initialization:={send_offset:=32#u8,receive_offset:=0#u8}",
		"initial ratchet Lean Beacon offsets",
	)?;
	let lean_server = section_between(
		&lean_effect,
		"theorempqxdh.concrete.start_server_ratchet_kdf_exact",
		"theorempqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition",
		"initial ratchet Lean Server role anchor",
	)?;
	require_once(
		lean_server,
		"initialization:={send_offset:=0#u8,receive_offset:=32#u8}",
		"initial ratchet Lean Server offsets",
	)?;
	let lean_resume = section_between(
		&lean_effect,
		"theorempqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition",
		"/-!##RatchetKDFresponseinterpretation-/",
		"initial ratchet Lean resume anchor",
	)?;
	for (wanted, label) in [
		(
			"pqxdh.split_initial_ratchet_kdf_outputresponse.bytespending.initialization",
			"initial ratchet Lean response partition",
		),
		(
			"ratchet.concrete.ConcreteRatchetKernel.newchains.send_chainchains.receive_chain",
			"initial ratchet Lean kernel chain order",
		),
	] {
		require_once(lean_resume, wanted, label)?;
	}
	let lean_kdf = compact(&snapshot.lean_pqxdh_kdf);
	require_once(
		&lean_kdf,
		"defrootChains(c:Crypto)(ds:Bytes):Bytes×Bytes:=((c.hkdfdsINFO_R64).take32,(c.hkdfdsINFO_R64).drop32)",
		"initial ratchet Lean ideal root-chain split anchor",
	)?;
	let lean_theorems = compact(&snapshot.lean_pqxdh_theorems);
	require_once(
		&lean_theorems,
		"theoremchain_agreement:",
		"initial ratchet Lean ideal post-record complementarity anchor",
	)?;

	let crypto = compact(&uncommented_pv(&snapshot.crypto)?);
	for (wanted, label) in [
		(
			"letfunserver_to_beacon_chain(root:bitstring)=hkdf_first_32(hkdf_sha512_no_salt(root,symmetric_ratchet_domain())).",
			"initial ratchet ProVerif server-to-beacon definition",
		),
		(
			"letfunbeacon_to_server_chain(root:bitstring)=hkdf_second_32(hkdf_sha512_no_salt(root,symmetric_ratchet_domain())).",
			"initial ratchet ProVerif beacon-to-server definition",
		),
	] {
		require_once(&crypto, wanted, label)?;
	}
	let environment = compact(&uncommented_pv(&snapshot.environment)?);
	let honest_beacon = section_between(
		&environment,
		"letHonestBeacon(",
		"letMaliciousBeacon(",
		"initial ratchet ProVerif HonestBeacon role",
	)?;
	let server = section_between(
		&environment,
		"letServer(",
		"letMaliciousServer()",
		"initial ratchet ProVerif Server role",
	)?;
	let malicious_server = section_between(
		&environment,
		"letMaliciousServer()",
		"letKeepBeaconStatePrivate()",
		"initial ratchet ProVerif MaliciousServer role",
	)?;
	for (role, label) in [
		(honest_beacon, "HonestBeacon"),
		(server, "Server"),
		(malicious_server, "MaliciousServer"),
	] {
		require_once(
			role,
			"letroot=pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input))in",
			&format!("initial ratchet ProVerif {label} exact root derivation"),
		)?;
	}
	for (role, server_calls, beacon_calls, label) in [
		(honest_beacon, 1, 1, "HonestBeacon"),
		(server, 1, 1, "Server"),
		(malicious_server, 1, 0, "MaliciousServer"),
	] {
		if count(role, "server_to_beacon_chain(") != server_calls
			|| count(role, "beacon_to_server_chain(") != beacon_calls
		{
			return Err(format!(
				"initial ratchet ProVerif {label} scoped chain occurrence count changed"
			));
		}
		if count(role, "letroot=") != 1 {
			return Err(format!(
				"initial ratchet ProVerif {label} root binding count changed"
			));
		}
	}
	for (source, wanted, label) in [
		(
			honest_beacon,
			"letserver_chain_1=server_to_beacon_chain(root)in",
			"initial ratchet ProVerif HonestBeacon initial-open chain",
		),
		(
			honest_beacon,
			"letbeacon_send_chain_1=beacon_to_server_chain(root)in",
			"initial ratchet ProVerif HonestBeacon outgoing chain",
		),
		(
			server,
			"letserver_chain_1=server_to_beacon_chain(root)in",
			"initial ratchet ProVerif Server initial-seal chain",
		),
		(
			server,
			"letbeacon_material_1=ratchet_material(beacon_to_server_chain(root))in",
			"initial ratchet ProVerif Server incoming chain",
		),
		(
			malicious_server,
			"letserver_material_1=ratchet_material(server_to_beacon_chain(root))in",
			"initial ratchet ProVerif MaliciousServer initial-seal chain",
		),
	] {
		require_once(source, wanted, label)?;
	}
	for (source, bindings, label) in [
		(
			honest_beacon,
			&[
				("letserver_chain_1=", 1usize),
				("letserver_material_1=", 1usize),
				("letbeacon_send_chain_1=", 1usize),
				("letbeacon_material_1=", 1usize),
			][..],
			"HonestBeacon",
		),
		(
			server,
			&[
				("letserver_chain_1=", 1usize),
				("letserver_material_1=", 1usize),
				("letbeacon_material_1=", 1usize),
			][..],
			"Server",
		),
		(
			malicious_server,
			&[("letserver_material_1=", 1usize)][..],
			"MaliciousServer",
		),
	] {
		for (binding, expected) in bindings {
			if count(source, binding) != *expected {
				return Err(format!(
					"initial ratchet ProVerif {label} binding count changed: {binding}"
				));
			}
		}
	}
	for (source, wanted, label) in [
		(
			honest_beacon,
			"letserver_material_1=ratchet_material(server_chain_1)inletopened_initial=open_frame(server_material_1,",
			"initial ratchet ProVerif HonestBeacon chain-to-open material",
		),
		(
			honest_beacon,
			"letbeacon_material_1=ratchet_material(beacon_send_chain_1)inletbeacon_frame=seal_frame(beacon_material_1,",
			"initial ratchet ProVerif HonestBeacon chain-to-seal material",
		),
		(
			server,
			"letserver_material_1=ratchet_material(server_chain_1)inletbinding=",
			"initial ratchet ProVerif Server initial material",
		),
	] {
		require_once(source, wanted, label)?;
	}

	Ok(())
}

fn validate_later_registration_fidelity(snapshot: &Snapshot) -> Result<(), String> {
	let facts = parse_facts(&snapshot.interface)?;
	let later_fact_count = facts
		.iter()
		.filter(|fact| fact.starts_with("later_registration."))
		.count();
	if later_fact_count != 68 {
		return Err(format!(
			"expected 68 later-registration fidelity facts, found {later_fact_count}"
		));
	}

	let beacon = rust_body(&snapshot.adapter_beacon, "finish_registration")?;
	for (wanted, label) in [
		(
			"letcontrol=match&self.state{BeaconState::InitSent{control,..}=>*control,_=>returnNone,};",
			"later-registration Beacon pending-state entry",
		),
		(
			"letresponse=typed_reader.get().ok()?;",
			"later-registration Beacon response reader",
		),
		(
			"response_server_identity:*response_server.as_bytes(),assigned_key_id:response.get_key_id(),shared_secrets:shared_secrets(dh1,dh2,dh3,dh4,&kem_shared)?,",
			"later-registration Beacon finish inputs",
		),
		(
			"letassociated_data=*candidate.associated_data();",
			"later-registration Beacon candidate associated data",
		),
		(
			"letauthenticated_server_key_id=decrypted.key_id;",
			"later-registration Beacon authenticated sender",
		),
		(
			"letmutauthenticated_plaintext=decrypted.plaintext;",
			"later-registration Beacon authenticated plaintext",
		),
		(
			"ifauthenticated_plaintext.len()<=verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE{returnNone;}",
			"later-registration Beacon binding-length gate",
		),
		(
			"letplaintext=authenticated_plaintext.split_off(verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE);",
			"later-registration Beacon returned remainder split",
		),
		(
			"letbinding=authenticated_plaintext.as_slice().try_into().ok()?;",
			"later-registration Beacon assigned-ID binding prefix",
		),
		(
			"Some((authenticated,associated_data,ratchet,plaintext))})();",
			"later-registration Beacon staged tuple",
		),
		(
			"letSome((authenticated,associated_data,ratchet,plaintext))=stagedelse{self.abort_registration(control);returnNone;};",
			"later-registration Beacon staged commit boundary",
		),
		(
			"self.state=BeaconState::Established{control:verified_pqxdh::beacon_commit(authenticated),associated_data,ratchet,};",
			"later-registration Beacon ratchet commit",
		),
	] {
		require_once(&beacon, wanted, label)?;
	}
	for (function, expected, label) in [
		(
			"decrypt_message_with_ratchet",
			&[
				"response.get_app_cipher_text().ok()?",
				"candidate.server_key_id()",
				"&associated_data",
				"&mutratchet",
				"",
			][..],
			"later-registration Beacon general receive handoff",
		),
		(
			"verified_pqxdh::authenticate_registration_key_id_binding",
			&["candidate", "authenticated_server_key_id", "binding", ""][..],
			"later-registration Beacon binding authentication",
		),
	] {
		require_one_call(&beacon, function, expected, label)?;
	}
	require_ordered_once(
		&beacon,
		&[
			"letresponse=typed_reader.get().ok()?;",
			"response.get_kem_cipher_text().ok()?",
			"response.get_ephemeral_key().ok()?",
			"response.get_identity_key().ok()?",
			"assigned_key_id:response.get_key_id()",
			"letassociated_data=*candidate.associated_data();",
			"decrypt_message_with_ratchet(response.get_app_cipher_text().ok()?,candidate.server_key_id(),&associated_data,&mutratchet,)?",
			"letauthenticated_server_key_id=decrypted.key_id;",
			"letmutauthenticated_plaintext=decrypted.plaintext;",
			"authenticated_plaintext.split_off(verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE)",
			"letbinding=authenticated_plaintext.as_slice().try_into().ok()?;",
			"verified_pqxdh::authenticate_registration_key_id_binding(candidate,authenticated_server_key_id,binding,)",
			"Some((authenticated,associated_data,ratchet,plaintext))})();",
			"letSome((authenticated,associated_data,ratchet,plaintext))=stagedelse",
			"self.state=BeaconState::Established",
			"Some(plaintext)",
		],
		"later-registration Beacon response-to-commit flow",
	)?;
	for forbidden in [
		"decrypted.seq",
		"first_sequence",
		"get_seq()",
		"seq==1",
		"seq!=1",
	] {
		forbid(
			&beacon,
			forbidden,
			"later-registration Beacon first-sequence gate",
		)?;
	}

	let adapter = rust_body(&snapshot.adapter_ratchet, "decrypt_message_with_ratchet")?;
	for (wanted, label) in [
		(
			"letkey_seq=frame.get_seq();",
			"later-registration adapter parsed sequence",
		),
		(
			"letkernel=ratchet.refined.take();",
			"later-registration adapter entry kernel",
		),
		(
			"letmuteffect=verified_ratchet::begin_receive(kernel,key_seq,context);",
			"later-registration adapter general receive start",
		),
		(
			"verified_ratchet::ReceiveEffect::ReceiveKdfRequested(pending)=>{letresponse=ratchet_hkdf(pending.request());pending.resume(response)}",
			"later-registration adapter exact KDF continuation",
		),
		(
			"letopened=open_frame(material,open.sequence(),open.context());",
			"later-registration adapter exact open capability",
		),
		(
			"let(kernel,opened)=open.finish(opened);",
			"later-registration adapter receive completion",
		),
		(
			"Some(Decrypted{plaintext,key_id:kid,seq:key_seq,})",
			"later-registration adapter result metadata",
		),
	] {
		require_once(&adapter, wanted, label)?;
	}
	require_ordered(
		&adapter,
		&[
			"letcontext=OpenFrameContext{ciphertext,associated_data,sender_kid:kid,};",
			"letkey_seq=frame.get_seq();",
			"letkernel=ratchet.refined.take();",
			"verified_ratchet::begin_receive(kernel,key_seq,context)",
			"ratchet_hkdf(pending.request())",
			"pending.resume(response)",
			"open_frame(material,open.sequence(),open.context())",
			"open.finish(opened)",
			"ratchet.refined.put(kernel)",
			"breakopened?",
			"Some(Decrypted{plaintext,key_id:kid,seq:key_seq,})",
		],
		"later-registration adapter parsed-sequence-to-result flow",
	)?;
	for forbidden in ["first_sequence", "key_seq==1", "key_seq!=1"] {
		forbid(
			&adapter,
			forbidden,
			"later-registration adapter first-sequence gate",
		)?;
	}

	let control = compact(&uncommented_rust(&snapshot.core_ratchet_control)?);
	require_once(
		&control,
		"pubconstRATCHET_MAX_GAP:u64=50;",
		"later-registration core maximum gap",
	)?;
	let plan = rust_body(&snapshot.core_ratchet_control, "plan_receive_until")?;
	require_ordered_once(
		&plan,
		&[
			"letderivations=target-state.receive_sequence;",
			"letskipped=derivations-1;",
			"letcached=state.receive_cache.lenasu64;",
			"ifskipped>RATCHET_MAX_GAP||cached>RATCHET_MAX_GAP-skipped",
			"ReceivePlan{sequence:Some(target),derivations,}",
		],
		"later-registration core future receive plan",
	)?;
	let skipped_source = section_between(
		&snapshot.core_ratchet_control,
		"pub(crate) fn advance_receive(",
		"/// Outcome of authenticating a cached receive key.",
		"later-registration skipped-key advance",
	)?;
	let skipped = rust_body(skipped_source, "advance_receive")?;
	require_ordered_once(
		&skipped,
		&[
			"letnext=state.receive_sequence+1;",
			"state.receive_cache.append(next)",
			"receive_sequence:next,receive_cache",
			"sequence:Some(next),slot:Some(slot)",
		],
		"later-registration core skipped-key advance",
	)?;
	let target = rust_body(&snapshot.core_ratchet_control, "advance_receive_target")?;
	require_once(
		&target,
		"state:RatchetState{receive_sequence:next,..state},sequence:Some(next)",
		"later-registration core target advance",
	)?;
	forbid(
		&target,
		"receive_cache.append",
		"later-registration core target cache insertion",
	)?;

	let begin = rust_body(&snapshot.core_ratchet_concrete, "begin_receive")?;
	for (wanted, label) in [
		(
			"letplan=plan_receive_until(kernel.refined.control,target);",
			"later-registration core begin plan",
		),
		(
			"letskipped=plan.derivations-1;",
			"later-registration core skipped count",
		),
		(
			"letremaining=plan.derivationsasu8;",
			"later-registration core remaining derivations",
		),
		(
			"letfirst_slot=kernel.refined.control.receive_cache_len();",
			"later-registration core first live cache slot",
		),
		(
			"if!refined_receive_slots_are_empty(&kernel.refined,first_slot,skippedasu8){returnreceive_rejected(kernel,context);}",
			"later-registration core empty destination preflight",
		),
		(
			"letrequest=SymmetricRatchetKdfRequest::new(*kernel.refined.receive_chain.as_bytes());",
			"later-registration core initial receive-chain request",
		),
		(
			"entry:kernel,context,target:sequence,working_control,staged_slots:empty_material_slots(),first_slot,skipped:0,remaining,request",
			"later-registration core private receive staging",
		),
	] {
		require_once(&begin, wanted, label)?;
	}
	let receive_kdf = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveKdf<Context>",
		"impl<Context> ReceiveOpen<Context>",
		"later-registration core receive KDF phase",
	)?;
	let resume = rust_body(receive_kdf, "resume")?;
	for (wanted, label) in [
		(
			"ifself.remaining==1{letadvanced=advance_receive_target(self.working_control);",
			"later-registration core final-target branch",
		),
		(
			"if!(sequence==self.target){returnreceive_rejected(self.entry,self.context);}",
			"later-registration core final target equality gate",
		),
		(
			"final_receive_chain:stepped.chain,staged_slots:self.staged_slots,target_sequence:sequence,target_material:stepped.material,first_slot:self.first_slot,skipped:self.skipped",
			"later-registration core pending target separation",
		),
		(
			"if!pending_receive_is_valid(&self.entry.refined,&pending,self.target){returnreceive_rejected(self.entry,self.context);}",
			"later-registration core final pending validation gate",
		),
		(
			"letadvanced=advance_receive(self.working_control);",
			"later-registration core nonfinal skipped step",
		),
		(
			"self.staged_slots[slot_index]=Some(CachedReceiveKey{sequence,material:stepped.material,});",
			"later-registration core skipped material pair",
		),
		(
			"self.working_control=advanced.state;self.skipped+=1;self.remaining-=1;self.request=SymmetricRatchetKdfRequest::new(*stepped.chain.as_bytes());",
			"later-registration core next receive request",
		),
	] {
		require_once(&resume, wanted, label)?;
	}
	let refined_source = uncommented_rust(&snapshot.core_ratchet_refined)?;
	let pending = compact(section_between(
		&refined_source,
		"pub(super) struct PendingReceive<",
		"impl<SendChain, ReceiveChain, Material> RefinedRatchet",
		"later-registration refined pending declaration",
	)?);
	require_once(
		&pending,
		"pub(super)committed_control:RatchetState,pub(super)final_receive_chain:ReceiveChain,pub(super)staged_slots:[Option<CachedReceiveKey<Material>>;RECEIVE_CACHE_CAPACITY],pub(super)target_sequence:u64,pub(super)target_material:Material,pub(super)first_slot:u8,pub(super)skipped:u8",
		"later-registration refined pending fields",
	)?;
	let pending_valid = rust_body(&snapshot.core_ratchet_refined, "pending_receive_is_valid")?;
	for (wanted, label) in [
		(
			"if!(pending.target_sequence==requested){returnfalse;}",
			"later-registration exact pending target validation",
		),
		(
			"if!(pending.first_slot==state.control.receive_cache_len()){returnfalse;}",
			"later-registration first live slot validation",
		),
		(
			"if!(pending.committed_control.send_sequence()==state.control.send_sequence()){returnfalse;}",
			"later-registration unchanged send counter validation",
		),
		(
			"if!(pending.committed_control.receive_sequence()==requested){returnfalse;}",
			"later-registration target receive counter validation",
		),
		(
			"if!(requested-entry_receive_sequence==pending.skippedasu64+1){returnfalse;}",
			"later-registration skipped-prefix validation",
		),
		(
			"iflookup_receive_key(pending.committed_control,requested).is_some(){returnfalse;}",
			"later-registration target cache absence validation",
		),
		(
			"if!(pending.committed_control.receive_cache_len()asusize==committed_len){returnfalse;}",
			"later-registration exact cache-length validation",
		),
		(
			"receive_control_prefix_matches(state.control,pending.committed_control,0,pending.first_slot,)",
			"later-registration committed cache-prefix validation",
		),
		(
			"pending_receive_slots_are_valid(state,pending,pending.first_slot,expected_first,pending.skipped,)",
			"later-registration staged-slot prefix validation",
		),
	] {
		require_once(&pending_valid, wanted, label)?;
	}
	let empty_slots = rust_body(
		&snapshot.core_ratchet_refined,
		"refined_receive_slots_are_empty",
	)?;
	require_ordered_once(
		&empty_slots,
		&[
			"letmutslot=first_slot;",
			"letmutleft=remaining;",
			"letslot_index=slotasusize;",
			"ifslot_index>=RECEIVE_CACHE_CAPACITY{returnfalse;}",
			"ifstate.receive_slots[slot_index].is_some(){returnfalse;}",
			"slot+=1;",
			"left-=1;",
			"true",
		],
		"later-registration empty destination scan",
	)?;
	let staged_slots = rust_body(
		&snapshot.core_ratchet_refined,
		"pending_receive_slots_are_valid",
	)?;
	require_ordered_once(
		&staged_slots,
		&[
			"letmutcurrent_slot=slot;",
			"letmutexpected=expected_sequence;",
			"letmutleft=remaining;",
			"letslot_index=current_slotasusize;",
			"ifslot_index>=RECEIVE_CACHE_CAPACITY{returnfalse;}",
			"ifstate.receive_slots[slot_index].is_some(){returnfalse;}",
			"letstaged=matchpending.staged_slots[slot_index].as_ref(){Some(staged)=>staged,None=>returnfalse,};",
			"if!(staged.sequence==expected){returnfalse;}",
			"if!(pending.committed_control.receive_key_at(current_slot)==Some(expected)){returnfalse;}",
			"left-=1;",
			"current_slot+=1;",
			"expected+=1;",
			"true",
		],
		"later-registration staged slot pairing scan",
	)?;
	let open_phase = section_between(
		&snapshot.core_ratchet_concrete,
		"impl<Context> ReceiveOpen<Context>",
		"/// Checked restoration builder",
		"later-registration core receive-open phase",
	)?;
	for (name, wanted, label) in [
		(
			"sequence",
			"PreparedReceive::PreparedReceiveFutureCase(pending)=>pending.target_sequence",
			"later-registration future open sequence",
		),
		(
			"material",
			"PreparedReceive::PreparedReceiveFutureCase(pending)=>Some(&pending.target_material)",
			"later-registration future open material",
		),
	] {
		require_once(&rust_body(open_phase, name)?, wanted, label)?;
	}
	let finish = rust_body(open_phase, "finish")?;
	require_ordered_once(
		&finish,
		&[
			"None=>return(self.entry,None)",
			"publish_future_receive(&mutentry.refined,pending)",
			"(entry,Some(plaintext))",
		],
		"later-registration success-only publication",
	)?;
	let publish_source = section_between(
		&snapshot.core_ratchet_refined,
		"pub(super) fn publish_future_receive<",
		"/// Commit an already-preflighted suffix of receive steps.",
		"later-registration future publisher",
	)?;
	let publish = rust_body(publish_source, "publish_future_receive")?;
	require_ordered_once(
		&publish,
		&[
			"letfirst_index=pending.first_slotasusize;",
			"letskipped=pending.skippedasusize;",
			"iffirst_index>RECEIVE_CACHE_CAPACITY{return;}",
			"ifskipped>RECEIVE_CACHE_CAPACITY-first_index{return;}",
			"publish_future_receive_slots(state,&mutpending.staged_slots,pending.first_slot,pending.skipped,)",
			"state.receive_chain=pending.final_receive_chain;",
			"state.control=pending.committed_control;",
		],
		"later-registration future publication order",
	)?;
	forbid(
		&publish,
		"target_material",
		"later-registration target material publication",
	)?;
	let publish_slots = rust_body(
		&snapshot.core_ratchet_refined,
		"publish_future_receive_slots",
	)?;
	require_ordered_once(
		&publish_slots,
		&[
			"letmutcurrent_slot=slot;",
			"letmutleft=remaining;",
			"letslot_index=current_slotasusize;",
			"ifslot_index>=RECEIVE_CACHE_CAPACITY{return;}",
			"letmoved=staged_slots[slot_index].take();",
			"state.receive_slots[slot_index]=moved;",
			"current_slot+=1;",
			"left-=1;",
		],
		"later-registration exact skipped-slot movement",
	)?;

	for theorem in [
		"theorem ratchet.concrete.begin_receive_future_request_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_sequence_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_material_exact",
		"theorem ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext",
	] {
		require_once(
			&snapshot.lean_ratchet_effect,
			theorem,
			"later-registration structural Lean anchor",
		)?;
	}
	for theorem in [
		"theorem max_gap_eq :",
		"theorem plan_receive_until_accept (",
		"theorem plan_receive_until_bound (",
		"theorem advance_receive_ok (",
		"theorem advance_receive_target_ok (",
	] {
		require_once(
			&snapshot.lean_ratchet_control,
			theorem,
			"later-registration control Lean anchor",
		)?;
	}
	for theorem in [
		"theorem receiveMessage_refines",
		"theorem receiveMessage_state_neutral",
	] {
		require_once(
			&snapshot.lean_ratchet_refinement,
			theorem,
			"later-registration refinement Lean anchor",
		)?;
	}

	let model = compact(&uncommented_pv(&snapshot.later_registration_control)?);
	for (wanted, label) in [
		(
			"funzero_sequence():sequence[data].",
			"later-registration zero sequence constructor",
		),
		(
			"funlater_registration_ratchet_state(sequence,bitstring,bitstring):bitstring[data].",
			"later-registration ratchet-state constructor",
		),
		(
			"funlater_registration_return(bitstring,bitstring):bitstring[data].",
			"later-registration return constructor",
		),
		(
			"freeLATER_REGISTRATION_SEQ1_PAYLOAD:bitstring[private].",
			"later-registration sequence-one payload",
		),
		(
			"freeLATER_REGISTRATION_SEQ2_PAYLOAD:bitstring[private].",
			"later-registration sequence-two payload",
		),
		(
			"freeLATER_REGISTRATION_SEQ3_PAYLOAD:bitstring[private].",
			"later-registration sequence-three payload",
		),
		(
			"freeLATER_REGISTRATION_ORIGINAL_WITNESS:bitstring[private].",
			"later-registration original-response witness",
		),
		(
			"freeLATER_REGISTRATION_SUBSTITUTION_WITNESS:bitstring[private].",
			"later-registration substitution witness",
		),
		(
			"freeLATER_REGISTRATION_FAITHFUL_WITNESS:bitstring[private].",
			"later-registration faithful witness",
		),
		(
			"freeLATER_REGISTRATION_FIRST_ONLY_WITNESS:bitstring[private].",
			"later-registration counterfactual witness",
		),
		(
			"freeLATER_REGISTRATION_FIRST_ONLY_CANARY:bitstring[private].",
			"later-registration counterfactual canary",
		),
		(
			"eventLaterRegistrationOriginalResponseIssued(bitstring,bitstring,bitstring,bitstring,bitstring).",
			"later-registration original-response event signature",
		),
		(
			"eventLaterRegistrationServerFrameSent(bitstring,bitstring,bitstring,sequence,key_id,key_id,bitstring,bitstring,bitstring).",
			"later-registration Server-send event signature",
		),
		(
			"eventLaterRegistrationSubstitutionSelected(bitstring,bitstring,bitstring,bitstring,bitstring).",
			"later-registration substitution event signature",
		),
		(
			"eventLaterRegistrationFaithfulAttempted(bitstring,bitstring).",
			"later-registration faithful-attempt event signature",
		),
		(
			"eventLaterRegistrationFirstOnlyAttempted(bitstring,bitstring).",
			"later-registration counterfactual-attempt event signature",
		),
		(
			"eventLaterRegistrationGeneralReceiveOpened(bitstring,bitstring,sequence,key_id,beaconcrypt_core__pqxdh__t_RegistrationKeyIdBinding,bitstring,bitstring,bitstring).",
			"later-registration opened event signature",
		),
		(
			"eventLaterRegistrationFirstOnlyGateReached(bitstring,sequence,bitstring).",
			"later-registration gate-reached event signature",
		),
		(
			"eventLaterRegistrationFirstOnlyGatePassed(bitstring,sequence,bitstring).",
			"later-registration gate-passed event signature",
		),
		(
			"eventLaterRegistrationPoststatePublished(bitstring,bitstring,bitstring,sequence,bitstring,sequence,bitstring,receive_cache,bitstring).",
			"later-registration poststate event signature",
		),
		(
			"eventLaterRegistrationCommitted(bitstring,bitstring,bitstring,bitstring,sequence,key_id,key_id,bitstring,bitstring,bitstring,bitstring,bitstring,bitstring).",
			"later-registration committed event signature",
		),
		(
			"eventLaterRegistrationTargetUnavailable(bitstring,bitstring,sequence,bitstring,receive_cache,bitstring).",
			"later-registration target-absence event signature",
		),
		(
			"eventLaterRegistrationReturned(bitstring,bitstring).",
			"later-registration returned event signature",
		),
	] {
		require_once(&model, wanted, label)?;
	}

	let open = section_between(
		&model,
		"letLaterSequenceRegistrationOpen(",
		"letLaterSequenceRegistrationCommit(",
		"later-registration finite open process",
	)?;
	require_ordered_once(
		open,
		&[
			"letresponse_server_kex=x25519_public_from_ed(response_server_identity)in",
			"letbeacon_identity=ed_public(beacon_identity_secret)in",
			"letdh1=x25519_beacon_dh(beacon_prekey_secret,response_server_kex)in",
			"letdh2=x25519_beacon_dh(beacon_identity_secret,server_ephemeral)in",
			"letdh3=x25519_beacon_dh(beacon_prekey_secret,server_ephemeral)in",
			"letdh4=x25519_beacon_dh(beacon_one_time_secret,server_ephemeral)in",
			"letkem_secret=mlkem_decapsulate(kem_ciphertext,beacon_pq_secret)in",
			"letshared_secrets=beaconcrypt_core__pqxdh__PqxdhSharedSecrets(dh1,dh2,dh3,dh4,kem_secret)in",
			"ifresponse_server_identity=expected_server_identitythen",
			"letroot_input=beaconcrypt_core__pqxdh__build_root_key_input(shared_secrets)in",
			"letroot=pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input))in",
		],
		"later-registration Beacon root reconstruction",
	)?;
	for (wanted, label) in [
		(
			"letkex_response(response_server_identity,server_ephemeral,kem_ciphertext,app_ciphertext,assigned_key_id)=responsein",
			"later-registration response field parse",
		),
		(
			"ifresponse_server_identity=expected_server_identitythen",
			"later-registration Beacon root reconstruction",
		),
		(
			"letroot=pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input))in",
			"later-registration reconstructed root",
		),
		(
			"letassociated_data=beaconcrypt_core__pqxdh__build_associated_data(expected_server_identity,beacon_identity)in",
			"later-registration reconstructed associated data",
		),
		(
			"letsession=session_label(expected_server_identity,beacon_identity,assigned_key_id,root_input)in",
			"later-registration reconstructed session",
		),
		(
			"letserver_chain_1=server_to_beacon_chain(root)inletserver_chain_2=ratchet_next(server_chain_1)inletserver_chain_3=ratchet_next(server_chain_2)inletserver_chain_4=ratchet_next(server_chain_3)in",
			"later-registration receive chain expansion",
		),
		(
			"letserver_material_1=ratchet_material(server_chain_1)inletserver_material_2=ratchet_material(server_chain_2)inletserver_material_3=ratchet_material(server_chain_3)in",
			"later-registration receive material expansion",
		),
		(
			"letcrypto_frame(frame_ciphertext,frame_tag,frame_commitment,frame_sequence,authenticated_server_key_id)=app_ciphertextin",
			"later-registration inner frame parse",
		),
		(
			"ifauthenticated_server_key_id=expected_server_key_idthen",
			"later-registration authenticated sender gate",
		),
		(
			"letopened=open_frame(server_material_3,associated_data,frame_sequence,expected_server_key_id,app_ciphertext)in",
			"later-registration generic sequence open",
		),
		(
			"letregistration_payload(authenticated_binding,registration_plaintext)=openedin",
			"later-registration opened payload parse",
		),
		(
			"letcache_1=receive_cache_entry(first_sequence(),server_material_1,receive_cache_empty())inletcache_2=receive_cache_entry(next_sequence(first_sequence()),server_material_2,cache_1)in",
			"later-registration exact newest-first cache",
		),
		(
			"letreceive_poststate=receive_state(frame_sequence,server_chain_4,cache_2)in",
			"later-registration receive poststate",
		),
		(
			"letcommitted_ratchet=later_registration_ratchet_state(zero_sequence(),beacon_to_server_chain(root),receive_poststate)in",
			"later-registration complete ratchet poststate",
		),
	] {
		require_once(open, wanted, label)?;
	}
	let opened_events = all_arguments(open, "LaterRegistrationGeneralReceiveOpened")?;
	if opened_events
		!= [vec![
			"witness".to_owned(),
			"session".to_owned(),
			"frame_sequence".to_owned(),
			"authenticated_server_key_id".to_owned(),
			"authenticated_binding".to_owned(),
			"registration_plaintext".to_owned(),
			"opened".to_owned(),
			"app_ciphertext".to_owned(),
		]] {
		return Err(format!(
			"later-registration opened event fields changed: {opened_events:?}"
		));
	}
	let open_outputs = all_arguments(open, "out")?;
	if open_outputs.len() != 1
		|| open_outputs[0]
			!= [
				"reply",
				"(session,root,assigned_key_id,frame_sequence,authenticated_server_key_id,authenticated_binding,registration_plaintext,opened,app_ciphertext,server_chain_4,server_material_1,server_material_2,server_material_3,cache_2,receive_poststate,committed_ratchet)",
			]
			.map(str::to_owned)
	{
		return Err(format!(
			"later-registration open reply fields changed: {open_outputs:?}"
		));
	}

	let commit = section_between(
		&model,
		"letLaterSequenceRegistrationCommit(",
		"letLaterSequenceRegistrationFaithfulFinish(",
		"later-registration shared commit process",
	)?;
	require_ordered_once(
		commit,
		&[
			"letexpected_binding=beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(assigned_key_id))in",
			"letadmitted_binding=phase2_assigned_id_binding_gate(authenticated_binding,expected_binding)in",
			"eventLaterRegistrationPoststatePublished(",
			"eventLaterRegistrationTargetUnavailable(",
			"eventLaterRegistrationCommitted(",
			"eventLaterRegistrationReturned(witness,registration_plaintext);",
			"out(c,later_registration_return(witness,registration_plaintext));",
		],
		"later-registration binding-to-commit order",
	)?;
	require_once(
		commit,
		"ifwitness=LATER_REGISTRATION_FIRST_ONLY_WITNESSthenout(c,LATER_REGISTRATION_FIRST_ONLY_CANARY)",
		"later-registration counterfactual canary confinement",
	)?;
	for (function, expected, label) in [
		(
			"LaterRegistrationPoststatePublished",
			&[
				"witness",
				"session",
				"root",
				"zero_sequence()",
				"beacon_to_server_chain(root)",
				"frame_sequence",
				"server_chain_4",
				"cache_2",
				"committed_ratchet",
			][..],
			"later-registration exact poststate event",
		),
		(
			"LaterRegistrationTargetUnavailable",
			&[
				"witness",
				"session",
				"frame_sequence",
				"server_material_3",
				"cache_2",
				"committed_ratchet",
			][..],
			"later-registration target-absence event",
		),
		(
			"LaterRegistrationCommitted",
			&[
				"witness",
				"session",
				"root",
				"response",
				"frame_sequence",
				"authenticated_server_key_id",
				"assigned_key_id",
				"opened_payload",
				"registration_plaintext",
				"app_ciphertext",
				"server_material_3",
				"receive_poststate",
				"committed_ratchet",
			][..],
			"later-registration commit event",
		),
	] {
		require_one_call(commit, function, expected, label)?;
	}

	let faithful = section_between(
		&model,
		"letLaterSequenceRegistrationFaithfulFinish(",
		"letLaterSequenceRegistrationFirstOnlyFinish(",
		"later-registration faithful finish process",
	)?;
	require_once(
		faithful,
		"eventLaterRegistrationFaithfulAttempted(LATER_REGISTRATION_FAITHFUL_WITNESS,response);",
		"later-registration faithful attempt",
	)?;
	require_once(
		faithful,
		"LaterSequenceRegistrationOpen(LATER_REGISTRATION_FAITHFUL_WITNESS,expected_server_identity,expected_server_key_id,beacon_identity_secret,beacon_prekey_secret,beacon_one_time_secret,beacon_pq_secret,response,reply)",
		"later-registration faithful shared open",
	)?;
	require_once(
		faithful,
		"LaterSequenceRegistrationCommit(LATER_REGISTRATION_FAITHFUL_WITNESS,response,session,root,assigned_key_id,frame_sequence,authenticated_server_key_id,authenticated_binding,registration_plaintext,opened_payload,app_ciphertext,server_chain_4,server_material_1,server_material_2,server_material_3,cache_2,receive_poststate,committed_ratchet)",
		"later-registration faithful direct commit",
	)?;
	for forbidden in [
		"first_sequence()",
		"LaterRegistrationFirstOnlyGateReached",
		"LaterRegistrationFirstOnlyGatePassed",
	] {
		forbid(
			faithful,
			forbidden,
			"later-registration faithful sequence gate",
		)?;
	}

	let first_only = section_between(
		&model,
		"letLaterSequenceRegistrationFirstOnlyFinish(",
		"letLaterSequenceRegistrationControl()=",
		"later-registration counterfactual finish process",
	)?;
	require_once(
		first_only,
		"eventLaterRegistrationFirstOnlyAttempted(LATER_REGISTRATION_FIRST_ONLY_WITNESS,response);",
		"later-registration counterfactual attempt",
	)?;
	require_ordered_once(
		first_only,
		&[
			"LaterSequenceRegistrationOpen(LATER_REGISTRATION_FIRST_ONLY_WITNESS,expected_server_identity,expected_server_key_id,beacon_identity_secret,beacon_prekey_secret,beacon_one_time_secret,beacon_pq_secret,response,reply)",
			"in(reply,(session:bitstring,root:bitstring,assigned_key_id:key_id,frame_sequence:sequence",
			"eventLaterRegistrationFirstOnlyGateReached(LATER_REGISTRATION_FIRST_ONLY_WITNESS,frame_sequence,response);",
			"ifframe_sequence=first_sequence()then",
			"eventLaterRegistrationFirstOnlyGatePassed(LATER_REGISTRATION_FIRST_ONLY_WITNESS,frame_sequence,response);",
			"LaterSequenceRegistrationCommit(LATER_REGISTRATION_FIRST_ONLY_WITNESS,response,session,root,assigned_key_id,frame_sequence,authenticated_server_key_id,authenticated_binding,registration_plaintext,opened_payload,app_ciphertext,server_chain_4,server_material_1,server_material_2,server_material_3,cache_2,receive_poststate,committed_ratchet)",
		],
		"later-registration counterfactual post-open gate placement",
	)?;
	if count(&model, "ifframe_sequence=first_sequence()then") != 1 {
		return Err(
			"later-registration counterfactual first-sequence gate count changed".to_owned(),
		);
	}

	let coordinator_start = model
		.find("letLaterSequenceRegistrationControl()=")
		.ok_or_else(|| "missing later-registration coordinator".to_owned())?;
	let coordinator = &model[coordinator_start..];
	require_ordered_once(
		coordinator,
		&[
			"newserver_identity_secret:bitstring;",
			"newbeacon_identity_secret:bitstring;",
			"newbeacon_prekey_secret:bitstring;",
			"newbeacon_one_time_secret:bitstring;",
			"newbeacon_pq_secret:bitstring;",
			"newserver_ephemeral_secret:bitstring;",
			"newkem_coins:bitstring;",
			"letserver_identity=ed_public(server_identity_secret)in",
			"letbeacon_identity=ed_public(beacon_identity_secret)in",
			"letbeacon_prekey=x25519_public(beacon_prekey_secret)in",
			"letbeacon_one_time=x25519_public(beacon_one_time_secret)in",
			"letbeacon_pq=mlkem_public(beacon_pq_secret)in",
			"letserver_ephemeral=x25519_public(server_ephemeral_secret)in",
			"letkem_ciphertext=mlkem_ciphertext(beacon_pq,kem_coins)in",
			"letkem_secret=mlkem_shared_secret(beacon_pq,kem_coins)in",
			"letdh1=x25519_server_dh(server_identity_secret,beacon_prekey)in",
			"letdh2=x25519_server_dh(server_ephemeral_secret,x25519_public_from_ed(beacon_identity))in",
			"letdh3=x25519_server_dh(server_ephemeral_secret,beacon_prekey)in",
			"letdh4=x25519_server_dh(server_ephemeral_secret,beacon_one_time)in",
			"letshared_secrets=beaconcrypt_core__pqxdh__PqxdhSharedSecrets(dh1,dh2,dh3,dh4,kem_secret)in",
			"letroot_input=beaconcrypt_core__pqxdh__build_root_key_input(shared_secrets)in",
			"letroot=pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input))in",
		],
		"later-registration Server root construction",
	)?;
	for (wanted, label) in [
		(
			"letroot=pqxdh_root(beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input))in",
			"later-registration coordinator root",
		),
		(
			"letassociated_data=beaconcrypt_core__pqxdh__build_associated_data(server_identity,beacon_identity)in",
			"later-registration coordinator associated data",
		),
		(
			"letsession=session_label(server_identity,beacon_identity,assigned_key_id,root_input)in",
			"later-registration coordinator session",
		),
		(
			"letassigned_binding=beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(key_id_encoding(assigned_key_id))in",
			"later-registration coordinator binding",
		),
		(
			"letfirst_frame=seal_frame(server_material_1,associated_data,first_sequence(),server_key_id,registration_payload(assigned_binding,LATER_REGISTRATION_SEQ1_PAYLOAD))in",
			"later-registration genuine first frame",
		),
		(
			"letsecond_frame=seal_frame(server_material_2,associated_data,next_sequence(first_sequence()),server_key_id,LATER_REGISTRATION_SEQ2_PAYLOAD)in",
			"later-registration genuine second frame",
		),
		(
			"letthird_frame=seal_frame(server_material_3,associated_data,next_sequence(next_sequence(first_sequence())),server_key_id,registration_payload(assigned_binding,LATER_REGISTRATION_SEQ3_PAYLOAD))in",
			"later-registration genuine third frame",
		),
		(
			"letoriginal_response=kex_response(server_identity,server_ephemeral,kem_ciphertext,first_frame,assigned_key_id)in",
			"later-registration original response",
		),
		(
			"letsubstituted_response=kex_response(server_identity,server_ephemeral,kem_ciphertext,third_frame,assigned_key_id)in",
			"later-registration app-frame-only substitution",
		),
		(
			"in(c,candidate:bitstring);ifcandidate=substituted_responsethen",
			"later-registration single candidate selection",
		),
		(
			"eventLaterRegistrationSubstitutionSelected(LATER_REGISTRATION_SUBSTITUTION_WITNESS,session,root,original_response,candidate);",
			"later-registration exact substitution event",
		),
	] {
		require_once(coordinator, wanted, label)?;
	}
	require_ordered_once(
		coordinator,
		&[
			"eventLaterRegistrationServerFrameSent(session,root,original_response,first_sequence(),server_key_id,assigned_key_id,LATER_REGISTRATION_SEQ1_PAYLOAD,first_frame,server_material_1);",
			"eventLaterRegistrationOriginalResponseIssued(LATER_REGISTRATION_ORIGINAL_WITNESS,session,root,first_frame,original_response);",
			"out(c,original_response);",
			"eventLaterRegistrationServerFrameSent(session,root,original_response,next_sequence(first_sequence()),server_key_id,assigned_key_id,LATER_REGISTRATION_SEQ2_PAYLOAD,second_frame,server_material_2);",
			"out(c,second_frame);",
			"eventLaterRegistrationServerFrameSent(session,root,original_response,next_sequence(next_sequence(first_sequence())),server_key_id,assigned_key_id,LATER_REGISTRATION_SEQ3_PAYLOAD,third_frame,server_material_3);",
			"out(c,third_frame);",
			"in(c,candidate:bitstring);",
			"ifcandidate=substituted_responsethen",
		],
		"later-registration genuine response and later-frame order",
	)?;
	for (function, witness, label) in [
		(
			"LaterSequenceRegistrationFaithfulFinish",
			"LATER_REGISTRATION_FAITHFUL_WITNESS",
			"later-registration faithful fanout",
		),
		(
			"LaterSequenceRegistrationFirstOnlyFinish",
			"LATER_REGISTRATION_FIRST_ONLY_WITNESS",
			"later-registration counterfactual fanout",
		),
	] {
		let calls = all_arguments(coordinator, function)?;
		if calls.len() != 1 || calls[0].last().map(String::as_str) != Some("candidate") {
			return Err(format!("{label} changed: {calls:?}"));
		}
		if !model.contains(witness) {
			return Err(format!("missing {label} witness: {witness}"));
		}
	}

	let queries = compact(&uncommented_pv(&snapshot.later_registration_queries)?);
	if snapshot
		.later_registration_queries
		.lines()
		.filter(|line| line.trim_start().starts_with("query "))
		.count()
		!= 18
	{
		return Err("later-registration query count changed".to_owned());
	}
	let sym = "symmetric_ratchet_domain()";
	let chain1 = format!("hkdf_first_32(hkdf_sha512_no_salt(root,{sym}))");
	let chain2 = format!("hkdf_second_32(hkdf_sha512_no_salt({chain1},{sym}))");
	let chain3 = format!("hkdf_second_32(hkdf_sha512_no_salt({chain2},{sym}))");
	let chain4 = format!("hkdf_second_32(hkdf_sha512_no_salt({chain3},{sym}))");
	let material1 = format!(
		"ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt({chain1},{sym})),hkdf_final_12(hkdf_sha512_no_salt({chain1},{sym})))"
	);
	let material2 = format!(
		"ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt({chain2},{sym})),hkdf_final_12(hkdf_sha512_no_salt({chain2},{sym})))"
	);
	let material3 = format!(
		"ratchet_key_nonce(hkdf_first_32(hkdf_sha512_no_salt({chain3},{sym})),hkdf_final_12(hkdf_sha512_no_salt({chain3},{sym})))"
	);
	let cache = format!(
		"receive_cache_entry(next_sequence(first_sequence()),{material2},receive_cache_entry(first_sequence(),{material1},receive_cache_empty()))"
	);
	let receive_state =
		format!("receive_state(next_sequence(next_sequence(first_sequence())),{chain4},{cache})");
	let send_chain = format!("hkdf_second_32(hkdf_sha512_no_salt(root,{sym}))");
	let ratchet =
		format!("later_registration_ratchet_state(zero_sequence(),{send_chain},{receive_state})");
	for (wanted, label) in [
		(
			format!(
				"event(LaterRegistrationPoststatePublished(LATER_REGISTRATION_FAITHFUL_WITNESS,session,root,zero_sequence(),{send_chain},next_sequence(next_sequence(first_sequence())),{chain4},{cache},{ratchet}))."
			),
			"later-registration exact poststate query",
		),
		(
			format!(
				"event(LaterRegistrationTargetUnavailable(LATER_REGISTRATION_FAITHFUL_WITNESS,session,next_sequence(next_sequence(first_sequence())),{material3},{cache},{ratchet}))."
			),
			"later-registration exact target-absence query",
		),
	] {
		require_once(&queries, &wanted, label)?;
	}
	for (wanted, label) in [
		(
			"event(LaterRegistrationGeneralReceiveOpened(LATER_REGISTRATION_FAITHFUL_WITNESS,session,next_sequence(next_sequence(first_sequence())),sender,beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ3_PAYLOAD,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(receiver)),LATER_REGISTRATION_SEQ3_PAYLOAD),frame)).",
			"later-registration exact opened-payload query",
		),
		(
			"event(LaterRegistrationReturned(LATER_REGISTRATION_FAITHFUL_WITNESS,LATER_REGISTRATION_SEQ3_PAYLOAD)).",
			"later-registration exact return query",
		),
		(
			"event(LaterRegistrationFirstOnlyGateReached(LATER_REGISTRATION_FIRST_ONLY_WITNESS,next_sequence(next_sequence(first_sequence())),candidate)).",
			"later-registration counterfactual gate reachability query",
		),
		(
			"event(LaterRegistrationFirstOnlyGatePassed(LATER_REGISTRATION_FIRST_ONLY_WITNESS,next_sequence(next_sequence(first_sequence())),candidate)).",
			"later-registration counterfactual gate-pass query",
		),
		(
			"queryattacker(LATER_REGISTRATION_FIRST_ONLY_CANARY).",
			"later-registration counterfactual canary query",
		),
	] {
		require_once(&queries, wanted, label)?;
	}
	for event in [
		"LaterRegistrationOriginalResponseIssued",
		"LaterRegistrationSubstitutionSelected",
		"LaterRegistrationFaithfulAttempted",
		"LaterRegistrationCommitted",
		"LaterRegistrationServerFrameSent",
		"LaterRegistrationFirstOnlyAttempted",
	] {
		if !queries.contains(&format!("inj-event({event}(")) {
			return Err(format!(
				"missing later-registration origin correspondence: {event}"
			));
		}
	}
	if count(&queries, "==>inj-event(") != 5 {
		return Err("later-registration correspondence query count changed".to_owned());
	}
	let query_hashes = queries
		.split("query")
		.skip(1)
		.map(stable_text_hash)
		.collect::<Vec<_>>();
	if let Some((index, (actual, expected))) = query_hashes
		.iter()
		.zip(LATER_REGISTRATION_QUERY_HASHES)
		.enumerate()
		.find(|(_, (actual, expected))| **actual != *expected)
	{
		return Err(format!(
			"later-registration exact query {} changed: expected {expected}, found {actual}",
			index + 1
		));
	}

	let main = compact(&uncommented_pv(&snapshot.later_registration_main)?);
	if main != "processLaterSequenceRegistrationControl()" {
		return Err(format!("later-registration main process changed: {main}"));
	}
	let checker = section_between(
		&snapshot.proverif_result_checker,
		"} else if (scenario == \"later-sequence-registration\") {",
		"} else if (scenario == \"baseline\" ||",
		"later-registration result-checker branch",
	)?;
	for (wanted, label) in [
		(
			"if (query_count != 18)",
			"later-registration checker query count",
		),
		(
			"for (later_index = 1; later_index <= 18; later_index++)",
			"later-registration checker complete result loop",
		),
		(
			"later_expected[11] = \"Query not event(LaterRegistrationFirstOnlyGatePassed",
			"later-registration checker unreachable gate-pass polarity",
		),
		(
			"later_expected[12] = \"Query not event(LaterRegistrationCommitted(LATER_REGISTRATION_FIRST_ONLY_WITNESS[]",
			"later-registration checker unreachable counterfactual commit",
		),
		(
			"later_expected[13] = \"Query not attacker(LATER_REGISTRATION_FIRST_ONLY_CANARY[]) is true.\"",
			"later-registration checker canary secrecy polarity",
		),
	] {
		require_once(checker, wanted, label)?;
	}
	for index in 1..=18 {
		require_once(
			checker,
			&format!("later_expected[{index}] ="),
			"later-registration checker expected result",
		)?;
		let next = if index == 18 {
			"for (later_index = 1; later_index <= 18; later_index++)".to_owned()
		} else {
			format!("later_expected[{}] =", index + 1)
		};
		let assignment = section_between(
			checker,
			&format!("later_expected[{index}] ="),
			&next,
			"later-registration checker assignment",
		)?;
		let polarity = if index <= 10 { "is false." } else { "is true." };
		require_once(
			assignment,
			polarity,
			"later-registration checker exact polarity",
		)?;
	}
	let checker_hash = stable_text_hash(&compact(checker));
	if checker_hash != LATER_REGISTRATION_CHECKER_HASH {
		return Err(format!(
			"later-registration exact result-checker branch changed: expected {LATER_REGISTRATION_CHECKER_HASH}, found {checker_hash}"
		));
	}

	Ok(())
}

fn validate(snapshot: &Snapshot) -> Result<(), String> {
	validate_manifest(&snapshot.interface)?;
	validate_pv(snapshot)?;
	validate_phase1_source(snapshot)?;
	validate_phase2_source(snapshot)?;
	validate_cryptoframe_source(snapshot)?;
	validate_endpoint_frame_context_wiring(snapshot)?;
	validate_ratchet_effect_driver(snapshot)?;
	validate_finite_receive_state_fixture(snapshot)?;
	validate_registration_lifecycle(snapshot)?;
	validate_initial_ratchet_fidelity(snapshot)?;
	validate_later_registration_fidelity(snapshot)?;
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

fn replace_nth_once(source: &mut String, from: &str, to: &str, occurrence: usize) {
	let mut search_start = 0usize;
	for current in 0..=occurrence {
		let relative = source[search_start..]
			.find(from)
			.unwrap_or_else(|| panic!("mutation anchor missing: {from} occurrence {occurrence}"));
		let start = search_start + relative;
		if current == occurrence {
			source.replace_range(start..start + from.len(), to);
			return;
		}
		search_start = start + from.len();
	}
}

fn replace_nth_call_argument_after(
	source: &mut String,
	scope_marker: &str,
	function: &str,
	call_index: usize,
	argument_index: usize,
	replacement: &str,
) {
	let scope_start = source
		.find(scope_marker)
		.unwrap_or_else(|| panic!("mutation scope missing: {scope_marker}"));
	let call_marker = format!("{function}(");
	let mut search_start = scope_start;
	for current in 0..=call_index {
		let relative = source[search_start..]
			.find(&call_marker)
			.unwrap_or_else(|| panic!("mutation call missing: {function} #{call_index}"));
		let call_start = search_start + relative;
		let open = call_start + call_marker.len() - 1;
		let (mut arguments, end) = parse_call(source, open).unwrap();
		if current == call_index {
			assert!(
				argument_index < arguments.len(),
				"mutation argument missing: {function} #{call_index} argument #{argument_index}"
			);
			arguments[argument_index] = replacement.to_owned();
			source.replace_range(open + 1..end - 1, &arguments.join(","));
			return;
		}
		search_start = end;
	}
	unreachable!();
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

fn assert_ratchet_driver_rejected(
	name: &str,
	diagnostic: &str,
	mutate: impl FnOnce(&mut Snapshot),
) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate_ratchet_effect_driver(&snapshot) {
		Ok(()) => panic!("ratchet driver mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"ratchet driver mutation {name} produced wrong diagnostic: {error}"
	);
}

fn assert_finite_receive_fixture_rejected(
	name: &str,
	diagnostic: &str,
	mutate: impl FnOnce(&mut Snapshot),
) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate_finite_receive_state_fixture(&snapshot) {
		Ok(()) => panic!("finite receive-state fixture mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"finite receive-state fixture mutation {name} produced wrong diagnostic: {error}"
	);
}

fn assert_registration_lifecycle_rejected(
	name: &str,
	diagnostic: &str,
	mutate: impl FnOnce(&mut Snapshot),
) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate_manifest(&snapshot.interface)
		.and_then(|()| validate_registration_lifecycle(&snapshot))
	{
		Ok(()) => panic!("registration lifecycle mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"registration lifecycle mutation {name} produced wrong diagnostic: {error}"
	);
}

fn assert_initial_ratchet_rejected(
	name: &str,
	diagnostic: &str,
	mutate: impl FnOnce(&mut Snapshot),
) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate_manifest(&snapshot.interface)
		.and_then(|()| validate_initial_ratchet_fidelity(&snapshot))
	{
		Ok(()) => panic!("initial ratchet mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"initial ratchet mutation {name} produced wrong diagnostic: {error}"
	);
}

fn assert_later_registration_rejected(
	name: &str,
	diagnostic: &str,
	mutate: impl FnOnce(&mut Snapshot),
) {
	let mut snapshot = Snapshot::production();
	mutate(&mut snapshot);
	let error = match validate_manifest(&snapshot.interface)
		.and_then(|()| validate_later_registration_fidelity(&snapshot))
		.and_then(|()| validate_makefile(&snapshot.makefile))
	{
		Ok(()) => panic!("later-registration mutation survived: {name}"),
		Err(error) => error,
	};
	assert!(
		error.contains(diagnostic),
		"later-registration mutation {name} produced wrong diagnostic: {error}"
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
fn initial_ratchet_source_model_fidelity_is_exact_and_nonvacuous() {
	validate_manifest(INTERFACE).unwrap();
	validate_initial_ratchet_fidelity(&Snapshot::production()).unwrap();
	let facts = parse_facts(INTERFACE).unwrap();
	assert_eq!(
		facts
			.iter()
			.filter(|fact| fact.starts_with("initial_ratchet."))
			.count(),
		71
	);

	let root = core::array::from_fn::<_, 32, _>(|index| index as u8);
	let output = core::array::from_fn::<_, 64, _>(|index| (index as u8).wrapping_add(1));
	let server = pqxdh::resume_initial_ratchet_kdf(
		pqxdh::start_server_ratchet_kdf(&root),
		InitialRatchetKdfResponse::from_bytes(output),
	);
	let beacon = pqxdh::resume_initial_ratchet_kdf(
		pqxdh::start_beacon_ratchet_kdf(&root),
		InitialRatchetKdfResponse::from_bytes(output),
	);
	assert_eq!(
		server.send_chain().as_bytes(),
		beacon.receive_chain().as_bytes()
	);
	assert_eq!(
		server.receive_chain().as_bytes(),
		beacon.send_chain().as_bytes()
	);
	assert_eq!(server.send_chain().as_bytes(), &output[0..32]);
	assert_eq!(server.receive_chain().as_bytes(), &output[32..64]);
}

#[test]
fn later_registration_sequence_three_poststate_is_exact_and_nonvacuous() {
	validate_manifest(INTERFACE).unwrap();
	validate_later_registration_fidelity(&Snapshot::production()).unwrap();
	let facts = parse_facts(INTERFACE).unwrap();
	assert_eq!(
		facts
			.iter()
			.filter(|fact| fact.starts_with("later_registration."))
			.count(),
		68
	);

	fn response(key: u8, next_chain: u8, nonce: u8) -> RatchetKdfResponse {
		let mut bytes = [0u8; RATCHET_KDF_OUTPUT_SIZE];
		bytes[..32].fill(key);
		bytes[32..64].fill(next_chain);
		bytes[64..].fill(nonce);
		RatchetKdfResponse::from_bytes(bytes)
	}

	let send_chain = [0x31; 32];
	let chain1 = [0x41; 32];
	let chain2 = [0x42; 32];
	let chain3 = [0x43; 32];
	let chain4 = [0x44; 32];
	let kernel = ConcreteRatchetKernel::new(
		RatchetChain::from_bytes(send_chain),
		RatchetChain::from_bytes(chain1),
	);
	let ReceiveEffect::ReceiveKdfRequested(first) = begin_receive(kernel, 3, "seq3 payload") else {
		panic!("fresh sequence-three receive must request its first derivation");
	};
	assert_eq!(first.request().input(), &chain1);
	let ReceiveEffect::ReceiveKdfRequested(second) = first.resume(response(0x11, 0x42, 0x91))
	else {
		panic!("sequence-three receive must stage sequence one");
	};
	assert_eq!(second.request().input(), &chain2);
	let ReceiveEffect::ReceiveKdfRequested(third) = second.resume(response(0x22, 0x43, 0x92))
	else {
		panic!("sequence-three receive must stage sequence two");
	};
	assert_eq!(third.request().input(), &chain3);
	let ReceiveEffect::ReceiveOpenRequested(open) = third.resume(response(0x33, 0x44, 0x93)) else {
		panic!("sequence-three target must produce one open capability");
	};
	assert_eq!(open.sequence(), 3);
	assert_eq!(open.context(), &"seq3 payload");
	let target = open.material().expect("sequence-three target material");
	assert_eq!(target.key().as_bytes(), &[0x33; 32]);
	assert_eq!(target.nonce().as_bytes(), &[0x93; 12]);
	let (kernel, returned) = open.finish(Some("seq3 remainder"));

	assert_eq!(returned, Some("seq3 remainder"));
	assert_eq!(kernel.send_sequence(), 0);
	assert_eq!(kernel.send_chain().as_bytes(), &send_chain);
	assert_eq!(kernel.receive_sequence(), 3);
	assert_eq!(kernel.receive_chain().as_bytes(), &chain4);
	assert_eq!(kernel.receive_cache_len(), 2);
	let (sequence1, material1) = kernel.receive_entry_at(0).expect("cached sequence one");
	assert_eq!(sequence1, 1);
	assert_eq!(material1.key().as_bytes(), &[0x11; 32]);
	assert_eq!(material1.nonce().as_bytes(), &[0x91; 12]);
	let (sequence2, material2) = kernel.receive_entry_at(1).expect("cached sequence two");
	assert_eq!(sequence2, 2);
	assert_eq!(material2.key().as_bytes(), &[0x22; 32]);
	assert_eq!(material2.nonce().as_bytes(), &[0x92; 12]);
	assert!(kernel.receive_entry_at(2).is_none());
	assert!(
		(0..kernel.receive_cache_len())
			.filter_map(|slot| kernel.receive_entry_at(slot))
			.all(|(sequence, material)| sequence != 3 && material.key().as_bytes() != &[0x33; 32])
	);
}

const LATER_REGISTRATION_MUTATION_COUNT: usize = 409;

#[test]
fn later_registration_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;

	for fact in EXPECTED_FACTS
		.iter()
		.filter(|fact| fact.starts_with("later_registration."))
	{
		let key = fact.split_once('=').unwrap().0;
		assert_later_registration_rejected(
			&format!("later_registration_fact_{key}"),
			key,
			|snapshot| mutate_fact(&mut snapshot.interface, key, "mutated"),
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"later_registration_beacon_pending_state_swapped",
			"BeaconState::InitSent { control, .. } => *control,",
			"BeaconState::Established { control, .. } => *control,",
			"later-registration Beacon pending-state entry",
		),
		(
			"later_registration_beacon_response_reader_bypassed",
			"let response = typed_reader.get().ok()?;",
			"let response = replacement_response;",
			"later-registration Beacon response reader",
		),
		(
			"later_registration_beacon_finish_identity_substituted",
			"response_server_identity: *response_server.as_bytes(),",
			"response_server_identity: *self.server_id.as_bytes(),",
			"later-registration Beacon finish inputs",
		),
		(
			"later_registration_beacon_assigned_id_substituted",
			"assigned_key_id: response.get_key_id(),",
			"assigned_key_id: candidate.server_key_id(),",
			"later-registration Beacon finish inputs",
		),
		(
			"later_registration_beacon_shared_secrets_substituted",
			"shared_secrets: shared_secrets(dh1, dh2, dh3, dh4, &kem_shared)?,",
			"shared_secrets: replacement_shared_secrets,",
			"later-registration Beacon finish inputs",
		),
		(
			"later_registration_beacon_associated_data_substituted",
			"let associated_data = *candidate.associated_data();",
			"let associated_data = replacement_associated_data;",
			"later-registration Beacon candidate associated data",
		),
		(
			"later_registration_beacon_sender_substituted",
			"let authenticated_server_key_id = decrypted.key_id;",
			"let authenticated_server_key_id = candidate.server_key_id();",
			"later-registration Beacon authenticated sender",
		),
		(
			"later_registration_beacon_plaintext_substituted",
			"let mut authenticated_plaintext = decrypted.plaintext;",
			"let mut authenticated_plaintext = replacement_plaintext;",
			"later-registration Beacon authenticated plaintext",
		),
		(
			"later_registration_beacon_binding_length_gate_removed",
			"if authenticated_plaintext.len() <= verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE {",
			"if false {",
			"later-registration Beacon binding-length gate",
		),
		(
			"later_registration_beacon_plaintext_split_shifted",
			"authenticated_plaintext.split_off(verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE)",
			"authenticated_plaintext.split_off(0)",
			"later-registration Beacon returned remainder split",
		),
		(
			"later_registration_beacon_binding_substituted",
			"let binding = authenticated_plaintext.as_slice().try_into().ok()?;",
			"let binding = replacement_binding;",
			"later-registration Beacon assigned-ID binding prefix",
		),
		(
			"later_registration_beacon_staged_ratchet_substituted",
			"Some((authenticated, associated_data, ratchet, plaintext))",
			"Some((authenticated, associated_data, replacement_ratchet, plaintext))",
			"later-registration Beacon staged tuple",
		),
		(
			"later_registration_beacon_committed_ratchet_substituted",
			"associated_data,\n\t\t\tratchet,\n\t\t};",
			"associated_data,\n\t\t\tratchet: replacement_ratchet,\n\t\t};",
			"later-registration Beacon ratchet commit",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon {",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	for (name, argument, replacement) in [
		(
			"later_registration_beacon_frame_substituted",
			0usize,
			"replacement_frame",
		),
		(
			"later_registration_beacon_expected_sender_substituted",
			1,
			"replacement_sender",
		),
		(
			"later_registration_beacon_open_ad_substituted",
			2,
			"&replacement_associated_data",
		),
		(
			"later_registration_beacon_open_ratchet_substituted",
			3,
			"&mut replacement_ratchet",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration Beacon general receive handoff",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.adapter_beacon,
					"impl ProviderBeacon for Beacon {",
					"decrypt_message_with_ratchet",
					0,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (name, argument, replacement) in [
		(
			"later_registration_beacon_binding_candidate_substituted",
			0usize,
			"replacement_candidate",
		),
		(
			"later_registration_beacon_binding_sender_substituted",
			1,
			"candidate.server_key_id()",
		),
		(
			"later_registration_beacon_binding_prefix_substituted",
			2,
			"replacement_binding",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration Beacon binding authentication",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.adapter_beacon,
					"impl ProviderBeacon for Beacon {",
					"verified_pqxdh::authenticate_registration_key_id_binding",
					0,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_beacon_reads_decrypted_sequence",
		"later-registration Beacon first-sequence gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon {",
				"let authenticated_server_key_id = decrypted.key_id;",
				"let _registration_sequence = decrypted.seq;\n\t\t\tlet authenticated_server_key_id = decrypted.key_id;",
			);
		},
	);
	mutation_count += 1;
	assert_later_registration_rejected(
		"later_registration_beacon_adds_first_sequence_gate",
		"later-registration Beacon first-sequence gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon {",
				"let authenticated_server_key_id = decrypted.key_id;",
				"if decrypted.seq != 1 { return None; }\n\t\t\tlet authenticated_server_key_id = decrypted.key_id;",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"later_registration_adapter_sequence_substituted",
			"let key_seq = frame.get_seq();",
			"let key_seq = expected_sender_kid;",
			"later-registration adapter parsed sequence",
		),
		(
			"later_registration_adapter_kernel_substituted",
			"let kernel = ratchet.refined.take();",
			"let kernel = replacement_kernel;",
			"later-registration adapter entry kernel",
		),
		(
			"later_registration_adapter_request_substituted",
			"ratchet_hkdf(pending.request())",
			"ratchet_hkdf(replacement_request)",
			"later-registration adapter exact KDF continuation",
		),
		(
			"later_registration_adapter_pending_substituted",
			"pending.resume(response)",
			"replacement_pending.resume(response)",
			"later-registration adapter exact KDF continuation",
		),
		(
			"later_registration_adapter_open_material_substituted",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(replacement_material, open.sequence(), open.context())",
			"later-registration adapter exact open capability",
		),
		(
			"later_registration_adapter_open_sequence_substituted",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, key_seq, open.context())",
			"later-registration adapter exact open capability",
		),
		(
			"later_registration_adapter_open_context_substituted",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, open.sequence(), replacement_context)",
			"later-registration adapter exact open capability",
		),
		(
			"later_registration_adapter_finish_substituted",
			"open.finish(opened)",
			"open.finish(replacement_opened)",
			"later-registration adapter receive completion",
		),
		(
			"later_registration_adapter_result_sequence_substituted",
			"seq: key_seq,",
			"seq: 1,",
			"later-registration adapter result metadata",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet(",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	for (name, argument, replacement) in [
		(
			"later_registration_adapter_begin_kernel_substituted",
			0usize,
			"replacement_kernel",
		),
		(
			"later_registration_adapter_begin_sequence_substituted",
			1,
			"key_seq.wrapping_add(1)",
		),
		(
			"later_registration_adapter_begin_context_substituted",
			2,
			"replacement_context",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration adapter general receive start",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.adapter_ratchet,
					"pub(crate) fn decrypt_message_with_ratchet(",
					"verified_ratchet::begin_receive",
					0,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_adapter_adds_first_sequence_gate",
		"later-registration adapter first-sequence gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet(",
				"let key_seq = frame.get_seq();",
				"let key_seq = frame.get_seq();\n\tif key_seq != 1 { return None; }",
			);
		},
	);
	mutation_count += 1;

	for (name, source, marker, from, to, diagnostic) in [
		(
			"later_registration_core_max_gap_changed",
			"control",
			"pub const RATCHET_MAX_GAP",
			"50",
			"49",
			"later-registration core maximum gap",
		),
		(
			"later_registration_core_plan_difference_changed",
			"control",
			"pub(crate) fn plan_receive_until(",
			"target - state.receive_sequence",
			"target.saturating_sub(state.receive_sequence)",
			"later-registration core future receive plan",
		),
		(
			"later_registration_core_plan_skipped_changed",
			"control",
			"pub(crate) fn plan_receive_until(",
			"derivations - 1",
			"derivations",
			"later-registration core future receive plan",
		),
		(
			"later_registration_core_plan_bound_removed",
			"control",
			"pub(crate) fn plan_receive_until(",
			"skipped > RATCHET_MAX_GAP || cached > RATCHET_MAX_GAP - skipped",
			"false",
			"later-registration core future receive plan",
		),
		(
			"later_registration_core_skipped_cache_bypassed",
			"control",
			"pub(crate) fn advance_receive(",
			"state.receive_cache.append(next)",
			"replacement_cache.append(next)",
			"later-registration core skipped-key advance",
		),
		(
			"later_registration_core_target_counter_substituted",
			"control",
			"pub(crate) fn advance_receive_target(",
			"receive_sequence: next",
			"receive_sequence: state.receive_sequence",
			"later-registration core target advance",
		),
		(
			"later_registration_core_begin_plan_substituted",
			"concrete",
			"pub fn begin_receive<Context>(",
			"plan_receive_until(kernel.refined.control, target)",
			"plan_receive_until(kernel.refined.control, target + 1)",
			"later-registration core begin plan",
		),
		(
			"later_registration_core_begin_first_slot_substituted",
			"concrete",
			"pub fn begin_receive<Context>(",
			"kernel.refined.control.receive_cache_len()",
			"0",
			"later-registration core first live cache slot",
		),
		(
			"later_registration_core_begin_remaining_substituted",
			"concrete",
			"pub fn begin_receive<Context>(",
			"let remaining = plan.derivations as u8;",
			"let remaining = skipped as u8;",
			"later-registration core remaining derivations",
		),
		(
			"later_registration_core_begin_empty_preflight_inverted",
			"concrete",
			"pub fn begin_receive<Context>(",
			"!refined_receive_slots_are_empty",
			"refined_receive_slots_are_empty",
			"later-registration core empty destination preflight",
		),
		(
			"later_registration_core_begin_request_uses_send_chain",
			"concrete",
			"pub fn begin_receive<Context>(",
			"kernel.refined.receive_chain.as_bytes()",
			"kernel.refined.send_chain.as_bytes()",
			"later-registration core initial receive-chain request",
		),
		(
			"later_registration_core_begin_entry_substituted",
			"concrete",
			"pub fn begin_receive<Context>(",
			"ReceiveEffect::ReceiveKdfRequested(ReceiveKdf {\n\t\tentry: kernel,",
			"ReceiveEffect::ReceiveKdfRequested(ReceiveKdf {\n\t\tentry: replacement_kernel,",
			"later-registration core private receive staging",
		),
		(
			"later_registration_core_begin_skipped_not_zero",
			"concrete",
			"ReceiveEffect::ReceiveKdfRequested(ReceiveKdf {",
			"skipped: 0,",
			"skipped: 1,",
			"later-registration core private receive staging",
		),
		(
			"later_registration_core_final_branch_shifted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"self.remaining == 1",
			"self.remaining == 2",
			"later-registration core final-target branch",
		),
		(
			"later_registration_core_final_target_guard_removed",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"if !(sequence == self.target) {",
			"if false {",
			"later-registration core final target equality gate",
		),
		(
			"later_registration_core_pending_chain_substituted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"final_receive_chain: stepped.chain,",
			"final_receive_chain: replacement_chain,",
			"later-registration core pending target separation",
		),
		(
			"later_registration_core_pending_material_substituted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"target_material: stepped.material,",
			"target_material: replacement_material,",
			"later-registration core pending target separation",
		),
		(
			"later_registration_core_final_validation_bypassed",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"if !pending_receive_is_valid(&self.entry.refined, &pending, self.target) {",
			"if false {",
			"later-registration core final pending validation gate",
		),
		(
			"later_registration_core_nonfinal_uses_target_advance",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"advance_receive(self.working_control)",
			"advance_receive_target(self.working_control)",
			"later-registration core nonfinal skipped step",
		),
		(
			"later_registration_core_staged_sequence_substituted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"CachedReceiveKey {\n\t\t\tsequence,",
			"CachedReceiveKey {\n\t\t\tsequence: self.target,",
			"later-registration core skipped material pair",
		),
		(
			"later_registration_core_staged_material_substituted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"self.staged_slots[slot_index] = Some(CachedReceiveKey {\n\t\t\tsequence,\n\t\t\tmaterial: stepped.material,",
			"self.staged_slots[slot_index] = Some(CachedReceiveKey {\n\t\t\tsequence,\n\t\t\tmaterial: replacement_material,",
			"later-registration core skipped material pair",
		),
		(
			"later_registration_core_next_request_substituted",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"SymmetricRatchetKdfRequest::new(*stepped.chain.as_bytes())",
			"SymmetricRatchetKdfRequest::new(*self.entry.refined.receive_chain.as_bytes())",
			"later-registration core next receive request",
		),
		(
			"later_registration_core_skipped_counter_not_incremented",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"self.skipped += 1;",
			"self.skipped += 0;",
			"later-registration core next receive request",
		),
		(
			"later_registration_core_remaining_not_decremented",
			"concrete",
			"impl<Context> ReceiveKdf<Context>",
			"self.remaining -= 1;",
			"self.remaining -= 0;",
			"later-registration core next receive request",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			let selected = if source == "control" {
				&mut snapshot.core_ratchet_control
			} else {
				&mut snapshot.core_ratchet_concrete
			};
			replace_once_after(selected, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"later_registration_refined_pending_target_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"pending.target_sequence == requested",
			"pending.target_sequence == requested + 1",
			"later-registration exact pending target validation",
		),
		(
			"later_registration_refined_first_slot_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"pending.first_slot == state.control.receive_cache_len()",
			"pending.first_slot == 0",
			"later-registration first live slot validation",
		),
		(
			"later_registration_refined_send_counter_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"pending.committed_control.send_sequence() == state.control.send_sequence()",
			"pending.committed_control.send_sequence() == 0",
			"later-registration unchanged send counter validation",
		),
		(
			"later_registration_refined_receive_counter_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"pending.committed_control.receive_sequence() == requested",
			"pending.committed_control.receive_sequence() == requested + 1",
			"later-registration target receive counter validation",
		),
		(
			"later_registration_refined_skipped_relation_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"requested - entry_receive_sequence == pending.skipped as u64 + 1",
			"requested - entry_receive_sequence == pending.skipped as u64",
			"later-registration skipped-prefix validation",
		),
		(
			"later_registration_refined_target_absence_removed",
			"pub(super) fn pending_receive_is_valid<",
			"lookup_receive_key(pending.committed_control, requested).is_some()",
			"false",
			"later-registration target cache absence validation",
		),
		(
			"later_registration_refined_cache_length_substituted",
			"pub(super) fn pending_receive_is_valid<",
			"pending.committed_control.receive_cache_len() as usize == committed_len",
			"pending.committed_control.receive_cache_len() as usize <= committed_len",
			"later-registration exact cache-length validation",
		),
		(
			"later_registration_refined_cache_prefix_bypassed",
			"pub(super) fn pending_receive_is_valid<",
			"receive_control_prefix_matches(\n\t\tstate.control,",
			"receive_control_prefix_matches(\n\t\tpending.committed_control,",
			"later-registration committed cache-prefix validation",
		),
		(
			"later_registration_refined_staged_validation_bypassed",
			"pub(super) fn pending_receive_is_valid<",
			"pending_receive_slots_are_valid(\n\t\tstate,",
			"pending_receive_slots_are_valid(\n\t\tunsafe_state,",
			"later-registration staged-slot prefix validation",
		),
		(
			"later_registration_empty_scan_bounds_removed",
			"pub(super) fn refined_receive_slots_are_empty<",
			"if slot_index >= RECEIVE_CACHE_CAPACITY {",
			"if false {",
			"later-registration empty destination scan",
		),
		(
			"later_registration_empty_scan_accepts_occupied",
			"pub(super) fn refined_receive_slots_are_empty<",
			"state.receive_slots[slot_index].is_some()",
			"state.receive_slots[slot_index].is_none()",
			"later-registration empty destination scan",
		),
		(
			"later_registration_empty_scan_does_not_advance",
			"pub(super) fn refined_receive_slots_are_empty<",
			"slot += 1;",
			"slot += 0;",
			"later-registration empty destination scan",
		),
		(
			"later_registration_empty_scan_does_not_terminate",
			"pub(super) fn refined_receive_slots_are_empty<",
			"left -= 1;",
			"left -= 0;",
			"later-registration empty destination scan",
		),
		(
			"later_registration_staged_scan_accepts_live_slot",
			"pub(super) fn pending_receive_slots_are_valid<",
			"state.receive_slots[slot_index].is_some()",
			"state.receive_slots[slot_index].is_none()",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_uses_live_material",
			"pub(super) fn pending_receive_slots_are_valid<",
			"pending.staged_slots[slot_index].as_ref()",
			"state.receive_slots[slot_index].as_ref()",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_accepts_missing",
			"pub(super) fn pending_receive_slots_are_valid<",
			"None => return false,",
			"None => continue,",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_sequence_substituted",
			"pub(super) fn pending_receive_slots_are_valid<",
			"staged.sequence == expected",
			"staged.sequence == expected + 1",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_control_pairing_removed",
			"pub(super) fn pending_receive_slots_are_valid<",
			"pending.committed_control.receive_key_at(current_slot) == Some(expected)",
			"pending.committed_control.receive_key_at(current_slot).is_some()",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_does_not_advance_slot",
			"pub(super) fn pending_receive_slots_are_valid<",
			"current_slot += 1;",
			"current_slot += 0;",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_does_not_advance_sequence",
			"pub(super) fn pending_receive_slots_are_valid<",
			"expected += 1;",
			"expected += 0;",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_staged_scan_does_not_terminate",
			"pub(super) fn pending_receive_slots_are_valid<",
			"left -= 1;",
			"left -= 0;",
			"later-registration staged slot pairing scan",
		),
		(
			"later_registration_publisher_first_bound_removed",
			"pub(super) fn publish_future_receive<",
			"if first_index > RECEIVE_CACHE_CAPACITY {",
			"if false {",
			"later-registration future publication order",
		),
		(
			"later_registration_publisher_range_bound_removed",
			"pub(super) fn publish_future_receive<",
			"if skipped > RECEIVE_CACHE_CAPACITY - first_index {",
			"if false {",
			"later-registration future publication order",
		),
		(
			"later_registration_publisher_slots_bypassed",
			"pub(super) fn publish_future_receive<",
			"publish_future_receive_slots(\n\t\tstate,",
			"publish_future_receive_slots(\n\t\treplacement_state,",
			"later-registration future publication order",
		),
		(
			"later_registration_publisher_chain_substituted",
			"pub(super) fn publish_future_receive<",
			"state.receive_chain = pending.final_receive_chain;",
			"state.receive_chain = replacement_chain;",
			"later-registration future publication order",
		),
		(
			"later_registration_publisher_control_substituted",
			"pub(super) fn publish_future_receive<",
			"state.control = pending.committed_control;",
			"state.control = replacement_control;",
			"later-registration future publication order",
		),
		(
			"later_registration_publisher_inserts_target",
			"pub(super) fn publish_future_receive<",
			"let skipped = pending.skipped as usize;",
			"let _target_material = &pending.target_material;\n\tlet skipped = pending.skipped as usize;",
			"later-registration target material publication",
		),
		(
			"later_registration_slot_mover_uses_reference",
			"pub(super) fn publish_future_receive_slots<",
			"staged_slots[slot_index].take()",
			"staged_slots[slot_index].as_ref()",
			"later-registration exact skipped-slot movement",
		),
		(
			"later_registration_slot_mover_wrong_destination",
			"pub(super) fn publish_future_receive_slots<",
			"state.receive_slots[slot_index] = moved;",
			"state.receive_slots[0] = moved;",
			"later-registration exact skipped-slot movement",
		),
		(
			"later_registration_slot_mover_does_not_advance",
			"pub(super) fn publish_future_receive_slots<",
			"current_slot += 1;",
			"current_slot += 0;",
			"later-registration exact skipped-slot movement",
		),
		(
			"later_registration_slot_mover_does_not_terminate",
			"pub(super) fn publish_future_receive_slots<",
			"left -= 1;",
			"left -= 0;",
			"later-registration exact skipped-slot movement",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_refined, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, _function, from, to, diagnostic) in [
		(
			"later_registration_open_sequence_uses_cached_target",
			"sequence",
			"pending.target_sequence",
			"pending.committed_control.receive_sequence()",
			"later-registration future open sequence",
		),
		(
			"later_registration_open_material_uses_staged_slot",
			"material",
			"Some(&pending.target_material)",
			"pending.staged_slots[0].as_ref().map(|cached| &cached.material)",
			"later-registration future open material",
		),
		(
			"later_registration_open_finish_skips_publication",
			"finish",
			"publish_future_receive(&mut entry.refined, pending);",
			"drop(pending);",
			"later-registration success-only publication",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.core_ratchet_concrete,
				"impl<Context> ReceiveOpen<Context>",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, source, from, diagnostic) in [
		(
			"later_registration_lean_begin_future_anchor_removed",
			"effect",
			"theorem ratchet.concrete.begin_receive_future_request_exact",
			"later-registration structural Lean anchor",
		),
		(
			"later_registration_lean_future_sequence_anchor_removed",
			"effect",
			"theorem ratchet.concrete.ReceiveOpen.future_sequence_exact",
			"later-registration structural Lean anchor",
		),
		(
			"later_registration_lean_future_material_anchor_removed",
			"effect",
			"theorem ratchet.concrete.ReceiveOpen.future_material_exact",
			"later-registration structural Lean anchor",
		),
		(
			"later_registration_lean_future_finish_anchor_removed",
			"effect",
			"theorem ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext",
			"later-registration structural Lean anchor",
		),
		(
			"later_registration_lean_max_gap_anchor_removed",
			"control",
			"theorem max_gap_eq :",
			"later-registration control Lean anchor",
		),
		(
			"later_registration_lean_plan_accept_anchor_removed",
			"control",
			"theorem plan_receive_until_accept (",
			"later-registration control Lean anchor",
		),
		(
			"later_registration_lean_plan_bound_anchor_removed",
			"control",
			"theorem plan_receive_until_bound (",
			"later-registration control Lean anchor",
		),
		(
			"later_registration_lean_advance_skipped_anchor_removed",
			"control",
			"theorem advance_receive_ok (",
			"later-registration control Lean anchor",
		),
		(
			"later_registration_lean_advance_target_anchor_removed",
			"control",
			"theorem advance_receive_target_ok (",
			"later-registration control Lean anchor",
		),
		(
			"later_registration_lean_receive_refinement_anchor_removed",
			"refinement",
			"theorem receiveMessage_refines",
			"later-registration refinement Lean anchor",
		),
		(
			"later_registration_lean_state_neutral_anchor_removed",
			"refinement",
			"theorem receiveMessage_state_neutral",
			"later-registration refinement Lean anchor",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			let selected = match source {
				"effect" => &mut snapshot.lean_ratchet_effect,
				"control" => &mut snapshot.lean_ratchet_control,
				_ => &mut snapshot.lean_ratchet_refinement,
			};
			replace_once(
				selected,
				from,
				&from.replacen("theorem", "theorem mutated", 1),
			);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"later_registration_pv_zero_sequence_type_changed",
			"fun zero_sequence()",
			"fun zero_sequence(): sequence",
			"fun zero_sequence(): bitstring",
			"later-registration zero sequence constructor",
		),
		(
			"later_registration_pv_ratchet_state_constructor_renamed",
			"fun later_registration_ratchet_state(",
			"later_registration_ratchet_state",
			"later_registration_other_state",
			"later-registration ratchet-state constructor",
		),
		(
			"later_registration_pv_return_constructor_renamed",
			"fun later_registration_return(",
			"later_registration_return",
			"later_registration_other_return",
			"later-registration return constructor",
		),
		(
			"later_registration_pv_seq1_payload_renamed",
			"free LATER_REGISTRATION_SEQ1_PAYLOAD",
			"LATER_REGISTRATION_SEQ1_PAYLOAD",
			"LATER_REGISTRATION_OTHER_PAYLOAD",
			"later-registration sequence-one payload",
		),
		(
			"later_registration_pv_seq2_payload_renamed",
			"free LATER_REGISTRATION_SEQ2_PAYLOAD",
			"LATER_REGISTRATION_SEQ2_PAYLOAD",
			"LATER_REGISTRATION_OTHER_PAYLOAD",
			"later-registration sequence-two payload",
		),
		(
			"later_registration_pv_seq3_payload_renamed",
			"free LATER_REGISTRATION_SEQ3_PAYLOAD",
			"LATER_REGISTRATION_SEQ3_PAYLOAD",
			"LATER_REGISTRATION_OTHER_PAYLOAD",
			"later-registration sequence-three payload",
		),
		(
			"later_registration_pv_commit_event_renamed",
			"event LaterRegistrationCommitted(",
			"LaterRegistrationCommitted",
			"LaterRegistrationOtherCommitted",
			"later-registration committed event signature",
		),
		(
			"later_registration_pv_target_event_renamed",
			"event LaterRegistrationTargetUnavailable(",
			"LaterRegistrationTargetUnavailable",
			"LaterRegistrationTargetAvailable",
			"later-registration target-absence event signature",
		),
		(
			"later_registration_pv_response_fields_swapped",
			"let LaterSequenceRegistrationOpen(",
			"app_ciphertext,\n    assigned_key_id",
			"assigned_key_id,\n    app_ciphertext",
			"later-registration response field parse",
		),
		(
			"later_registration_pv_outer_identity_gate_removed",
			"let LaterSequenceRegistrationOpen(",
			"if response_server_identity = expected_server_identity then",
			"if response_server_identity = response_server_identity then",
			"later-registration Beacon root reconstruction",
		),
		(
			"later_registration_pv_root_input_substituted",
			"let LaterSequenceRegistrationOpen(",
			"beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)",
			"replacement_root_input",
			"later-registration Beacon root reconstruction",
		),
		(
			"later_registration_pv_associated_data_identity_substituted",
			"let LaterSequenceRegistrationOpen(",
			"expected_server_identity,\n        beacon_identity",
			"response_server_identity,\n        beacon_identity",
			"later-registration reconstructed associated data",
		),
		(
			"later_registration_pv_session_assigned_id_substituted",
			"let LaterSequenceRegistrationOpen(",
			"assigned_key_id,\n      root_input",
			"expected_server_key_id,\n      root_input",
			"later-registration reconstructed session",
		),
		(
			"later_registration_pv_chain2_substituted",
			"let LaterSequenceRegistrationOpen(",
			"let server_chain_2 = ratchet_next(server_chain_1)",
			"let server_chain_2 = ratchet_next(root)",
			"later-registration receive chain expansion",
		),
		(
			"later_registration_pv_chain4_substituted",
			"let LaterSequenceRegistrationOpen(",
			"let server_chain_4 = ratchet_next(server_chain_3)",
			"let server_chain_4 = ratchet_next(server_chain_2)",
			"later-registration receive chain expansion",
		),
		(
			"later_registration_pv_material2_substituted",
			"let LaterSequenceRegistrationOpen(",
			"let server_material_2 = ratchet_material(server_chain_2)",
			"let server_material_2 = ratchet_material(server_chain_1)",
			"later-registration receive material expansion",
		),
		(
			"later_registration_pv_frame_sequence_sender_swapped",
			"let LaterSequenceRegistrationOpen(",
			"frame_sequence,\n      authenticated_server_key_id",
			"authenticated_server_key_id,\n      frame_sequence",
			"later-registration inner frame parse",
		),
		(
			"later_registration_pv_sender_gate_removed",
			"let LaterSequenceRegistrationOpen(",
			"if authenticated_server_key_id = expected_server_key_id then",
			"if authenticated_server_key_id = authenticated_server_key_id then",
			"later-registration authenticated sender gate",
		),
		(
			"later_registration_pv_opened_payload_fields_swapped",
			"let LaterSequenceRegistrationOpen(",
			"authenticated_binding,\n        registration_plaintext",
			"registration_plaintext,\n        authenticated_binding",
			"later-registration opened payload parse",
		),
		(
			"later_registration_pv_receive_state_sequence_substituted",
			"let LaterSequenceRegistrationOpen(",
			"frame_sequence,\n        server_chain_4,",
			"first_sequence(),\n        server_chain_4,",
			"later-registration receive poststate",
		),
		(
			"later_registration_pv_ratchet_send_counter_substituted",
			"let LaterSequenceRegistrationOpen(",
			"zero_sequence(),\n        beacon_to_server_chain(root),",
			"first_sequence(),\n        beacon_to_server_chain(root),",
			"later-registration complete ratchet poststate",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.later_registration_control, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, argument, replacement, diagnostic) in [
		(
			"later_registration_pv_open_material_substituted",
			0usize,
			"server_material_2",
			"later-registration generic sequence open",
		),
		(
			"later_registration_pv_open_ad_substituted",
			1,
			"replacement_associated_data",
			"later-registration generic sequence open",
		),
		(
			"later_registration_pv_open_sequence_substituted",
			2,
			"first_sequence()",
			"later-registration generic sequence open",
		),
		(
			"later_registration_pv_open_sender_substituted",
			3,
			"authenticated_server_key_id",
			"later-registration generic sequence open",
		),
		(
			"later_registration_pv_open_frame_substituted",
			4,
			"replacement_frame",
			"later-registration generic sequence open",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_nth_call_argument_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationOpen(",
				"open_frame",
				0,
				argument,
				replacement,
			);
		});
		mutation_count += 1;
	}

	for (name, function, call, argument, replacement, diagnostic) in [
		(
			"later_registration_pv_cache1_sequence_substituted",
			"receive_cache_entry",
			0usize,
			0usize,
			"next_sequence(first_sequence())",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_cache1_material_substituted",
			"receive_cache_entry",
			0,
			1,
			"server_material_2",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_cache1_tail_substituted",
			"receive_cache_entry",
			0,
			2,
			"replacement_cache",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_cache2_sequence_substituted",
			"receive_cache_entry",
			1,
			0,
			"first_sequence()",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_cache2_material_substituted",
			"receive_cache_entry",
			1,
			1,
			"server_material_1",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_cache2_tail_substituted",
			"receive_cache_entry",
			1,
			2,
			"receive_cache_empty()",
			"later-registration exact newest-first cache",
		),
		(
			"later_registration_pv_receive_state_sequence_substitution",
			"receive_state",
			0,
			0,
			"first_sequence()",
			"later-registration receive poststate",
		),
		(
			"later_registration_pv_receive_state_chain_substitution",
			"receive_state",
			0,
			1,
			"server_chain_3",
			"later-registration receive poststate",
		),
		(
			"later_registration_pv_receive_state_cache_substitution",
			"receive_state",
			0,
			2,
			"cache_1",
			"later-registration receive poststate",
		),
		(
			"later_registration_pv_ratchet_send_sequence_substitution",
			"later_registration_ratchet_state",
			0,
			0,
			"first_sequence()",
			"later-registration complete ratchet poststate",
		),
		(
			"later_registration_pv_ratchet_send_chain_substitution",
			"later_registration_ratchet_state",
			0,
			1,
			"server_to_beacon_chain(root)",
			"later-registration complete ratchet poststate",
		),
		(
			"later_registration_pv_ratchet_receive_state_substitution",
			"later_registration_ratchet_state",
			0,
			2,
			"replacement_receive_state",
			"later-registration complete ratchet poststate",
		),
		(
			"later_registration_pv_opened_event_sequence_substituted",
			"LaterRegistrationGeneralReceiveOpened",
			0,
			2,
			"first_sequence()",
			"later-registration opened event fields",
		),
		(
			"later_registration_pv_opened_event_payload_substituted",
			"LaterRegistrationGeneralReceiveOpened",
			0,
			6,
			"registration_plaintext",
			"later-registration opened event fields",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_nth_call_argument_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationOpen(",
				function,
				call,
				argument,
				replacement,
			);
		});
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_pv_open_reply_target_material_omitted",
		"later-registration open reply fields",
		|snapshot| {
			replace_once_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationOpen(",
				"          server_material_3,\n          cache_2,",
				"          cache_2,",
			);
		},
	);
	mutation_count += 1;

	for (name, marker, from, to, diagnostic) in [
		(
			"later_registration_pv_expected_binding_substituted",
			"let LaterSequenceRegistrationCommit(",
			"key_id_encoding(assigned_key_id)",
			"key_id_encoding(authenticated_server_key_id)",
			"later-registration binding-to-commit order",
		),
		(
			"later_registration_pv_binding_gate_bypassed",
			"let LaterSequenceRegistrationCommit(",
			"phase2_assigned_id_binding_gate(\n    authenticated_binding,\n    expected_binding\n  )",
			"phase2_assigned_id_binding_gate(\n    expected_binding,\n    expected_binding\n  )",
			"later-registration binding-to-commit order",
		),
		(
			"later_registration_pv_return_payload_substituted",
			"let LaterSequenceRegistrationCommit(",
			"event LaterRegistrationReturned(witness, registration_plaintext);",
			"event LaterRegistrationReturned(witness, opened_payload);",
			"later-registration binding-to-commit order",
		),
		(
			"later_registration_pv_return_term_substituted",
			"let LaterSequenceRegistrationCommit(",
			"later_registration_return(witness, registration_plaintext)",
			"later_registration_return(witness, opened_payload)",
			"later-registration binding-to-commit order",
		),
		(
			"later_registration_pv_canary_witness_substituted",
			"let LaterSequenceRegistrationCommit(",
			"if witness = LATER_REGISTRATION_FIRST_ONLY_WITNESS then",
			"if witness = LATER_REGISTRATION_FAITHFUL_WITNESS then",
			"later-registration counterfactual canary confinement",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.later_registration_control, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, function, argument, replacement, diagnostic) in [
		(
			"later_registration_pv_poststate_send_counter_substituted",
			"LaterRegistrationPoststatePublished",
			3usize,
			"frame_sequence",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_poststate_send_chain_substituted",
			"LaterRegistrationPoststatePublished",
			4,
			"server_chain_4",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_poststate_receive_counter_substituted",
			"LaterRegistrationPoststatePublished",
			5,
			"first_sequence()",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_poststate_receive_chain_substituted",
			"LaterRegistrationPoststatePublished",
			6,
			"server_chain_3",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_poststate_cache_substituted",
			"LaterRegistrationPoststatePublished",
			7,
			"cache_1",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_poststate_ratchet_substituted",
			"LaterRegistrationPoststatePublished",
			8,
			"replacement_ratchet",
			"later-registration exact poststate event",
		),
		(
			"later_registration_pv_target_sequence_substituted",
			"LaterRegistrationTargetUnavailable",
			2,
			"first_sequence()",
			"later-registration target-absence event",
		),
		(
			"later_registration_pv_target_material_substituted",
			"LaterRegistrationTargetUnavailable",
			3,
			"server_material_2",
			"later-registration target-absence event",
		),
		(
			"later_registration_pv_target_cache_substituted",
			"LaterRegistrationTargetUnavailable",
			4,
			"cache_1",
			"later-registration target-absence event",
		),
		(
			"later_registration_pv_target_ratchet_substituted",
			"LaterRegistrationTargetUnavailable",
			5,
			"replacement_ratchet",
			"later-registration target-absence event",
		),
		(
			"later_registration_pv_commit_response_substituted",
			"LaterRegistrationCommitted",
			3,
			"replacement_response",
			"later-registration commit event",
		),
		(
			"later_registration_pv_commit_sender_substituted",
			"LaterRegistrationCommitted",
			5,
			"assigned_key_id",
			"later-registration commit event",
		),
		(
			"later_registration_pv_commit_opened_payload_substituted",
			"LaterRegistrationCommitted",
			7,
			"registration_plaintext",
			"later-registration commit event",
		),
		(
			"later_registration_pv_commit_frame_substituted",
			"LaterRegistrationCommitted",
			9,
			"replacement_frame",
			"later-registration commit event",
		),
		(
			"later_registration_pv_commit_material_substituted",
			"LaterRegistrationCommitted",
			10,
			"server_material_2",
			"later-registration commit event",
		),
		(
			"later_registration_pv_commit_state_substituted",
			"LaterRegistrationCommitted",
			11,
			"replacement_state",
			"later-registration commit event",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_nth_call_argument_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationCommit(",
				function,
				0,
				argument,
				replacement,
			);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"later_registration_pv_faithful_attempt_response_substituted",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"LATER_REGISTRATION_FAITHFUL_WITNESS,\n    response",
			"LATER_REGISTRATION_FAITHFUL_WITNESS,\n    replacement_response",
			"later-registration faithful attempt",
		),
		(
			"later_registration_pv_faithful_open_witness_substituted",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"LaterSequenceRegistrationOpen(\n      LATER_REGISTRATION_FAITHFUL_WITNESS,",
			"LaterSequenceRegistrationOpen(\n      LATER_REGISTRATION_FIRST_ONLY_WITNESS,",
			"later-registration faithful shared open",
		),
		(
			"later_registration_pv_faithful_open_response_substituted",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"      response,\n      reply\n    )",
			"      replacement_response,\n      reply\n    )",
			"later-registration faithful shared open",
		),
		(
			"later_registration_pv_faithful_commit_witness_substituted",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"LaterSequenceRegistrationCommit(\n      LATER_REGISTRATION_FAITHFUL_WITNESS,",
			"LaterSequenceRegistrationCommit(\n      LATER_REGISTRATION_FIRST_ONLY_WITNESS,",
			"later-registration faithful direct commit",
		),
		(
			"later_registration_pv_faithful_commit_response_substituted",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"      LATER_REGISTRATION_FAITHFUL_WITNESS,\n      response,",
			"      LATER_REGISTRATION_FAITHFUL_WITNESS,\n      replacement_response,",
			"later-registration faithful direct commit",
		),
		(
			"later_registration_pv_faithful_adds_sequence_gate",
			"let LaterSequenceRegistrationFaithfulFinish(",
			"    LaterSequenceRegistrationCommit(",
			"    if frame_sequence = first_sequence() then\n      LaterSequenceRegistrationCommit(",
			"later-registration faithful sequence gate",
		),
		(
			"later_registration_pv_first_only_attempt_response_substituted",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"LATER_REGISTRATION_FIRST_ONLY_WITNESS,\n    response",
			"LATER_REGISTRATION_FIRST_ONLY_WITNESS,\n    replacement_response",
			"later-registration counterfactual attempt",
		),
		(
			"later_registration_pv_first_only_open_witness_substituted",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"LaterSequenceRegistrationOpen(\n      LATER_REGISTRATION_FIRST_ONLY_WITNESS,",
			"LaterSequenceRegistrationOpen(\n      LATER_REGISTRATION_FAITHFUL_WITNESS,",
			"later-registration counterfactual post-open gate placement",
		),
		(
			"later_registration_pv_first_only_gate_reached_removed",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"event LaterRegistrationFirstOnlyGateReached(",
			"event LaterRegistrationFirstOnlyGateSkipped(",
			"later-registration counterfactual post-open gate placement",
		),
		(
			"later_registration_pv_first_only_gate_condition_changed",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"if frame_sequence = first_sequence() then",
			"if frame_sequence = next_sequence(first_sequence()) then",
			"later-registration counterfactual post-open gate placement",
		),
		(
			"later_registration_pv_first_only_gate_passed_removed",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"event LaterRegistrationFirstOnlyGatePassed(",
			"event LaterRegistrationFirstOnlyGateSkipped(",
			"later-registration counterfactual post-open gate placement",
		),
		(
			"later_registration_pv_first_only_commit_witness_substituted",
			"let LaterSequenceRegistrationFirstOnlyFinish(",
			"LaterSequenceRegistrationCommit(\n        LATER_REGISTRATION_FIRST_ONLY_WITNESS,",
			"LaterSequenceRegistrationCommit(\n        LATER_REGISTRATION_FAITHFUL_WITNESS,",
			"later-registration counterfactual post-open gate placement",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.later_registration_control, marker, from, to);
		});
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_pv_first_only_gate_moved_before_open_reply",
		"later-registration counterfactual post-open gate placement",
		|snapshot| {
			replace_once_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationFirstOnlyFinish(",
				"    event LaterRegistrationFirstOnlyGateReached(\n      LATER_REGISTRATION_FIRST_ONLY_WITNESS,\n      frame_sequence,\n      response\n    );\n",
				"",
			);
			replace_once_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationFirstOnlyFinish(",
				"    in(\n      reply,",
				"    event LaterRegistrationFirstOnlyGateReached(\n      LATER_REGISTRATION_FIRST_ONLY_WITNESS,\n      frame_sequence,\n      response\n    );\n    in(\n      reply,",
			);
		},
	);
	mutation_count += 1;

	for (name, marker, from, to, diagnostic) in [
		(
			"later_registration_pv_coordinator_root_substituted",
			"let LaterSequenceRegistrationControl() =",
			"beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)",
			"replacement_root_input",
			"later-registration Server root construction",
		),
		(
			"later_registration_pv_coordinator_ad_order_swapped",
			"let LaterSequenceRegistrationControl() =",
			"server_identity,\n      beacon_identity",
			"beacon_identity,\n      server_identity",
			"later-registration coordinator associated data",
		),
		(
			"later_registration_pv_coordinator_session_root_substituted",
			"let LaterSequenceRegistrationControl() =",
			"assigned_key_id,\n    root_input",
			"assigned_key_id,\n    replacement_root_input",
			"later-registration coordinator session",
		),
		(
			"later_registration_pv_coordinator_binding_substituted",
			"let LaterSequenceRegistrationControl() =",
			"key_id_encoding(assigned_key_id)",
			"key_id_encoding(server_key_id)",
			"later-registration coordinator binding",
		),
		(
			"later_registration_pv_first_frame_material_substituted",
			"let LaterSequenceRegistrationControl() =",
			"let first_frame = seal_frame(\n    server_material_1,",
			"let first_frame = seal_frame(\n    server_material_2,",
			"later-registration genuine first frame",
		),
		(
			"later_registration_pv_first_frame_payload_substituted",
			"let LaterSequenceRegistrationControl() =",
			"LATER_REGISTRATION_SEQ1_PAYLOAD\n    )",
			"LATER_REGISTRATION_SEQ3_PAYLOAD\n    )",
			"later-registration genuine first frame",
		),
		(
			"later_registration_pv_second_frame_sequence_substituted",
			"let LaterSequenceRegistrationControl() =",
			"next_sequence(first_sequence()),\n    server_key_id,\n    LATER_REGISTRATION_SEQ2_PAYLOAD",
			"first_sequence(),\n    server_key_id,\n    LATER_REGISTRATION_SEQ2_PAYLOAD",
			"later-registration genuine second frame",
		),
		(
			"later_registration_pv_third_frame_material_substituted",
			"let LaterSequenceRegistrationControl() =",
			"let third_frame = seal_frame(\n    server_material_3,",
			"let third_frame = seal_frame(\n    server_material_2,",
			"later-registration genuine third frame",
		),
		(
			"later_registration_pv_third_frame_sender_substituted",
			"let LaterSequenceRegistrationControl() =",
			"next_sequence(next_sequence(first_sequence())),\n    server_key_id,",
			"next_sequence(next_sequence(first_sequence())),\n    assigned_key_id,",
			"later-registration genuine third frame",
		),
		(
			"later_registration_pv_third_frame_binding_removed",
			"let LaterSequenceRegistrationControl() =",
			"registration_payload(\n      assigned_binding,\n      LATER_REGISTRATION_SEQ3_PAYLOAD\n    )",
			"LATER_REGISTRATION_SEQ3_PAYLOAD",
			"later-registration genuine third frame",
		),
		(
			"later_registration_pv_original_response_frame_substituted",
			"let LaterSequenceRegistrationControl() =",
			"kem_ciphertext,\n    first_frame,\n    assigned_key_id",
			"kem_ciphertext,\n    third_frame,\n    assigned_key_id",
			"later-registration original response",
		),
		(
			"later_registration_pv_substitution_outer_identity_changed",
			"let substituted_response = kex_response(",
			"server_identity,",
			"beacon_identity,",
			"later-registration app-frame-only substitution",
		),
		(
			"later_registration_pv_substitution_ephemeral_changed",
			"let substituted_response = kex_response(",
			"server_ephemeral,",
			"replacement_ephemeral,",
			"later-registration app-frame-only substitution",
		),
		(
			"later_registration_pv_substitution_kem_changed",
			"let substituted_response = kex_response(",
			"kem_ciphertext,",
			"replacement_kem_ciphertext,",
			"later-registration app-frame-only substitution",
		),
		(
			"later_registration_pv_substitution_frame_changed",
			"let substituted_response = kex_response(",
			"third_frame,",
			"second_frame,",
			"later-registration app-frame-only substitution",
		),
		(
			"later_registration_pv_substitution_assigned_id_changed",
			"let substituted_response = kex_response(",
			"assigned_key_id\n  )",
			"server_key_id\n  )",
			"later-registration app-frame-only substitution",
		),
		(
			"later_registration_pv_candidate_gate_bypassed",
			"let LaterSequenceRegistrationControl() =",
			"if candidate = substituted_response then",
			"if candidate = candidate then",
			"later-registration single candidate selection",
		),
		(
			"later_registration_pv_substitution_event_original_changed",
			"event LaterRegistrationSubstitutionSelected(",
			"original_response,\n      candidate",
			"candidate,\n      candidate",
			"later-registration exact substitution event",
		),
		(
			"later_registration_pv_original_output_moved_before_event",
			"let LaterSequenceRegistrationControl() =",
			"event LaterRegistrationOriginalResponseIssued(\n    LATER_REGISTRATION_ORIGINAL_WITNESS,\n    session,\n    root,\n    first_frame,\n    original_response\n  );\n  out(c, original_response);",
			"out(c, original_response);\n  event LaterRegistrationOriginalResponseIssued(\n    LATER_REGISTRATION_ORIGINAL_WITNESS,\n    session,\n    root,\n    first_frame,\n    original_response\n  );",
			"later-registration genuine response and later-frame order",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.later_registration_control, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, function, replacement, diagnostic) in [
		(
			"later_registration_pv_faithful_fanout_candidate_substituted",
			"LaterSequenceRegistrationFaithfulFinish",
			"replacement_candidate",
			"later-registration faithful fanout",
		),
		(
			"later_registration_pv_first_only_fanout_candidate_substituted",
			"LaterSequenceRegistrationFirstOnlyFinish",
			"replacement_candidate",
			"later-registration counterfactual fanout",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			let calls = all_arguments(
				&compact(&uncommented_pv(&snapshot.later_registration_control).unwrap()),
				function,
			)
			.unwrap();
			let last = calls[1].len() - 1;
			replace_nth_call_argument_after(
				&mut snapshot.later_registration_control,
				"let LaterSequenceRegistrationControl() =",
				function,
				0,
				last,
				replacement,
			);
		});
		mutation_count += 1;
	}

	for query_index in 0..18 {
		let diagnostic = if query_index == 12 {
			"later-registration counterfactual canary query".to_owned()
		} else {
			format!("later-registration exact query {} changed", query_index + 1)
		};
		assert_later_registration_rejected(
			&format!(
				"later_registration_query_{}_formula_mutated",
				query_index + 1
			),
			&diagnostic,
			|snapshot| {
				replace_nth_once(
					&mut snapshot.later_registration_queries,
					"query ",
					"query not ",
					query_index,
				);
			},
		);
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_query_count_reduced",
		"later-registration query count changed",
		|snapshot| {
			replace_nth_once(
				&mut snapshot.later_registration_queries,
				"query ",
				"let mutated_query = ",
				0,
			);
		},
	);
	mutation_count += 1;

	for (name, marker, function, argument, replacement, diagnostic) in [
		(
			"later_registration_poststate_query_send_counter_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			3usize,
			"first_sequence()",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_send_chain_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			4,
			"wrong_send_chain()",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_receive_counter_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			5,
			"first_sequence()",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_live_chain_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			6,
			"wrong_chain_4()",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_order_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(first_sequence(), wrong_material_1(), receive_cache_entry(next_sequence(first_sequence()), wrong_material_2(), receive_cache_empty()))",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_seq2_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(first_sequence(), wrong_material_2(), receive_cache_empty())",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_material2_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(next_sequence(first_sequence()), wrong_material_2(), receive_cache_empty())",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_seq1_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(next_sequence(first_sequence()), wrong_material_2(), receive_cache_entry(next_sequence(first_sequence()), wrong_material_1(), receive_cache_empty()))",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_material1_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(next_sequence(first_sequence()), wrong_material_2(), receive_cache_entry(first_sequence(), wrong_material_1(), receive_cache_empty()))",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_cache_tail_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			7,
			"receive_cache_entry(next_sequence(first_sequence()), wrong_material_2(), receive_cache_entry(first_sequence(), wrong_material_1(), wrong_cache_tail()))",
			"later-registration exact poststate query",
		),
		(
			"later_registration_poststate_query_ratchet_mutated",
			"event(LaterRegistrationPoststatePublished(",
			"LaterRegistrationPoststatePublished",
			8,
			"wrong_ratchet_state()",
			"later-registration exact poststate query",
		),
		(
			"later_registration_target_query_sequence_mutated",
			"event(LaterRegistrationTargetUnavailable(",
			"LaterRegistrationTargetUnavailable",
			2,
			"first_sequence()",
			"later-registration exact target-absence query",
		),
		(
			"later_registration_target_query_material3_mutated",
			"event(LaterRegistrationTargetUnavailable(",
			"LaterRegistrationTargetUnavailable",
			3,
			"wrong_material_3()",
			"later-registration exact target-absence query",
		),
		(
			"later_registration_target_query_cache_mutated",
			"event(LaterRegistrationTargetUnavailable(",
			"LaterRegistrationTargetUnavailable",
			4,
			"wrong_cache()",
			"later-registration exact target-absence query",
		),
		(
			"later_registration_target_query_ratchet_mutated",
			"event(LaterRegistrationTargetUnavailable(",
			"LaterRegistrationTargetUnavailable",
			5,
			"wrong_ratchet_state()",
			"later-registration exact target-absence query",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_nth_call_argument_after(
				&mut snapshot.later_registration_queries,
				marker,
				function,
				0,
				argument,
				replacement,
			);
		});
		mutation_count += 1;
	}

	assert_later_registration_rejected(
		"later_registration_main_process_mutated",
		"later-registration main process changed",
		|snapshot| {
			replace_once(
				&mut snapshot.later_registration_main,
				"LaterSequenceRegistrationControl()",
				"OtherControl()",
			);
		},
	);
	mutation_count += 1;

	for index in 1..=18 {
		let diagnostic = match index {
			11 => "later-registration checker unreachable gate-pass polarity",
			12 => "later-registration checker unreachable counterfactual commit",
			13 => "later-registration checker canary secrecy polarity",
			_ => "later-registration exact result-checker branch changed",
		};
		assert_later_registration_rejected(
			&format!("later_registration_checker_result_{index}_term_mutated"),
			diagnostic,
			|snapshot| {
				replace_once_after(
					&mut snapshot.proverif_result_checker,
					&format!("later_expected[{index}] ="),
					"Query",
					"MutatedQuery",
				);
			},
		);
		mutation_count += 1;
	}
	for index in 1..=18 {
		let polarity = if index <= 10 { "is false." } else { "is true." };
		let replacement = if index <= 10 { "is true." } else { "is false." };
		let diagnostic = if index == 13 {
			"later-registration checker canary secrecy polarity"
		} else {
			"later-registration checker exact polarity"
		};
		assert_later_registration_rejected(
			&format!("later_registration_checker_result_{index}_polarity_mutated"),
			diagnostic,
			|snapshot| {
				replace_once_after(
					&mut snapshot.proverif_result_checker,
					&format!("later_expected[{index}] ="),
					polarity,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	assert_later_registration_rejected(
		"later_registration_checker_query_count_mutated",
		"later-registration checker query count",
		|snapshot| {
			replace_once_after(
				&mut snapshot.proverif_result_checker,
				"} else if (scenario == \"later-sequence-registration\") {",
				"if (query_count != 18)",
				"if (query_count != 17)",
			);
		},
	);
	mutation_count += 1;
	assert_later_registration_rejected(
		"later_registration_checker_loop_bound_mutated",
		"later-registration checker complete result loop",
		|snapshot| {
			replace_once_after(
				&mut snapshot.proverif_result_checker,
				"for (later_index = 1;",
				"later_index <= 18",
				"later_index <= 17",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"later_registration_make_scenario_removed",
			"\tlater-sequence-registration \\\n",
			"",
			"expected 29 ProVerif scenarios",
		),
		(
			"later_registration_make_extraction_prerequisite_removed",
			"check-proverif-later-sequence-registration: check-proverif-extraction",
			"check-proverif-later-sequence-registration:",
			"later-sequence registration extraction prerequisite",
		),
		(
			"later_registration_make_binding_theory_removed",
			"-lib $(PROVERIF_DIR)/phase2-assigned-id-strong-theory.pvl",
			"-lib $(PROVERIF_DIR)/phase2-assigned-id-weak-theory.pvl",
			"later-sequence registration binding theory",
		),
		(
			"later_registration_make_control_loader_removed",
			"-lib $(PROVERIF_DIR)/later-sequence-registration-control.pvl",
			"-lib $(PROVERIF_DIR)/other-control.pvl",
			"later-sequence registration control loader",
		),
		(
			"later_registration_make_query_loader_removed",
			"-lib $(PROVERIF_DIR)/later-sequence-registration-queries.pvl",
			"-lib $(PROVERIF_DIR)/other-queries.pvl",
			"later-sequence registration query loader",
		),
		(
			"later_registration_make_main_removed",
			"$(PROVERIF_DIR)/later-sequence-registration.pv |",
			"$(PROVERIF_DIR)/other.pv |",
			"later-sequence registration main model",
		),
		(
			"later_registration_make_checker_scenario_changed",
			"awk -v scenario=later-sequence-registration -f '$(PROVERIF_CHECKER)'",
			"awk -v scenario=other -f '$(PROVERIF_CHECKER)'",
			"later-sequence registration result checker",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.makefile,
				if name == "later_registration_make_scenario_removed" {
					"PROVERIF_SCENARIOS :="
				} else {
					"check-proverif-later-sequence-registration:"
				},
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, function, call, argument, replacement) in [
		(
			"later_registration_pv_beacon_server_kex_input_substituted",
			"x25519_public_from_ed",
			0usize,
			0usize,
			"expected_server_identity",
		),
		(
			"later_registration_pv_beacon_identity_input_substituted",
			"ed_public",
			0,
			0,
			"beacon_prekey_secret",
		),
		(
			"later_registration_pv_beacon_dh1_secret_substituted",
			"x25519_beacon_dh",
			0,
			0,
			"beacon_identity_secret",
		),
		(
			"later_registration_pv_beacon_dh1_peer_substituted",
			"x25519_beacon_dh",
			0,
			1,
			"server_ephemeral",
		),
		(
			"later_registration_pv_beacon_dh2_secret_substituted",
			"x25519_beacon_dh",
			1,
			0,
			"beacon_prekey_secret",
		),
		(
			"later_registration_pv_beacon_dh2_peer_substituted",
			"x25519_beacon_dh",
			1,
			1,
			"response_server_kex",
		),
		(
			"later_registration_pv_beacon_dh3_secret_substituted",
			"x25519_beacon_dh",
			2,
			0,
			"beacon_identity_secret",
		),
		(
			"later_registration_pv_beacon_dh3_peer_substituted",
			"x25519_beacon_dh",
			2,
			1,
			"response_server_kex",
		),
		(
			"later_registration_pv_beacon_dh4_secret_substituted",
			"x25519_beacon_dh",
			3,
			0,
			"beacon_prekey_secret",
		),
		(
			"later_registration_pv_beacon_dh4_peer_substituted",
			"x25519_beacon_dh",
			3,
			1,
			"response_server_kex",
		),
		(
			"later_registration_pv_beacon_kem_ciphertext_substituted",
			"mlkem_decapsulate",
			0,
			0,
			"replacement_ciphertext",
		),
		(
			"later_registration_pv_beacon_kem_secret_key_substituted",
			"mlkem_decapsulate",
			0,
			1,
			"replacement_pq_secret",
		),
		(
			"later_registration_pv_beacon_shared_dh_order_swapped",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets",
			0,
			0,
			"dh2",
		),
		(
			"later_registration_pv_beacon_shared_kem_substituted",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets",
			0,
			4,
			"replacement_kem_secret",
		),
		(
			"later_registration_pv_beacon_root_builder_substituted",
			"beaconcrypt_core__pqxdh__build_root_key_input",
			0,
			0,
			"replacement_shared_secrets",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration Beacon root reconstruction",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.later_registration_control,
					"let LaterSequenceRegistrationOpen(",
					function,
					call,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, function, call, argument, replacement) in [
		(
			"later_registration_pv_server_identity_public_substituted",
			"ed_public",
			0usize,
			0usize,
			"beacon_identity_secret",
		),
		(
			"later_registration_pv_server_beacon_identity_public_substituted",
			"ed_public",
			1,
			0,
			"server_identity_secret",
		),
		(
			"later_registration_pv_server_prekey_public_substituted",
			"x25519_public",
			0,
			0,
			"beacon_one_time_secret",
		),
		(
			"later_registration_pv_server_one_time_public_substituted",
			"x25519_public",
			1,
			0,
			"beacon_prekey_secret",
		),
		(
			"later_registration_pv_server_pq_public_substituted",
			"mlkem_public",
			0,
			0,
			"replacement_pq_secret",
		),
		(
			"later_registration_pv_server_ephemeral_public_substituted",
			"x25519_public",
			2,
			0,
			"beacon_prekey_secret",
		),
		(
			"later_registration_pv_server_kem_ciphertext_key_substituted",
			"mlkem_ciphertext",
			0,
			0,
			"replacement_pq",
		),
		(
			"later_registration_pv_server_kem_ciphertext_coins_substituted",
			"mlkem_ciphertext",
			0,
			1,
			"replacement_coins",
		),
		(
			"later_registration_pv_server_kem_secret_key_substituted",
			"mlkem_shared_secret",
			0,
			0,
			"replacement_pq",
		),
		(
			"later_registration_pv_server_kem_secret_coins_substituted",
			"mlkem_shared_secret",
			0,
			1,
			"replacement_coins",
		),
		(
			"later_registration_pv_server_dh1_secret_substituted",
			"x25519_server_dh",
			0,
			0,
			"server_ephemeral_secret",
		),
		(
			"later_registration_pv_server_dh1_peer_substituted",
			"x25519_server_dh",
			0,
			1,
			"beacon_one_time",
		),
		(
			"later_registration_pv_server_dh2_secret_substituted",
			"x25519_server_dh",
			1,
			0,
			"server_identity_secret",
		),
		(
			"later_registration_pv_server_dh2_peer_substituted",
			"x25519_server_dh",
			1,
			1,
			"beacon_prekey",
		),
		(
			"later_registration_pv_server_dh3_secret_substituted",
			"x25519_server_dh",
			2,
			0,
			"server_identity_secret",
		),
		(
			"later_registration_pv_server_dh3_peer_substituted",
			"x25519_server_dh",
			2,
			1,
			"beacon_one_time",
		),
		(
			"later_registration_pv_server_dh4_secret_substituted",
			"x25519_server_dh",
			3,
			0,
			"server_identity_secret",
		),
		(
			"later_registration_pv_server_dh4_peer_substituted",
			"x25519_server_dh",
			3,
			1,
			"beacon_prekey",
		),
		(
			"later_registration_pv_server_shared_dh_order_swapped",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets",
			0,
			0,
			"dh2",
		),
		(
			"later_registration_pv_server_shared_kem_substituted",
			"beaconcrypt_core__pqxdh__PqxdhSharedSecrets",
			0,
			4,
			"replacement_kem_secret",
		),
		(
			"later_registration_pv_server_root_builder_substituted",
			"beaconcrypt_core__pqxdh__build_root_key_input",
			0,
			0,
			"replacement_shared_secrets",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration Server root construction",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.later_registration_control,
					"let LaterSequenceRegistrationControl() =",
					function,
					call,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"later_registration_original_witness_visibility_changed",
			"free LATER_REGISTRATION_ORIGINAL_WITNESS: bitstring [private].",
			"free LATER_REGISTRATION_ORIGINAL_WITNESS: bitstring.",
			"later-registration original-response witness",
		),
		(
			"later_registration_substitution_witness_visibility_changed",
			"free LATER_REGISTRATION_SUBSTITUTION_WITNESS: bitstring [private].",
			"free LATER_REGISTRATION_SUBSTITUTION_WITNESS: bitstring.",
			"later-registration substitution witness",
		),
		(
			"later_registration_faithful_witness_visibility_changed",
			"free LATER_REGISTRATION_FAITHFUL_WITNESS: bitstring [private].",
			"free LATER_REGISTRATION_FAITHFUL_WITNESS: bitstring.",
			"later-registration faithful witness",
		),
		(
			"later_registration_counterfactual_witness_visibility_changed",
			"free LATER_REGISTRATION_FIRST_ONLY_WITNESS: bitstring [private].",
			"free LATER_REGISTRATION_FIRST_ONLY_WITNESS: bitstring.",
			"later-registration counterfactual witness",
		),
		(
			"later_registration_canary_visibility_changed",
			"free LATER_REGISTRATION_FIRST_ONLY_CANARY: bitstring [private].",
			"free LATER_REGISTRATION_FIRST_ONLY_CANARY: bitstring.",
			"later-registration counterfactual canary",
		),
		(
			"later_registration_original_event_signature_changed",
			"event LaterRegistrationOriginalResponseIssued(",
			"event LaterRegistrationOtherResponseIssued(",
			"later-registration original-response event signature",
		),
		(
			"later_registration_server_send_event_signature_changed",
			"event LaterRegistrationServerFrameSent(",
			"event LaterRegistrationOtherFrameSent(",
			"later-registration Server-send event signature",
		),
		(
			"later_registration_substitution_event_signature_changed",
			"event LaterRegistrationSubstitutionSelected(",
			"event LaterRegistrationOtherSubstitutionSelected(",
			"later-registration substitution event signature",
		),
		(
			"later_registration_faithful_attempt_event_signature_changed",
			"event LaterRegistrationFaithfulAttempted(",
			"event LaterRegistrationOtherFaithfulAttempted(",
			"later-registration faithful-attempt event signature",
		),
		(
			"later_registration_counterfactual_attempt_event_signature_changed",
			"event LaterRegistrationFirstOnlyAttempted(",
			"event LaterRegistrationOtherFirstOnlyAttempted(",
			"later-registration counterfactual-attempt event signature",
		),
		(
			"later_registration_opened_event_signature_changed",
			"event LaterRegistrationGeneralReceiveOpened(",
			"event LaterRegistrationOtherReceiveOpened(",
			"later-registration opened event signature",
		),
		(
			"later_registration_gate_reached_event_signature_changed",
			"event LaterRegistrationFirstOnlyGateReached(",
			"event LaterRegistrationOtherGateReached(",
			"later-registration gate-reached event signature",
		),
		(
			"later_registration_gate_passed_event_signature_changed",
			"event LaterRegistrationFirstOnlyGatePassed(",
			"event LaterRegistrationOtherGatePassed(",
			"later-registration gate-passed event signature",
		),
		(
			"later_registration_poststate_event_signature_changed",
			"event LaterRegistrationPoststatePublished(",
			"event LaterRegistrationOtherPoststatePublished(",
			"later-registration poststate event signature",
		),
		(
			"later_registration_returned_event_signature_changed",
			"event LaterRegistrationReturned(",
			"event LaterRegistrationOtherReturned(",
			"later-registration returned event signature",
		),
	] {
		assert_later_registration_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.later_registration_control, from, to);
		});
		mutation_count += 1;
	}

	for (name, function, call, argument, replacement) in [
		(
			"later_registration_original_event_root_substituted",
			"LaterRegistrationOriginalResponseIssued",
			0usize,
			2usize,
			"replacement_root",
		),
		(
			"later_registration_original_event_response_substituted",
			"LaterRegistrationOriginalResponseIssued",
			0,
			4,
			"third_frame",
		),
		(
			"later_registration_seq3_origin_session_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			0,
			"replacement_session",
		),
		(
			"later_registration_seq3_origin_root_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			1,
			"replacement_root",
		),
		(
			"later_registration_seq3_origin_response_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			2,
			"substituted_response",
		),
		(
			"later_registration_seq3_origin_sequence_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			3,
			"first_sequence()",
		),
		(
			"later_registration_seq3_origin_sender_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			4,
			"assigned_key_id",
		),
		(
			"later_registration_seq3_origin_payload_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			6,
			"LATER_REGISTRATION_SEQ2_PAYLOAD",
		),
		(
			"later_registration_seq3_origin_frame_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			7,
			"second_frame",
		),
		(
			"later_registration_seq3_origin_material_substituted",
			"LaterRegistrationServerFrameSent",
			2,
			8,
			"server_material_2",
		),
	] {
		assert_later_registration_rejected(
			name,
			"later-registration genuine response and later-frame order",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.later_registration_control,
					"let LaterSequenceRegistrationControl() =",
					function,
					call,
					argument,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	assert_eq!(mutation_count, LATER_REGISTRATION_MUTATION_COUNT);
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

const ENDPOINT_FRAME_CONTEXT_MUTATION_COUNT: usize = 242;

#[test]
fn endpoint_frame_context_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	let endpoint_facts = parse_facts(INTERFACE)
		.unwrap()
		.into_iter()
		.filter(|fact| fact.starts_with("endpoint."))
		.collect::<Vec<_>>();
	assert_eq!(endpoint_facts.len(), 56);
	for fact in endpoint_facts {
		let (key, _) = fact.split_once('=').unwrap();
		assert_rejected(&format!("endpoint_fact_{key}"), key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, "mutated");
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"endpoint_sender_parser_ignores_wire",
			"capnp::serialize::read_message(data, ReaderOptions::new())",
			"capnp::serialize::read_message(&[], ReaderOptions::new())",
			"endpoint Server wire-sender Cap'n Proto read",
		),
		(
			"endpoint_sender_parser_uses_phase2_type",
			"TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader)",
			"TypedReader::<_, crate::phase2_capnp::kex_response::Owned>::new(reader)",
			"endpoint Server wire-sender typed CryptoFrame reader",
		),
		(
			"endpoint_sender_parser_returns_sequence",
			"Some(typed_reader.get().ok()?.get_key_id())",
			"Some(typed_reader.get().ok()?.get_seq())",
			"endpoint Server wire-sender keyId getter",
		),
		(
			"endpoint_sender_parser_returns_constant",
			"Some(typed_reader.get().ok()?.get_key_id())",
			"Some(0)",
			"endpoint Server wire-sender keyId getter",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn encrypted_frame_sender",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to) in [
		(
			"endpoint_server_ad_reverses_identities",
			"build_associated_data(\n\t\t\tself.identity_pk().clone(),\n\t\t\tself.pk_by_kid(k)?.clone(),\n\t\t)",
			"build_associated_data(\n\t\t\tself.pk_by_kid(k)?.clone(),\n\t\t\tself.identity_pk().clone(),\n\t\t)",
		),
		(
			"endpoint_server_ad_selects_local_id",
			"self.pk_by_kid(k)?.clone()",
			"self.pk_by_kid(self.identity_key_kid)?.clone()",
		),
		(
			"endpoint_server_ad_uses_peer_twice",
			"self.identity_pk().clone()",
			"self.pk_by_kid(k)?.clone()",
		),
	] {
		assert_rejected(
			name,
			"endpoint Server server-first associated-data mapping",
			move |snapshot| {
				replace_once_after(&mut snapshot.adapter_server, "fn associated_data", from, to);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"endpoint_server_send_ad_uses_local_id",
			"let ad = self.associated_data(k)?;",
			"let ad = self.associated_data(self.identity_key_kid)?;",
			"endpoint Server send peer-associated data",
		),
		(
			"endpoint_server_send_sender_uses_peer_id",
			"let sender = self.identity_key_kid;",
			"let sender = k;",
			"endpoint Server send local sender",
		),
		(
			"endpoint_server_send_target_uses_local_sender",
			"encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)",
			"encrypt_message_with_ratchet(b, sender, sender, &ad, self.ratchet_manager_mut(k)?)",
			"endpoint Server send target/sender/context/ratchet mapping",
		),
		(
			"endpoint_server_send_wire_sender_uses_peer",
			"encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)",
			"encrypt_message_with_ratchet(b, k, k, &ad, self.ratchet_manager_mut(k)?)",
			"endpoint Server send target/sender/context/ratchet mapping",
		),
		(
			"endpoint_server_send_ratchet_uses_local_sender",
			"encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)",
			"encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(sender)?)",
			"endpoint Server send target/sender/context/ratchet mapping",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"pub fn encrypt_message(&mut self, b: &[u8], k: u64)",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"endpoint_server_receive_ignores_parsed_sender",
			"let Some(k) = crate::ratchet::encrypted_frame_sender(b) else {\n\t\t\treturn ReceiveTransition::Rejected;\n\t\t};",
			"let Some(_k) = crate::ratchet::encrypted_frame_sender(b) else {\n\t\t\treturn ReceiveTransition::Rejected;\n\t\t};\n\t\tlet k = self.identity_key_kid;",
			"endpoint Server parsed sender selector",
		),
		(
			"endpoint_server_receive_ad_uses_local_id",
			"self.associated_data(k)",
			"self.associated_data(self.identity_key_kid)",
			"endpoint Server receive selected-peer associated data",
		),
		(
			"endpoint_server_receive_ratchet_uses_local_id",
			"self.ratchet_manager_mut(k)",
			"self.ratchet_manager_mut(self.identity_key_kid)",
			"endpoint Server receive selected-peer ratchet",
		),
		(
			"endpoint_server_receive_expected_sender_uses_local_id",
			"decrypt_message_with_ratchet(b, k, &ad, ratchet)",
			"decrypt_message_with_ratchet(b, self.identity_key_kid, &ad, ratchet)",
			"endpoint Server receive expected-sender/context/ratchet mapping",
		),
		(
			"endpoint_server_receive_uses_zero_ad",
			"decrypt_message_with_ratchet(b, k, &ad, ratchet)",
			"decrypt_message_with_ratchet(b, k, &[0; AD_SIZE], ratchet)",
			"endpoint Server receive expected-sender/context/ratchet mapping",
		),
		(
			"endpoint_server_receive_rejects_successful_open",
			"Some(decrypted) => ReceiveTransition::Accepted(decrypted)",
			"Some(_decrypted) => ReceiveTransition::Rejected",
			"endpoint Server acceptance only after successful open",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn decrypt_message_transition",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"endpoint_beacon_send_sender_uses_server_id",
			"pub fn encrypt_message(&mut self, b: &[u8])",
			"let sender = self.identity_key_kid;",
			"let sender = self.server_kid();",
			"endpoint Beacon assigned sender snapshot",
		),
		(
			"endpoint_beacon_send_target_uses_assigned_id",
			"pub fn encrypt_message(&mut self, b: &[u8])",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, ratchet)",
			"encrypt_message_with_ratchet(b, sender, sender, associated_data, ratchet)",
			"endpoint Beacon send target/sender/stored context mapping",
		),
		(
			"endpoint_beacon_send_wire_sender_uses_server_id",
			"pub fn encrypt_message(&mut self, b: &[u8])",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, ratchet)",
			"encrypt_message_with_ratchet(b, control.server_key_id(), control.server_key_id(), associated_data, ratchet)",
			"endpoint Beacon send target/sender/stored context mapping",
		),
		(
			"endpoint_beacon_send_replaces_stored_ad",
			"pub fn encrypt_message(&mut self, b: &[u8])",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, ratchet)",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, &[0; AD_SIZE], ratchet)",
			"endpoint Beacon send target/sender/stored context mapping",
		),
		(
			"endpoint_beacon_receive_expected_sender_uses_assigned_id",
			"pub fn decrypt_message(&mut self, b: &[u8])",
			"decrypt_message_with_ratchet(b, control.server_key_id(), associated_data, ratchet)",
			"decrypt_message_with_ratchet(b, self.identity_key_kid, associated_data, ratchet)",
			"endpoint Beacon receive expected-sender/stored context mapping",
		),
		(
			"endpoint_beacon_receive_replaces_stored_ad",
			"pub fn decrypt_message(&mut self, b: &[u8])",
			"decrypt_message_with_ratchet(b, control.server_key_id(), associated_data, ratchet)",
			"decrypt_message_with_ratchet(b, control.server_key_id(), &[0; AD_SIZE], ratchet)",
			"endpoint Beacon receive expected-sender/stored context mapping",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.adapter_beacon, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"endpoint_registration_server_peer_identity_uses_local_identity",
			"crypto_sign::PublicKey::from_bytes(candidate.beacon_identity_public_key()).ok()?",
			"crypto_sign::PublicKey::from_bytes(candidate.server_identity_public_key()).ok()?",
			"endpoint registration Server candidate peer identity",
		),
		(
			"endpoint_registration_server_ratchet_uses_zero_root",
			"start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_server_candidate_ratchet_kdf(&candidate, &[0; 32])",
			"endpoint registration Server candidate ratchet",
		),
		(
			"endpoint_registration_server_rebuilds_candidate_ad",
			"let associated_data = *candidate.associated_data();",
			"let associated_data = self.associated_data(remote_kid)?;",
			"endpoint registration Server candidate associated data",
		),
		(
			"endpoint_registration_server_target_uses_local_id",
			"&authenticated_plaintext,\n\t\t\tremote_kid,\n\t\t\tcandidate.server_identity_key_id(),",
			"&authenticated_plaintext,\n\t\t\tcandidate.server_identity_key_id(),\n\t\t\tcandidate.server_identity_key_id(),",
			"endpoint registration Server initial target/sender/context/ratchet mapping",
		),
		(
			"endpoint_registration_server_sender_uses_assigned_id",
			"&authenticated_plaintext,\n\t\t\tremote_kid,\n\t\t\tcandidate.server_identity_key_id(),",
			"&authenticated_plaintext,\n\t\t\tremote_kid,\n\t\t\tremote_kid,",
			"endpoint registration Server initial target/sender/context/ratchet mapping",
		),
		(
			"endpoint_registration_server_initial_uses_zero_ad",
			"&associated_data,\n\t\t\t&mut ratchet,",
			"&[0; AD_SIZE],\n\t\t\t&mut ratchet,",
			"endpoint registration Server initial target/sender/context/ratchet mapping",
		),
		(
			"endpoint_registration_server_initial_uses_committed_ratchet",
			"&associated_data,\n\t\t\t&mut ratchet,",
			"&associated_data,\n\t\t\tself.ratchet_manager_mut(remote_kid)?,",
			"endpoint registration Server initial target/sender/context/ratchet mapping",
		),
		(
			"endpoint_registration_server_return_metadata_uses_local_id",
			"kid: remote_kid,",
			"kid: self.identity_key_kid,",
			"endpoint registration Server returned target metadata",
		),
		(
			"endpoint_registration_server_map_uses_local_id",
			".insert(remote_kid, EstablishedRemote::new(public_key, ratchet))",
			".insert(self.identity_key_kid, EstablishedRemote::new(public_key, ratchet))",
			"endpoint registration Server committed peer identity and candidate ratchet",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn build_registration_response",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"endpoint_registration_server_outer_key_id_uses_local_id",
		"Phase-2 server assigned-ID mapping",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn build_registration_response",
				"bundle.set_key_id(remote_kid);",
				"bundle.set_key_id(candidate.server_identity_key_id());",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"endpoint_registration_beacon_ratchet_uses_zero_root",
			"start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_beacon_candidate_ratchet_kdf(&candidate, &[0; 32])",
			"endpoint registration Beacon candidate ratchet",
		),
		(
			"endpoint_registration_beacon_replaces_candidate_ad",
			"let associated_data = *candidate.associated_data();",
			"let associated_data = [0; AD_SIZE];",
			"endpoint registration Beacon candidate associated data",
		),
		(
			"endpoint_registration_beacon_expected_sender_uses_outer_id",
			"candidate.server_key_id(),\n\t\t\t\t&associated_data,",
			"response.get_key_id(),\n\t\t\t\t&associated_data,",
			"Phase-2 beacon initial-frame mapping",
		),
		(
			"endpoint_registration_beacon_open_uses_zero_ad",
			"&associated_data,\n\t\t\t\t&mut ratchet,",
			"&[0; AD_SIZE],\n\t\t\t\t&mut ratchet,",
			"Phase-2 beacon initial-frame mapping",
		),
		(
			"endpoint_registration_beacon_open_discards_candidate_ratchet",
			"&associated_data,\n\t\t\t\t&mut ratchet,",
			"&associated_data,\n\t\t\t\tpanic!(),",
			"Phase-2 beacon initial-frame mapping",
		),
		(
			"endpoint_registration_beacon_handoff_replaces_ad",
			"Some((authenticated, associated_data, ratchet, plaintext))",
			"Some((authenticated, [0; AD_SIZE], ratchet, plaintext))",
			"endpoint registration Beacon candidate context handoff",
		),
		(
			"endpoint_registration_beacon_handoff_discards_ratchet",
			"Some((authenticated, associated_data, ratchet, plaintext))",
			"Some((authenticated, associated_data, panic!(), plaintext))",
			"endpoint registration Beacon candidate context handoff",
		),
		(
			"endpoint_registration_beacon_local_sender_uses_server_id",
			"self.identity_key_kid = authenticated.assigned_key_id();",
			"self.identity_key_kid = server_kid;",
			"endpoint registration Beacon assigned local sender",
		),
		(
			"endpoint_registration_beacon_state_replaces_ad",
			"associated_data,\n\t\t\tratchet,",
			"associated_data: [0; AD_SIZE],\n\t\t\tratchet,",
			"endpoint registration Beacon stores candidate context",
		),
		(
			"endpoint_registration_beacon_state_discards_ratchet",
			"associated_data,\n\t\t\tratchet,",
			"associated_data,\n\t\t\tratchet: panic!(),",
			"endpoint registration Beacon stores candidate context",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"endpoint_server_receive_fail_open",
		"endpoint Server acceptance only after successful open",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn decrypt_message_transition",
				"None => ReceiveTransition::Rejected",
				"None => ReceiveTransition::Accepted(panic!())",
			);
		},
	);
	mutation_count += 1;

	for (name, marker, from, to, diagnostic) in [
		(
			"endpoint_beacon_send_discards_stored_ratchet",
			"pub fn encrypt_message(&mut self, b: &[u8])",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, ratchet)",
			"encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, return None)",
			"endpoint Beacon send target/sender/stored context mapping",
		),
		(
			"endpoint_beacon_receive_discards_stored_ratchet",
			"pub fn decrypt_message(&mut self, b: &[u8])",
			"decrypt_message_with_ratchet(b, control.server_key_id(), associated_data, ratchet)",
			"decrypt_message_with_ratchet(b, control.server_key_id(), associated_data, return None)",
			"endpoint Beacon receive expected-sender/stored context mapping",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.adapter_beacon, marker, from, to);
		});
		mutation_count += 1;
	}
	assert_rejected(
		"endpoint_registration_server_remote_id_uses_local_id",
		"Phase-2 assigned key-ID source",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn build_registration_response",
				"let remote_kid = candidate.key_id();",
				"let remote_kid = candidate.server_identity_key_id();",
			);
		},
	);
	mutation_count += 1;
	for (name, from, to, diagnostic) in [
		(
			"endpoint_registration_server_materialization_discards_pending",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(panic!()))",
			"endpoint registration Server initial ratchet materialization",
		),
		(
			"endpoint_registration_server_map_discards_peer_identity",
			"EstablishedRemote::new(public_key, ratchet)",
			"EstablishedRemote::new(panic!(), ratchet)",
			"endpoint registration Server committed peer identity and candidate ratchet",
		),
		(
			"endpoint_registration_server_map_discards_post_send_ratchet",
			"EstablishedRemote::new(public_key, ratchet)",
			"EstablishedRemote::new(public_key, panic!())",
			"endpoint registration Server committed peer identity and candidate ratchet",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn build_registration_response",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"endpoint_registration_beacon_materialization_discards_pending",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(panic!()))",
			"endpoint registration Beacon initial ratchet materialization",
		),
		(
			"endpoint_registration_beacon_state_discards_authenticated_control",
			"control: verified_pqxdh::beacon_commit(authenticated),",
			"control: panic!(),",
			"endpoint registration Beacon stores candidate context",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_rejected(
		"endpoint_registration_beacon_assigns_local_id_before_server_binding_checks",
		"endpoint registration Beacon initial source order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {",
				"let server_binding = authenticated.server_binding();",
				"self.identity_key_kid = authenticated.assigned_key_id();\n\t\tlet server_binding = authenticated.server_binding();",
			);
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"if self.server_id.as_bytes() != &server_binding.identity_public_key",
				"self.identity_key_kid = authenticated.assigned_key_id();",
				"let _assigned_id_checked_above = authenticated.assigned_key_id();",
			);
		},
	);
	mutation_count += 1;

	assert_rejected(
		"endpoint_registration_server_publishes_control_before_peer_insert",
		"endpoint registration Server initial source order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn build_registration_response",
				"let old = self\n\t\t\t.known_ids\n\t\t\t.insert(remote_kid, EstablishedRemote::new(public_key, ratchet));\n\t\tdebug_assert!(old.is_none());\n\t\tself.control = next_control;",
				"self.control = next_control;\n\t\tlet old = self\n\t\t\t.known_ids\n\t\t\t.insert(remote_kid, EstablishedRemote::new(public_key, ratchet));\n\t\tdebug_assert!(old.is_none());",
			);
		},
	);
	mutation_count += 1;

	for (family, scope, function, calls, replacement, diagnostic) in [
		(
			"honest_beacon_server_open",
			"let HonestBeacon(",
			"open_frame",
			4usize,
			"assigned_key_id",
			"symbolic server-to-Beacon open wiring changed",
		),
		(
			"honest_beacon_send",
			"let HonestBeacon(",
			"seal_frame",
			1usize,
			"SERVER_KEY_ID",
			"symbolic Beacon-to-Server seal wiring",
		),
		(
			"server_send",
			"let Server(",
			"seal_frame",
			4usize,
			"assigned_key_id",
			"symbolic Server-to-Beacon seal wiring changed",
		),
		(
			"server_beacon_open",
			"let Server(",
			"open_frame",
			1usize,
			"SERVER_KEY_ID",
			"symbolic Server Beacon-frame open wiring",
		),
		(
			"malicious_registration_server_send",
			"let MaliciousServer(",
			"seal_frame",
			1usize,
			"assigned_key_id",
			"symbolic malicious-registration initial-frame wiring",
		),
	] {
		for call_index in 0..calls {
			for (argument_index, field, wrong_value) in [
				(0usize, "material", "server_identity"),
				(1usize, "associated_data", "server_identity"),
				(
					2usize,
					"sequence",
					"next_sequence(next_sequence(next_sequence(next_sequence(first_sequence()))))",
				),
				(3usize, "sender", replacement),
				(4usize, "payload", "server_identity"),
			] {
				assert_rejected(
					&format!("endpoint_symbolic_{family}_{field}_{call_index}"),
					diagnostic,
					move |snapshot| {
						replace_nth_call_argument_after(
							&mut snapshot.environment,
							scope,
							function,
							call_index,
							argument_index,
							wrong_value,
						);
					},
				);
				mutation_count += 1;
			}
		}
	}

	for (name, scope, marker, replacement, diagnostic) in [
		(
			"endpoint_symbolic_honest_server_open_count_increases",
			"let HonestBeacon(",
			"let opened_initial = open_frame(",
			"let endpoint_extra_open = open_frame(server_material_1, associated_data, first_sequence(), SERVER_KEY_ID, initial_frame) in\n    let opened_initial = open_frame(",
			"symbolic server-to-Beacon open wiring changed",
		),
		(
			"endpoint_symbolic_honest_beacon_seal_count_increases",
			"let HonestBeacon(",
			"let beacon_frame = seal_frame(",
			"let endpoint_extra_beacon_frame = seal_frame(beacon_material_1, associated_data, first_sequence(), assigned_key_id, beacon_record_secret) in\n    let beacon_frame = seal_frame(",
			"symbolic Beacon-to-Server seal wiring",
		),
		(
			"endpoint_symbolic_server_seal_count_increases",
			"let Server(",
			"let initial_frame = seal_frame(",
			"let endpoint_extra_initial_frame = seal_frame(server_material_1, associated_data, first_sequence(), SERVER_KEY_ID, registration_payload(binding, initial_secret)) in\n      let initial_frame = seal_frame(",
			"symbolic Server-to-Beacon seal wiring changed",
		),
		(
			"endpoint_symbolic_server_open_count_increases",
			"let Server(",
			"let beacon_plaintext = open_frame(",
			"let endpoint_extra_beacon_plaintext = open_frame(beacon_material_1, associated_data, first_sequence(), assigned_key_id, beacon_frame) in\n      let beacon_plaintext = open_frame(",
			"symbolic Server Beacon-frame open wiring",
		),
		(
			"endpoint_symbolic_malicious_initial_seal_count_increases",
			"let MaliciousServer(",
			"let initial_frame = seal_frame(",
			"let endpoint_extra_malicious_frame = seal_frame(server_material_1, associated_data, first_sequence(), SERVER_KEY_ID, registration_payload(binding, MALICIOUS_TASK_SECRET)) in\n  let initial_frame = seal_frame(",
			"symbolic malicious-registration initial-frame wiring",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.environment, scope, marker, replacement);
		});
		mutation_count += 1;
	}

	for (family, scope, event, calls, direction, sender, receiver, diagnostic) in [
		(
			"honest_beacon_receive",
			"let HonestBeacon(",
			"MessageReceived",
			4usize,
			"server_to_beacon()",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"symbolic HonestBeacon received-event fixture",
		),
		(
			"honest_beacon_send",
			"let HonestBeacon(",
			"MessageSent",
			1usize,
			"beacon_to_server()",
			"assigned_key_id",
			"SERVER_KEY_ID",
			"symbolic HonestBeacon sent-event fixture",
		),
		(
			"server_send",
			"let Server(",
			"MessageSent",
			4usize,
			"server_to_beacon()",
			"SERVER_KEY_ID",
			"assigned_key_id",
			"symbolic Server sent-event fixture",
		),
		(
			"server_receive",
			"let Server(",
			"MessageReceived",
			1usize,
			"beacon_to_server()",
			"assigned_key_id",
			"SERVER_KEY_ID",
			"symbolic Server received-event fixture",
		),
	] {
		for call_index in 0..calls {
			let wrong_direction = if direction == "server_to_beacon()" {
				"beacon_to_server()"
			} else {
				"server_to_beacon()"
			};
			let wrong_sender = if sender == "SERVER_KEY_ID" {
				"assigned_key_id"
			} else {
				"SERVER_KEY_ID"
			};
			let wrong_receiver = if receiver == "SERVER_KEY_ID" {
				"assigned_key_id"
			} else {
				"SERVER_KEY_ID"
			};
			for (argument_index, field, wrong_value) in [
				(0usize, "session", "server_identity"),
				(1usize, "direction", wrong_direction),
				(
					2usize,
					"sequence",
					"next_sequence(next_sequence(next_sequence(next_sequence(first_sequence()))))",
				),
				(3usize, "sender", wrong_sender),
				(4usize, "receiver", wrong_receiver),
				(5usize, "plaintext", "server_identity"),
			] {
				assert_rejected(
					&format!("endpoint_symbolic_{family}_event_{field}_{call_index}"),
					diagnostic,
					move |snapshot| {
						replace_nth_call_argument_after(
							&mut snapshot.environment,
							scope,
							event,
							call_index,
							argument_index,
							wrong_value,
						);
					},
				);
				mutation_count += 1;
			}
		}
	}

	for (name, scope, marker, replacement, diagnostic) in [
		(
			"endpoint_symbolic_honest_received_event_count_increases",
			"let HonestBeacon(",
			"event MessageReceived(",
			"event MessageReceived(session, server_to_beacon(), first_sequence(), SERVER_KEY_ID, assigned_key_id, initial_plaintext);\n    event MessageReceived(",
			"symbolic HonestBeacon received-event fixture",
		),
		(
			"endpoint_symbolic_honest_sent_event_count_increases",
			"let HonestBeacon(",
			"event MessageSent(",
			"event MessageSent(session, beacon_to_server(), first_sequence(), assigned_key_id, SERVER_KEY_ID, beacon_record_secret);\n    event MessageSent(",
			"symbolic HonestBeacon sent-event fixture",
		),
		(
			"endpoint_symbolic_server_sent_event_count_increases",
			"let Server(",
			"event MessageSent(",
			"event MessageSent(session, server_to_beacon(), first_sequence(), SERVER_KEY_ID, assigned_key_id, initial_secret);\n      event MessageSent(",
			"symbolic Server sent-event fixture",
		),
		(
			"endpoint_symbolic_server_received_event_count_increases",
			"let Server(",
			"event MessageReceived(",
			"event MessageReceived(session, beacon_to_server(), first_sequence(), assigned_key_id, SERVER_KEY_ID, beacon_plaintext);\n      event MessageReceived(",
			"symbolic Server received-event fixture",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.environment, scope, marker, replacement);
		});
		mutation_count += 1;
	}

	for (name, scope, marker, replacement, diagnostic) in [
		(
			"endpoint_symbolic_honest_received_event_arity_increases",
			"let HonestBeacon(",
			"assigned_key_id,\n      initial_plaintext\n    );",
			"assigned_key_id,\n      initial_plaintext,\n      server_identity\n    );",
			"symbolic HonestBeacon received-event fixture",
		),
		(
			"endpoint_symbolic_honest_sent_event_arity_increases",
			"let HonestBeacon(",
			"SERVER_KEY_ID,\n      beacon_record_secret\n    );",
			"SERVER_KEY_ID,\n      beacon_record_secret,\n      server_identity\n    );",
			"symbolic HonestBeacon sent-event fixture",
		),
		(
			"endpoint_symbolic_server_sent_event_arity_increases",
			"let Server(",
			"assigned_key_id,\n        initial_secret\n      );",
			"assigned_key_id,\n        initial_secret,\n        server_identity\n      );",
			"symbolic Server sent-event fixture",
		),
		(
			"endpoint_symbolic_server_received_event_arity_increases",
			"let Server(",
			"SERVER_KEY_ID,\n        beacon_plaintext\n      );",
			"SERVER_KEY_ID,\n        beacon_plaintext,\n        server_identity\n      );",
			"symbolic Server received-event fixture",
		),
	] {
		assert_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.environment, scope, marker, replacement);
		});
		mutation_count += 1;
	}

	for (name, scope) in [
		(
			"endpoint_symbolic_honest_ad_reverses_identities",
			"let HonestBeacon(",
		),
		(
			"endpoint_symbolic_server_ad_reverses_identities",
			"let Server(",
		),
		(
			"endpoint_symbolic_malicious_server_ad_reverses_identities",
			"let MaliciousServer(",
		),
	] {
		assert_rejected(
			name,
			"associated-data identity order changed",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					scope,
					"beaconcrypt_core__pqxdh__build_associated_data",
					0,
					0,
					"beacon_identity",
				);
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					scope,
					"beaconcrypt_core__pqxdh__build_associated_data",
					0,
					1,
					"server_identity",
				);
			},
		);
		mutation_count += 1;
	}

	assert_eq!(mutation_count, ENDPOINT_FRAME_CONTEXT_MUTATION_COUNT);
}

const RATCHET_EFFECT_DRIVER_MUTATION_COUNT: usize = 154;

#[test]
fn ratchet_effect_driver_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	let driver_facts = parse_facts(INTERFACE)
		.unwrap()
		.into_iter()
		.filter(|fact| fact.starts_with("ratchet.driver."))
		.collect::<Vec<_>>();
	assert_eq!(driver_facts.len(), 38);
	for fact in driver_facts {
		let (key, _) = fact.split_once('=').unwrap();
		assert_rejected(&format!("ratchet_driver_fact_{key}"), key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, "mutated");
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"ratchet_driver_slot_take_duplicates_take",
			"fn take(&mut self)",
			"self.kernel\n\t\t\t.take()",
			"self.kernel.take();\n\t\tself.kernel\n\t\t\t.take()",
			"ratchet driver affine slot take",
		),
		(
			"ratchet_driver_slot_put_omits_empty_assertion",
			"fn put(&mut self",
			"assert!(\n\t\t\tself.kernel.is_none(),\n\t\t\t\"a completed ratchet effect must return to an empty kernel slot\"\n\t\t);",
			"if self.kernel.is_some() {\n\t\t\tpanic!(\"a completed ratchet effect must return to an empty kernel slot\");\n\t\t}",
			"ratchet driver returned-kernel slot put",
		),
		(
			"ratchet_driver_slot_put_drops_returned_kernel",
			"fn put(&mut self",
			"self.kernel = Some(kernel);",
			"drop(kernel);",
			"ratchet driver returned-kernel slot put",
		),
		(
			"ratchet_driver_kdf_uses_fixed_request",
			"pub(crate) fn ratchet_hkdf",
			"symmetric_ratchet_hkdf(request)",
			"symmetric_ratchet_hkdf(&verified_ratchet::SymmetricRatchetKdfRequest::new([0; KDF_STATE_SIZE]))",
			"ratchet driver typed KDF reply",
		),
		(
			"ratchet_driver_kdf_returns_untyped_bytes",
			"pub(crate) fn ratchet_hkdf",
			"verified_ratchet::RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))",
			"symmetric_ratchet_hkdf(request)",
			"ratchet driver typed KDF reply",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.adapter_ratchet, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"ratchet_driver_send_context_swaps_target_and_sender",
			"let context = SealFrameContext {\n\t\tbytes,\n\t\ttarget_kid,\n\t\tsender_kid,\n\t\tassociated_data,\n\t};",
			"let context = SealFrameContext {\n\t\tbytes,\n\t\ttarget_kid: sender_kid,\n\t\tsender_kid: target_kid,\n\t\tassociated_data,\n\t};",
			"ratchet send exact frame context",
		),
		(
			"ratchet_driver_send_context_replaces_plaintext",
			"let context = SealFrameContext {\n\t\tbytes,\n\t\ttarget_kid,\n\t\tsender_kid,\n\t\tassociated_data,\n\t};",
			"let context = SealFrameContext {\n\t\tbytes: &[],\n\t\ttarget_kid,\n\t\tsender_kid,\n\t\tassociated_data,\n\t};",
			"ratchet send exact frame context",
		),
		(
			"ratchet_driver_send_context_replaces_associated_data",
			"let context = SealFrameContext {\n\t\tbytes,\n\t\ttarget_kid,\n\t\tsender_kid,\n\t\tassociated_data,\n\t};",
			"let context = SealFrameContext {\n\t\tbytes,\n\t\ttarget_kid,\n\t\tsender_kid,\n\t\tassociated_data: &[0; AD_SIZE],\n\t};",
			"ratchet send exact frame context",
		),
		(
			"ratchet_driver_send_duplicates_kernel_take",
			"let kernel = ratchet.refined.take();",
			"let kernel = ratchet.refined.take();\n\tratchet.refined.put(kernel);\n\tlet kernel = ratchet.refined.take();",
			"ratchet send affine kernel take",
		),
		(
			"ratchet_driver_send_omits_begin",
			"verified_ratchet::begin_send(kernel, context)",
			"panic!(\"begin send omitted\")",
			"ratchet send begin effect",
		),
		(
			"ratchet_driver_send_begins_with_rebuilt_context",
			"verified_ratchet::begin_send(kernel, context)",
			"verified_ratchet::begin_send(kernel, SealFrameContext { bytes, target_kid: sender_kid, sender_kid: target_kid, associated_data })",
			"ratchet send begin effect",
		),
		(
			"ratchet_driver_send_exhaustion_drops_kernel",
			"ratchet.refined.put(kernel);\n\t\t\treturn None;",
			"drop(kernel);\n\t\t\treturn None;",
			"ratchet send exhausted and KDF branches",
		),
		(
			"ratchet_driver_send_exhaustion_puts_after_return",
			"ratchet.refined.put(kernel);\n\t\t\treturn None;",
			"return None;\n\t\t\tratchet.refined.put(kernel);",
			"ratchet send exhausted and KDF branches",
		),
		(
			"ratchet_driver_send_uses_fixed_request",
			"ratchet_hkdf(pending.request())",
			"ratchet_hkdf(&verified_ratchet::SymmetricRatchetKdfRequest::new([0; KDF_STATE_SIZE]))",
			"ratchet send exact pending request interpretation",
		),
		(
			"ratchet_driver_send_omits_request_interpretation",
			"let response = ratchet_hkdf(pending.request());",
			"let response = verified_ratchet::RatchetKdfResponse::from_bytes([0; verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]);",
			"ratchet send exact pending request interpretation",
		),
		(
			"ratchet_driver_send_resumes_with_wrong_response",
			"pending.resume(response)",
			"pending.resume(verified_ratchet::RatchetKdfResponse::from_bytes([0; verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]))",
			"ratchet send same-pending resume",
		),
		(
			"ratchet_driver_send_resumes_different_pending",
			"pending.resume(response)",
			"unsafe { std::hint::unreachable_unchecked() }.resume(response)",
			"ratchet send same-pending resume",
		),
		(
			"ratchet_driver_send_omits_pending_resume",
			"let seal = pending.resume(response);",
			"let seal = panic!(\"pending resume omitted\");",
			"ratchet send same-pending resume",
		),
		(
			"ratchet_driver_send_seals_with_wrong_material",
			"seal_frame(seal.material(), seal.sequence(), seal.context())",
			"seal_frame(panic!(), seal.sequence(), seal.context())",
			"ratchet send seal capability handoff",
		),
		(
			"ratchet_driver_send_seals_with_wrong_sequence",
			"seal_frame(seal.material(), seal.sequence(), seal.context())",
			"seal_frame(seal.material(), seal.sequence().wrapping_add(1), seal.context())",
			"ratchet send seal capability handoff",
		),
		(
			"ratchet_driver_send_seals_with_rebuilt_context",
			"seal_frame(seal.material(), seal.sequence(), seal.context())",
			"seal_frame(seal.material(), seal.sequence(), &SealFrameContext { bytes, target_kid: sender_kid, sender_kid: target_kid, associated_data })",
			"ratchet send seal capability handoff",
		),
		(
			"ratchet_driver_send_omits_seal",
			"let sealed = seal_frame(seal.material(), seal.sequence(), seal.context());",
			"let sealed: Option<Encrypted> = None;",
			"ratchet send seal capability handoff",
		),
		(
			"ratchet_driver_send_finishes_with_none",
			"seal.finish(sealed)",
			"seal.finish(None::<Encrypted>)",
			"ratchet send capability finish",
		),
		(
			"ratchet_driver_send_omits_finish",
			"let (kernel, sealed) = seal.finish(sealed);",
			"let (kernel, sealed) = panic!(\"seal finish omitted\");",
			"ratchet send capability finish",
		),
		(
			"ratchet_driver_send_drops_finished_kernel",
			"ratchet.refined.put(kernel);\n\tsealed",
			"drop(kernel);\n\tsealed",
			"ratchet send returned-kernel puts",
		),
		(
			"ratchet_driver_send_returns_before_put",
			"ratchet.refined.put(kernel);\n\tsealed",
			"return sealed;\n\tratchet.refined.put(kernel);",
			"ratchet send returned-kernel put before result",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn encrypt_message_with_ratchet",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_ratchet_driver_rejected(
		"ratchet_driver_send_moves_empty_gate_after_take",
		"ratchet send empty-input precheck",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn encrypt_message_with_ratchet",
				"if bytes.is_empty() {\n\t\treturn None;\n\t}\n",
				"",
			);
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn encrypt_message_with_ratchet",
				"let kernel = ratchet.refined.take();",
				"let kernel = ratchet.refined.take();\n\tif bytes.is_empty() {\n\t\tratchet.refined.put(kernel);\n\t\treturn None;\n\t}",
			);
		},
	);
	mutation_count += 1;

	assert_ratchet_driver_rejected(
		"ratchet_driver_send_invokes_cancel",
		"ratchet send production cancellation",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn encrypt_message_with_ratchet",
				"let response = ratchet_hkdf(pending.request());",
				"pending.cancel();\n\tlet response = ratchet_hkdf(pending.request());",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to) in [
		(
			"ratchet_driver_core_send_finish_discards_interpreter_result",
			"(self.advanced, sealed)",
			"(self.advanced, None)",
		),
		(
			"ratchet_driver_core_send_finish_discards_advanced_kernel",
			"(self.advanced, sealed)",
			"(panic!(), sealed)",
		),
	] {
		assert_ratchet_driver_rejected(
			name,
			"ratchet send finish preserves interpreter result on advanced kernel",
			move |snapshot| {
				replace_once_after(
					&mut snapshot.core_ratchet_concrete,
					"impl<Context> SendSeal<Context>",
					from,
					to,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"ratchet_driver_receive_context_uses_expected_sender",
			"sender_kid: kid,",
			"sender_kid: expected_sender_kid,",
			"ratchet receive prechecks and effect start order",
		),
		(
			"ratchet_driver_receive_context_replaces_ciphertext",
			"let context = OpenFrameContext {\n\t\tciphertext,\n\t\tassociated_data,\n\t\tsender_kid: kid,\n\t};",
			"let context = OpenFrameContext {\n\t\tciphertext: &[],\n\t\tassociated_data,\n\t\tsender_kid: kid,\n\t};",
			"ratchet receive prechecks and effect start order",
		),
		(
			"ratchet_driver_receive_context_replaces_associated_data",
			"let context = OpenFrameContext {\n\t\tciphertext,\n\t\tassociated_data,\n\t\tsender_kid: kid,\n\t};",
			"let context = OpenFrameContext {\n\t\tciphertext,\n\t\tassociated_data: &[0; AD_SIZE],\n\t\tsender_kid: kid,\n\t};",
			"ratchet receive prechecks and effect start order",
		),
		(
			"ratchet_driver_receive_duplicates_kernel_take",
			"let kernel = ratchet.refined.take();",
			"let kernel = ratchet.refined.take();\n\tratchet.refined.put(kernel);\n\tlet kernel = ratchet.refined.take();",
			"ratchet receive affine kernel take",
		),
		(
			"ratchet_driver_receive_begins_with_wrong_sequence",
			"verified_ratchet::begin_receive(kernel, key_seq, context)",
			"verified_ratchet::begin_receive(kernel, key_seq.wrapping_add(1), context)",
			"ratchet receive prechecks and effect start order",
		),
		(
			"ratchet_driver_receive_begins_with_rebuilt_context",
			"verified_ratchet::begin_receive(kernel, key_seq, context)",
			"verified_ratchet::begin_receive(kernel, key_seq, OpenFrameContext { ciphertext, associated_data, sender_kid: expected_sender_kid })",
			"ratchet receive prechecks and effect start order",
		),
		(
			"ratchet_driver_receive_rejected_drops_kernel",
			"ratchet.refined.put(kernel);\n\t\t\t\treturn None;",
			"drop(kernel);\n\t\t\t\treturn None;",
			"ratchet receive rejected branch",
		),
		(
			"ratchet_driver_receive_rejected_puts_after_return",
			"ratchet.refined.put(kernel);\n\t\t\t\treturn None;",
			"return None;\n\t\t\t\tratchet.refined.put(kernel);",
			"ratchet receive rejected branch",
		),
		(
			"ratchet_driver_receive_fixes_loop_iteration_count",
			"let plaintext = loop {\n\t\teffect = match effect {",
			"let mut remaining_iterations = 1usize;\n\tlet plaintext = loop {\n\t\tif remaining_iterations == 0 { return None; }\n\t\tremaining_iterations -= 1;\n\t\teffect = match effect {",
			"ratchet receive effect loop without fixed iteration count",
		),
		(
			"ratchet_driver_receive_uses_fixed_kdf_request",
			"ratchet_hkdf(pending.request())",
			"ratchet_hkdf(&verified_ratchet::SymmetricRatchetKdfRequest::new([0; KDF_STATE_SIZE]))",
			"ratchet receive exact pending request interpretation",
		),
		(
			"ratchet_driver_receive_omits_kdf_request",
			"let response = ratchet_hkdf(pending.request());",
			"let response = verified_ratchet::RatchetKdfResponse::from_bytes([0; verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]);",
			"ratchet receive exact pending request interpretation",
		),
		(
			"ratchet_driver_receive_resumes_with_wrong_response",
			"pending.resume(response)",
			"pending.resume(verified_ratchet::RatchetKdfResponse::from_bytes([0; verified_ratchet::RATCHET_KDF_OUTPUT_SIZE]))",
			"ratchet receive same-pending resume",
		),
		(
			"ratchet_driver_receive_resumes_different_pending",
			"pending.resume(response)",
			"unsafe { std::hint::unreachable_unchecked() }.resume(response)",
			"ratchet receive same-pending resume",
		),
		(
			"ratchet_driver_receive_omits_pending_resume",
			"pending.resume(response)",
			"panic!(\"pending resume omitted\")",
			"ratchet receive same-pending resume",
		),
		(
			"ratchet_driver_receive_kdf_publishes_slot",
			"let response = ratchet_hkdf(pending.request());",
			"ratchet.refined.put(panic!(\"premature publication\"));\n\t\t\t\tlet response = ratchet_hkdf(pending.request());",
			"ratchet receive KDF-arm live publication",
		),
		(
			"ratchet_driver_receive_no_material_omits_material_gate",
			"let Some(material) = open.material() else {",
			"let material = open.material().unwrap_or_else(|| panic!(\"material missing\"));\n\t\t\t\tif false {",
			"ratchet receive no-material rejection",
		),
		(
			"ratchet_driver_receive_no_material_omits_reject",
			"let (kernel, _) = open.reject();",
			"let kernel = panic!(\"open reject omitted\");",
			"ratchet receive no-material rejection",
		),
		(
			"ratchet_driver_receive_no_material_drops_kernel",
			"ratchet.refined.put(kernel);\n\t\t\t\t\treturn None;",
			"drop(kernel);\n\t\t\t\t\treturn None;",
			"ratchet receive no-material rejection",
		),
		(
			"ratchet_driver_receive_no_material_puts_after_return",
			"ratchet.refined.put(kernel);\n\t\t\t\t\treturn None;",
			"return None;\n\t\t\t\t\tratchet.refined.put(kernel);",
			"ratchet receive no-material rejection",
		),
		(
			"ratchet_driver_receive_opens_with_wrong_material",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(panic!(), open.sequence(), open.context())",
			"ratchet receive open capability handoff",
		),
		(
			"ratchet_driver_receive_opens_with_wrong_sequence",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, open.sequence().wrapping_add(1), open.context())",
			"ratchet receive open capability handoff",
		),
		(
			"ratchet_driver_receive_opens_with_rebuilt_context",
			"open_frame(material, open.sequence(), open.context())",
			"open_frame(material, open.sequence(), &OpenFrameContext { ciphertext, associated_data, sender_kid: expected_sender_kid })",
			"ratchet receive open capability handoff",
		),
		(
			"ratchet_driver_receive_omits_open",
			"let opened = open_frame(material, open.sequence(), open.context());",
			"let opened: Option<Vec<u8>> = None;",
			"ratchet receive open capability handoff",
		),
		(
			"ratchet_driver_receive_finishes_with_none",
			"open.finish(opened)",
			"open.finish(None::<Vec<u8>>)",
			"ratchet receive capability finish",
		),
		(
			"ratchet_driver_receive_omits_finish",
			"let (kernel, opened) = open.finish(opened);",
			"let (kernel, opened) = panic!(\"open finish omitted\");",
			"ratchet receive capability finish",
		),
		(
			"ratchet_driver_receive_drops_finished_kernel",
			"ratchet.refined.put(kernel);\n\t\t\t\tbreak opened?;",
			"drop(kernel);\n\t\t\t\tbreak opened?;",
			"ratchet receive returned-kernel puts",
		),
		(
			"ratchet_driver_receive_questions_result_before_put",
			"let (kernel, opened) = open.finish(opened);\n\t\t\t\tratchet.refined.put(kernel);\n\t\t\t\tbreak opened?;",
			"let (kernel, opened) = open.finish(opened);\n\t\t\t\tlet opened = opened?;\n\t\t\t\tratchet.refined.put(kernel);\n\t\t\t\tbreak opened;",
			"ratchet receive open and terminal publication order",
		),
		(
			"ratchet_driver_receive_returns_expected_sender_metadata",
			"key_id: kid,",
			"key_id: expected_sender_kid,",
			"ratchet receive parsed result metadata",
		),
		(
			"ratchet_driver_receive_returns_wrong_sequence_metadata",
			"seq: key_seq,",
			"seq: key_seq.wrapping_add(1),",
			"ratchet receive parsed result metadata",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	assert_ratchet_driver_rejected(
		"ratchet_driver_receive_invokes_cancel",
		"ratchet receive production cancellation",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				"let response = ratchet_hkdf(pending.request());",
				"pending.cancel();\n\t\t\t\tlet response = ratchet_hkdf(pending.request());",
			);
		},
	);
	mutation_count += 1;
	for (name, gate) in [
		(
			"ratchet_driver_receive_moves_sender_gate_after_take",
			"if kid != expected_sender_kid {\n\t\treturn None;\n\t}\n",
		),
		(
			"ratchet_driver_receive_moves_length_gate_after_take",
			"if ct_len <= MESSAGE_OVERHEAD {\n\t\treturn None;\n\t}\n",
		),
	] {
		assert_ratchet_driver_rejected(
			name,
			"ratchet receive prechecks and effect start order",
			move |snapshot| {
				replace_once_after(
					&mut snapshot.adapter_ratchet,
					"pub(crate) fn decrypt_message_with_ratchet",
					gate,
					"",
				);
				replace_once_after(
					&mut snapshot.adapter_ratchet,
					"pub(crate) fn decrypt_message_with_ratchet",
					"let kernel = ratchet.refined.take();",
					&format!("let kernel = ratchet.refined.take();\n\t{gate}"),
				);
			},
		);
		mutation_count += 1;
	}
	assert_ratchet_driver_rejected(
		"ratchet_driver_receive_moves_empty_gate_after_take",
		"ratchet receive prechecks and effect start order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				"if data.is_empty() {\n\t\treturn None;\n\t}\n",
				"",
			);
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				"let kernel = ratchet.refined.take();",
				"let kernel = ratchet.refined.take();\n\tif data.is_empty() {\n\t\tratchet.refined.put(kernel);\n\t\treturn None;\n\t}",
			);
		},
	);
	mutation_count += 1;
	assert_ratchet_driver_rejected(
		"ratchet_driver_receive_takes_kernel_before_typed_parse",
		"ratchet receive prechecks and effect start order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				"let kernel = ratchet.refined.take();",
				"",
			);
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn decrypt_message_with_ratchet",
				"if data.is_empty() {\n\t\treturn None;\n\t}",
				"if data.is_empty() {\n\t\treturn None;\n\t}\n\tlet kernel = ratchet.refined.take();",
			);
		},
	);
	mutation_count += 1;

	for (name, marker, from, to, diagnostic) in [
		(
			"ratchet_driver_core_phase_renames_send_start",
			"pub enum SendStart<Context>",
			"pub enum SendStart<Context>",
			"pub enum RenamedSendStart<Context>",
			"ratchet core affine phase API",
		),
		(
			"ratchet_driver_core_phase_renames_send_kdf",
			"pub struct SendKdf<Context>",
			"pub struct SendKdf<Context>",
			"pub struct RenamedSendKdf<Context>",
			"ratchet core affine phase API",
		),
		(
			"ratchet_driver_core_phase_renames_send_seal",
			"pub struct SendSeal<Context>",
			"pub struct SendSeal<Context>",
			"pub struct RenamedSendSeal<Context>",
			"ratchet core affine phase API",
		),
		(
			"ratchet_driver_core_phase_renames_receive_effect",
			"pub enum ReceiveEffect<Context>",
			"pub enum ReceiveEffect<Context>",
			"pub enum RenamedReceiveEffect<Context>",
			"ratchet core affine phase API",
		),
		(
			"ratchet_driver_core_phase_renames_receive_kdf",
			"pub struct ReceiveKdf<Context>",
			"pub struct ReceiveKdf<Context>",
			"pub struct RenamedReceiveKdf<Context>",
			"ratchet core affine phase API",
		),
		(
			"ratchet_driver_core_phase_renames_receive_open",
			"pub struct ReceiveOpen<Context>",
			"pub struct ReceiveOpen<Context>",
			"pub struct RenamedReceiveOpen<Context>",
			"ratchet core affine phase API",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_concrete, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"ratchet_driver_core_finish_none_drops_entry",
			"impl<Context> ReceiveOpen<Context>",
			"None => return (self.entry, None)",
			"None => return (panic!(\"entry dropped\"), None)",
			"ratchet receive finish failure restores entry",
		),
		(
			"ratchet_driver_core_finish_cached_publication_omitted",
			"impl<Context> ReceiveOpen<Context>",
			"publish_cached_receive(&mut entry.refined, prepared);",
			"drop(prepared);",
			"ratchet core cached receive publication branch",
		),
		(
			"ratchet_driver_core_finish_future_publication_omitted",
			"impl<Context> ReceiveOpen<Context>",
			"publish_future_receive(&mut entry.refined, pending);",
			"drop(pending);",
			"ratchet core future receive publication branch",
		),
		(
			"ratchet_driver_core_finish_cached_uses_future_publisher",
			"impl<Context> ReceiveOpen<Context>",
			"publish_cached_receive(&mut entry.refined, prepared);",
			"publish_future_receive(&mut entry.refined, panic!(\"wrong prepared type\"));",
			"ratchet core cached receive publication branch",
		),
		(
			"ratchet_driver_core_finish_future_uses_cached_publisher",
			"impl<Context> ReceiveOpen<Context>",
			"publish_future_receive(&mut entry.refined, pending);",
			"publish_cached_receive(&mut entry.refined, panic!(\"wrong prepared type\"));",
			"ratchet core future receive publication branch",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_concrete, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, insertion, diagnostic) in [
		(
			"ratchet_driver_core_begin_receive_mutates_live_control",
			"kernel.refined.control = kernel.refined.control;\n\t",
			"ratchet core begin_receive live publication",
		),
		(
			"ratchet_driver_core_begin_receive_mutates_live_send_chain",
			"kernel.refined.send_chain = kernel.refined.send_chain;\n\t",
			"ratchet core begin_receive live publication",
		),
		(
			"ratchet_driver_core_begin_receive_mutates_live_receive_chain",
			"kernel.refined.receive_chain = kernel.refined.receive_chain;\n\t",
			"ratchet core begin_receive live publication",
		),
		(
			"ratchet_driver_core_begin_receive_mutates_live_receive_slots",
			"kernel.refined.receive_slots = kernel.refined.receive_slots;\n\t",
			"ratchet core begin_receive live publication",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.core_ratchet_concrete,
				"pub fn begin_receive<Context>",
				"let plan = plan_receive_until",
				&format!("{insertion}let plan = plan_receive_until"),
			);
		});
		mutation_count += 1;
	}

	for (name, insertion, diagnostic) in [
		(
			"ratchet_driver_core_receive_kdf_publishes_cached_early",
			"let _ = publish_cached_receive::<RatchetChain, RatchetChain, RatchetMaterial>;\n\t\t",
			"ratchet core receive KDF cached publication",
		),
		(
			"ratchet_driver_core_receive_kdf_publishes_future_early",
			"let _ = publish_future_receive::<RatchetChain, RatchetChain, RatchetMaterial>;\n\t\t",
			"ratchet core receive KDF future publication",
		),
	] {
		assert_ratchet_driver_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.core_ratchet_concrete,
				"impl<Context> ReceiveKdf<Context>",
				"if self.remaining == 0 {",
				&format!("{insertion}if self.remaining == 0 {{"),
			);
		});
		mutation_count += 1;
	}

	let structural_anchors = [
		"theorem ratchet.concrete.begin_send_nonexhausted_exact",
		"theorem ratchet.concrete.begin_send_exhausted_restores_entry",
		"theorem ratchet.concrete.SendKdf.request_exact",
		"theorem ratchet.concrete.SendKdf.resume_exact",
		"theorem ratchet.concrete.SendSeal.finish_returns_interpreter_result",
		"theorem ratchet.concrete.begin_receive_rejected_plan_restores_entry",
		"theorem ratchet.concrete.begin_receive_cached_exact",
		"theorem ratchet.concrete.begin_receive_future_request_exact",
		"theorem ratchet.concrete.ReceiveKdf.request_exact",
		"theorem ratchet.concrete.ReceiveOpen.reject_exact",
		"theorem ratchet.concrete.ReceiveOpen.context_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_sequence_exact",
		"theorem ratchet.concrete.ReceiveOpen.future_material_exact",
		"theorem ratchet.concrete.ReceiveOpen.finish_failure_restores_entry",
		"theorem ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext",
		"theorem ratchet.concrete.ReceiveOpen.finish_cached_success_publishes_same_plaintext",
	];
	for (index, anchor) in structural_anchors.into_iter().enumerate() {
		assert_ratchet_driver_rejected(
			&format!("ratchet_driver_lean_structural_anchor_{index}_renamed"),
			"ratchet checked structural Lean anchor",
			move |snapshot| {
				replace_once(
					&mut snapshot.lean_ratchet_effect,
					anchor,
					&anchor.replace("theorem ", "theorem renamed_"),
				);
			},
		);
		mutation_count += 1;
	}
	assert_ratchet_driver_rejected(
		"ratchet_driver_lean_failure_trace_anchor_renamed",
		"ratchet checked structural failure-trace anchor",
		|snapshot| {
			replace_once(
				&mut snapshot.lean_ratchet_effect_refinement,
				"theorem ReceiveFailureTrace.result_eq_entry",
				"theorem ReceiveFailureTrace.renamed_result_eq_entry",
			);
		},
	);
	mutation_count += 1;

	let refinement_anchors = [
		"def ResponseRefines",
		"theorem begin_send_refines",
		"theorem SendKdf.resume_refines",
		"theorem SendSeal.finish_refines_ideal_send",
		"theorem ReceiveOpen.failure_preserves_refinement",
		"theorem ReceiveFailureTrace.preserves_refinement",
		"def OpenReplyRefines",
		"theorem begin_receive_cached_refines",
		"theorem CachedOpenRefines.finish_success_matches_ideal",
		"theorem CachedOpenRefines.finish_success_refines_of_publication",
	];
	for (index, anchor) in refinement_anchors.into_iter().enumerate() {
		assert_ratchet_driver_rejected(
			&format!("ratchet_driver_lean_conditional_anchor_{index}_renamed"),
			"ratchet conditional Lean refinement anchor",
			move |snapshot| {
				let renamed = if anchor.starts_with("def ") {
					anchor.replacen("def ", "def renamed_", 1)
				} else {
					anchor.replacen("theorem ", "theorem renamed_", 1)
				};
				replace_once(
					&mut snapshot.lean_ratchet_effect_refinement,
					anchor,
					&renamed,
				);
			},
		);
		mutation_count += 1;
	}

	assert_ratchet_driver_rejected(
		"ratchet_driver_proverif_renames_atomic_seal",
		"ratchet ProVerif atomic seal abstraction",
		|snapshot| {
			replace_once(
				&mut snapshot.crypto,
				"letfun seal_frame(",
				"letfun renamed_seal_frame(",
			);
		},
	);
	mutation_count += 1;
	assert_ratchet_driver_rejected(
		"ratchet_driver_proverif_renames_ideal_open",
		"ratchet ProVerif ideal exact open abstraction",
		|snapshot| {
			replace_once_after(
				&mut snapshot.crypto,
				"reduc forall key: bitstring",
				"  open_frame(",
				"  renamed_open_frame(",
			);
		},
	);
	mutation_count += 1;
	for concrete_step in [
		"RatchetKernelSlot",
		"begin_send",
		"begin_receive",
		"ratchet_hkdf",
		"SendKdfRequested",
		"ReceiveKdfRequested",
	] {
		assert_ratchet_driver_rejected(
			&format!("ratchet_driver_proverif_exposes_{concrete_step}"),
			"concrete ratchet driver step in atomic ProVerif model",
			move |snapshot| {
				snapshot
					.crypto
					.push_str(&format!("\nfun {concrete_step}(bitstring): bitstring.\n"));
			},
		);
		mutation_count += 1;
	}

	assert_eq!(mutation_count, RATCHET_EFFECT_DRIVER_MUTATION_COUNT);
}

const FINITE_RECEIVE_STATE_FIXTURE_MUTATION_COUNT: usize = 1_230;

#[test]
fn finite_receive_state_fixture_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	let fixture_facts = parse_facts(INTERFACE)
		.unwrap()
		.into_iter()
		.filter(|fact| fact.starts_with("ratchet.receive_fixture."))
		.collect::<Vec<_>>();
	assert_eq!(fixture_facts.len(), 46);
	for fact in fixture_facts {
		let (key, _) = fact.split_once('=').unwrap();
		assert_rejected(
			&format!("finite_receive_fixture_fact_{key}"),
			key,
			|snapshot| {
				mutate_fact(&mut snapshot.interface, key, "mutated");
			},
		);
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"finite_receive_core_changes_max_gap",
			"pub const RATCHET_MAX_GAP",
			"pub const RATCHET_MAX_GAP: u64 = 50;",
			"pub const RATCHET_MAX_GAP: u64 = 49;",
			"finite receive core maximum gap",
		),
		(
			"finite_receive_core_decouples_cache_capacity",
			"pub const RECEIVE_CACHE_CAPACITY",
			"pub const RECEIVE_CACHE_CAPACITY: usize = RATCHET_MAX_GAP as usize;",
			"pub const RECEIVE_CACHE_CAPACITY: usize = 49;",
			"finite receive core cache capacity",
		),
		(
			"finite_receive_core_plan_derives_from_zero",
			"pub(crate) fn plan_receive_until",
			"let derivations = target - state.receive_sequence;",
			"let derivations = target;",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_caches_target_step",
			"pub(crate) fn plan_receive_until",
			"let skipped = derivations - 1;",
			"let skipped = derivations;",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_ignores_existing_cache",
			"pub(crate) fn plan_receive_until",
			"let cached = state.receive_cache.len as u64;",
			"let cached = 0u64;",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_rejects_boundary_gap",
			"pub(crate) fn plan_receive_until",
			"skipped > RATCHET_MAX_GAP",
			"skipped >= RATCHET_MAX_GAP",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_rejects_full_exact_capacity",
			"pub(crate) fn plan_receive_until",
			"cached > RATCHET_MAX_GAP - skipped",
			"cached >= RATCHET_MAX_GAP - skipped",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_rejection_returns_target",
			"if skipped > RATCHET_MAX_GAP",
			"sequence: None,",
			"sequence: Some(target),",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_rejection_requests_work",
			"if skipped > RATCHET_MAX_GAP",
			"derivations: 0,",
			"derivations: 1,",
			"finite receive core admission plan",
		),
		(
			"finite_receive_core_plan_old_target_requests_work",
			"if target <= state.receive_sequence",
			"derivations: 0,",
			"derivations: 1,",
			"finite receive core admission plan",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_control, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"finite_receive_core_target_advances_two",
			"pub(crate) fn advance_receive_target",
			"let next = state.receive_sequence + 1;",
			"let next = state.receive_sequence + 2;",
			"finite receive target counter advance",
		),
		(
			"finite_receive_core_target_returns_entry_state",
			"pub(crate) fn advance_receive_target",
			"receive_sequence: next,",
			"receive_sequence: state.receive_sequence,",
			"finite receive target result",
		),
		(
			"finite_receive_core_target_allocates_cache_slot",
			"pub(crate) fn advance_receive_target",
			"let next = state.receive_sequence + 1;",
			"let _ = state.receive_cache.append(1);\n\t\tlet next = state.receive_sequence + 1;",
			"finite receive target cache allocation",
		),
		(
			"finite_receive_core_skipped_appends_wrong_sequence",
			"pub(crate) fn advance_receive(",
			"state.receive_cache.append(next)",
			"state.receive_cache.append(next + 1)",
			"finite receive skipped-key cache append",
		),
		(
			"finite_receive_core_skipped_drops_new_cache",
			"pub(crate) fn advance_receive(",
			"\t\t\t\treceive_cache,\n\t\t\t\t..state",
			"\t\t\t\treceive_cache: state.receive_cache,\n\t\t\t\t..state",
			"finite receive skipped-key control update",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_control, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"finite_receive_core_cached_failure_changes_state",
			"state,\n\t\t\tdisposition: ReceiveDisposition::Retained,",
			"state: RatchetState::default(),\n\t\t\tdisposition: ReceiveDisposition::Retained,",
			"finite receive cached authentication failure neutrality",
		),
		(
			"finite_receive_core_cached_removal_keeps_target",
			"entries[slot_index] = entries[last_slot as usize];",
			"entries[slot_index] = entries[slot_index];",
			"finite receive cached swap removal",
		),
		(
			"finite_receive_core_cached_removal_keeps_last_slot",
			"entries[last_slot as usize] = 0;",
			"entries[last_slot as usize] = entries[last_slot as usize];",
			"finite receive cached swap removal",
		),
		(
			"finite_receive_core_cached_removal_keeps_length",
			"len: last_slot,",
			"len,",
			"finite receive cached swap removal",
		),
		(
			"finite_receive_core_cached_removal_reports_wrong_target",
			"target_slot: slot,",
			"target_slot: last_slot,",
			"finite receive cached swap removal",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.core_ratchet_control,
				"pub(crate) fn finish_receive_with_removal",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"finite_receive_core_replay_looks_up_next_sequence",
			"pub fn begin_receive<Context>",
			"prepare_cached_receive(&kernel.refined, sequence)",
			"prepare_cached_receive(&kernel.refined, sequence + 1)",
			"finite receive replay and cached lookup branch",
		),
		(
			"finite_receive_core_future_counts_target_as_skipped",
			"pub fn begin_receive<Context>",
			"let skipped = plan.derivations - 1;",
			"let skipped = plan.derivations;",
			"finite receive future skipped count",
		),
		(
			"finite_receive_core_future_reuses_live_slots",
			"pub fn begin_receive<Context>",
			"staged_slots: empty_material_slots(),",
			"staged_slots: kernel.refined.receive_slots,",
			"finite receive private future staging start",
		),
		(
			"finite_receive_core_future_pending_uses_wrong_target_material",
			"impl<Context> ReceiveKdf<Context>",
			"target_material: stepped.material,",
			"target_material: panic!(\"wrong target material\"),",
			"finite receive separate future target",
		),
		(
			"finite_receive_core_future_stages_wrong_material",
			"impl<Context> ReceiveKdf<Context>",
			"self.staged_slots[slot_index] = Some(CachedReceiveKey {\n\t\t\tsequence,\n\t\t\tmaterial: stepped.material,",
			"self.staged_slots[slot_index] = Some(CachedReceiveKey {\n\t\t\tsequence,\n\t\t\tmaterial: panic!(\"wrong skipped material\"),",
			"finite receive staged skipped material",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_concrete, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"finite_receive_core_pending_allows_cached_target",
			"pub(super) fn pending_receive_is_valid",
			"if lookup_receive_key(pending.committed_control, requested).is_some() {\n\t\treturn false;\n\t}",
			"if false {\n\t\treturn false;\n\t}",
			"finite receive target absent from committed cache",
		),
		(
			"finite_receive_core_pending_counts_target_in_cache",
			"pub(super) fn pending_receive_is_valid",
			"pending.first_slot as usize + pending.skipped as usize",
			"pending.first_slot as usize + pending.skipped as usize + 1",
			"finite receive committed skipped-cache length",
		),
		(
			"finite_receive_core_pending_accepts_wrong_cache_length",
			"pub(super) fn pending_receive_is_valid",
			"pending.committed_control.receive_cache_len() as usize == committed_len",
			"pending.committed_control.receive_cache_len() as usize + 1 == committed_len",
			"finite receive committed cache length check",
		),
		(
			"finite_receive_core_cached_preflight_looks_up_wrong_sequence",
			"pub(super) fn prepare_cached_receive",
			"lookup_receive_key(state.control, sequence)",
			"lookup_receive_key(state.control, sequence + 1)",
			"finite receive cached preflight",
		),
		(
			"finite_receive_core_cached_preflight_uses_first_as_last",
			"pub(super) fn prepare_cached_receive",
			"let last_slot = len - 1;",
			"let last_slot = 0;",
			"finite receive cached preflight",
		),
		(
			"finite_receive_core_cached_preflight_marks_failure",
			"pub(super) fn prepare_cached_receive",
			"finish_receive_with_removal(state.control, sequence, target_slot, true)",
			"finish_receive_with_removal(state.control, sequence, target_slot, false)",
			"finite receive cached preflight",
		),
		(
			"finite_receive_core_cached_preflight_ignores_target_slot",
			"pub(super) fn prepare_cached_receive",
			"if !(removal.target_slot == target_slot) {\n\t\treturn None;\n\t}",
			"if false {\n\t\treturn None;\n\t}",
			"finite receive cached preflight",
		),
		(
			"finite_receive_core_cached_preflight_ignores_last_slot",
			"pub(super) fn prepare_cached_receive",
			"if !(removal.last_slot == last_slot) {\n\t\treturn None;\n\t}",
			"if false {\n\t\treturn None;\n\t}",
			"finite receive cached preflight",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet_refined, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, source, marker, from, to, diagnostic) in [
		(
			"finite_receive_core_finish_failure_drops_entry",
			"concrete",
			"impl<Context> ReceiveOpen<Context>",
			"None => return (self.entry, None)",
			"None => return (panic!(\"entry dropped\"), None)",
			"finite receive success-only publication",
		),
		(
			"finite_receive_core_finish_omits_cached_publication",
			"concrete",
			"impl<Context> ReceiveOpen<Context>",
			"publish_cached_receive(&mut entry.refined, prepared);",
			"drop(prepared);",
			"finite receive success-only publication",
		),
		(
			"finite_receive_core_finish_omits_future_publication",
			"concrete",
			"impl<Context> ReceiveOpen<Context>",
			"publish_future_receive(&mut entry.refined, pending);",
			"drop(pending);",
			"finite receive success-only publication",
		),
		(
			"finite_receive_core_cached_publication_keeps_last",
			"refined",
			"pub(super) fn publish_cached_receive",
			"let _ = state.receive_slots[last_index].take();",
			"let _ = state.receive_slots[last_index].as_ref();",
			"finite receive cached whole-entry publication",
		),
		(
			"finite_receive_core_cached_publication_copies_last",
			"refined",
			"pub(super) fn publish_cached_receive",
			"let moved = state.receive_slots[last_index].take();",
			"let moved = None;",
			"finite receive cached whole-entry publication",
		),
		(
			"finite_receive_core_cached_publication_omits_control",
			"refined",
			"pub(super) fn publish_cached_receive",
			"state.control = prepared.committed_control;",
			"drop(prepared.committed_control);",
			"finite receive cached whole-entry publication",
		),
		(
			"finite_receive_core_future_publication_omits_slots",
			"refined",
			"pub(super) fn publish_future_receive<",
			"publish_future_receive_slots(\n\t\tstate,\n\t\t&mut pending.staged_slots,\n\t\tpending.first_slot,\n\t\tpending.skipped,\n\t);",
			"drop(pending.staged_slots);",
			"finite receive future publication",
		),
		(
			"finite_receive_core_future_publication_omits_chain",
			"refined",
			"pub(super) fn publish_future_receive<",
			"state.receive_chain = pending.final_receive_chain;",
			"drop(pending.final_receive_chain);",
			"finite receive future publication",
		),
		(
			"finite_receive_core_future_publication_reorders_control",
			"refined",
			"pub(super) fn publish_future_receive<",
			"state.receive_chain = pending.final_receive_chain;\n\tstate.control = pending.committed_control;",
			"state.control = pending.committed_control;\n\tstate.receive_chain = pending.final_receive_chain;",
			"finite receive future publication",
		),
		(
			"finite_receive_core_future_publication_mentions_target",
			"refined",
			"pub(super) fn publish_future_receive<",
			"let first_index = pending.first_slot as usize;",
			"let _ = &pending.target_material;\n\tlet first_index = pending.first_slot as usize;",
			"finite receive target publication",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			let target = if source == "concrete" {
				&mut snapshot.core_ratchet_concrete
			} else {
				&mut snapshot.core_ratchet_refined
			};
			replace_once_after(target, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"finite_receive_proverif_renames_empty_cache",
			"fun receive_cache_empty(): receive_cache [data].",
			"fun renamed_receive_cache_empty(): receive_cache [data].",
			"finite receive ProVerif empty cache constructor",
		),
		(
			"finite_receive_proverif_renames_cache_entry",
			"fun receive_cache_entry(",
			"fun renamed_receive_cache_entry(",
			"finite receive ProVerif cache-entry constructor",
		),
		(
			"finite_receive_proverif_renames_state",
			"fun receive_state(",
			"fun renamed_receive_state(",
			"finite receive ProVerif state constructor",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once(&mut snapshot.environment, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to) in [
		(
			"finite_receive_proverif_omits_short_leg",
			"StateNeutralFutureReceive()\n    | StateNeutralCapacityReceive()",
			"StateNeutralCapacityReceive()",
		),
		(
			"finite_receive_proverif_omits_capacity_leg",
			"StateNeutralFutureReceive()\n    | StateNeutralCapacityReceive()",
			"StateNeutralFutureReceive()",
		),
	] {
		assert_finite_receive_fixture_rejected(
			name,
			"finite receive two-leg scenario composition",
			move |snapshot| replace_once(&mut snapshot.environment, from, to),
		);
		mutation_count += 1;
	}

	let short_scope = "let StateNeutralFutureReceive() =";
	for (name, from, to, diagnostic) in [
		(
			"finite_receive_short_skipped_sequence_skips_a_step",
			"let skipped_sequence = next_sequence(first) in",
			"let skipped_sequence = next_sequence(next_sequence(first)) in",
			"finite receive short sequence prefix",
		),
		(
			"finite_receive_short_target_sequence_reuses_first",
			"let target_sequence = next_sequence(skipped_sequence) in",
			"let target_sequence = next_sequence(first) in",
			"finite receive short sequence prefix",
		),
		(
			"finite_receive_short_chain_2_skips_a_step",
			"let chain_2 = ratchet_next(chain_1) in",
			"let chain_2 = ratchet_next(ratchet_next(chain_1)) in",
			"finite receive short ratchet chain",
		),
		(
			"finite_receive_short_chain_3_reuses_chain_1",
			"let chain_3 = ratchet_next(chain_2) in",
			"let chain_3 = ratchet_next(chain_1) in",
			"finite receive short ratchet chain",
		),
		(
			"finite_receive_short_chain_4_reuses_chain_2",
			"let chain_4 = ratchet_next(chain_3) in",
			"let chain_4 = ratchet_next(chain_2) in",
			"finite receive short ratchet chain",
		),
		(
			"finite_receive_short_material_1_uses_chain_2",
			"let material_1 = ratchet_material(chain_1) in",
			"let material_1 = ratchet_material(chain_2) in",
			"finite receive short material chain",
		),
		(
			"finite_receive_short_skipped_material_uses_chain_3",
			"let skipped_material = ratchet_material(chain_2) in",
			"let skipped_material = ratchet_material(chain_3) in",
			"finite receive short material chain",
		),
		(
			"finite_receive_short_target_material_uses_chain_2",
			"let target_material = ratchet_material(chain_3) in",
			"let target_material = ratchet_material(chain_2) in",
			"finite receive short material chain",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.environment, short_scope, from, to);
		});
		mutation_count += 1;
	}

	let short_seal_replacements = [
		"root",
		"root",
		"next_sequence(target_sequence)",
		"receiver_id",
		"root",
	];
	for call_index in 0..3 {
		for (argument_index, replacement) in short_seal_replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_seal_{call_index}_argument_{argument_index}"),
				"finite receive short honest frame",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						"seal_frame",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (argument_index, replacement) in [
		"root",
		"target_frame",
		"skipped_frame",
		"skipped_sequence",
		"receiver_id",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_forged_frame_argument_{argument_index}"),
			"finite receive short forged target frame",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"crypto_frame",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	let short_message_sent_replacements = [
		"root",
		"beacon_to_server()",
		"next_sequence(target_sequence)",
		"receiver_id",
		"sender_id",
		"root",
	];
	for call_index in 0..3 {
		for (argument_index, replacement) in short_message_sent_replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_sent_{call_index}_argument_{argument_index}"),
				"finite receive short sent message",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						"MessageSent",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	let short_open_replacements = [
		"root",
		"root",
		"next_sequence(target_sequence)",
		"receiver_id",
		"root",
	];
	for (call_index, diagnostic) in [
		(0, "finite receive short initial open"),
		(1, "finite receive first exact-frame destructor rejection"),
		(
			2,
			"finite receive repeated exact-frame destructor rejection",
		),
		(3, "finite receive short future open"),
		(4, "finite receive delayed cached-key consumption"),
	] {
		for (argument_index, replacement) in short_open_replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_open_{call_index}_argument_{argument_index}"),
				diagnostic,
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						"open_frame",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (call_index, diagnostic) in [
		(0, "finite receive short first delivery"),
		(3, "finite receive short future delivery"),
		(4, "finite receive delayed delivery"),
	] {
		for (argument_index, replacement) in [
			"root",
			"beacon_to_server()",
			"next_sequence(target_sequence)",
			"receiver_id",
			"sender_id",
			"root",
		]
		.into_iter()
		.enumerate()
		{
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_received_{call_index}_argument_{argument_index}"),
				diagnostic,
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						"MessageReceived",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (argument_index, replacement) in ["target_sequence", "root", "receive_cache_empty()"]
		.into_iter()
		.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_ready_state_argument_{argument_index}"),
			"finite receive short entry state",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"receive_state",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, marker, from, to) in [
		(
			"finite_receive_short_first_equality_uses_honest_target",
			"in(c, forged_candidate: bitstring);",
			"if forged_candidate = forged_target_frame then",
			"if forged_candidate = target_frame then",
		),
		(
			"finite_receive_short_retry_equality_uses_first_candidate",
			"in(c, repeated_candidate: bitstring);",
			"if repeated_candidate = forged_target_frame then",
			"if repeated_candidate = forged_candidate then",
		),
	] {
		assert_finite_receive_fixture_rejected(
			name,
			if name.contains("retry") {
				"finite receive repeated exact-frame destructor rejection"
			} else {
				"finite receive first exact-frame destructor rejection"
			},
			move |snapshot| replace_once_after(&mut snapshot.environment, marker, from, to),
		);
		mutation_count += 1;
	}
	for (name, marker, diagnostic) in [
		(
			"finite_receive_short_first_bypasses_destructor_failure",
			"in(c, forged_candidate: bitstring);",
			"finite receive first exact-frame destructor rejection",
		),
		(
			"finite_receive_short_retry_bypasses_destructor_failure",
			"in(c, repeated_candidate: bitstring);",
			"finite receive repeated exact-frame destructor rejection",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				marker,
				"open_frame(",
				"seal_frame(",
			);
		});
		mutation_count += 1;
	}

	for (event, diagnostic, replacements) in [
		(
			"ReceiveRejectedNeutral",
			"finite receive first exact-frame destructor rejection",
			["root", "first", "target_frame", "root"],
		),
		(
			"ReceiveRejectionRetried",
			"finite receive repeated exact-frame destructor rejection",
			["root", "first", "target_frame", "root"],
		),
	] {
		for (argument_index, replacement) in replacements.into_iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_{event}_argument_{argument_index}"),
				diagnostic,
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						event,
						0,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (index, (from, to)) in [
		("session,\n              target_sequence,", "root,\n              target_sequence,"),
		("target_sequence,\n              ready_state,", "first,\n              ready_state,"),
		("ready_state,\n              ready_state,", "root,\n              ready_state,"),
		("ready_state,\n              chain_2,", "root,\n              chain_2,"),
		("chain_2,\n              empty_cache,", "root,\n              empty_cache,"),
		(
			"empty_cache,\n              compromise_ack",
			"receive_cache_entry(skipped_sequence, skipped_material, empty_cache),\n              compromise_ack",
		),
		("compromise_ack\n            )", "c\n            )"),
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_rejection_snapshot_field_{index}"),
			"finite receive unchanged rejection snapshot",
			move |snapshot| {
				replace_once_after(
					&mut snapshot.environment,
					"out(\n            receive_snapshots",
					from,
					to,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in ["first", "root", "receive_cache_empty()"]
		.into_iter()
		.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_committed_state_argument_{argument_index}"),
			"finite receive short successful skipped publication",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"receive_state",
					1,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"first",
		"root",
		"receive_cache_entry(first,material_1,empty_cache)",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_cache_entry_argument_{argument_index}"),
			"finite receive short successful skipped publication",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"receive_cache_entry",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in [
		"root",
		"server_role()",
		"beacon_to_server()",
		"first",
		"root",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_cached_event_argument_{argument_index}"),
			"finite receive short skipped-key cache event",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"MessageKeyCached",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (event, diagnostic, replacements) in [
		(
			"ReceiveFutureAccepted",
			"finite receive future acceptance",
			[
				"root",
				"first",
				"receiver_id",
				"sender_id",
				"root",
				"target_frame",
				"skipped_material",
				"target_frame",
				"committed_state",
				"ready_state",
			],
		),
		(
			"ReceiveHonestFutureDelivered",
			"finite receive honest future selection and delivery",
			[
				"root",
				"first",
				"receiver_id",
				"sender_id",
				"root",
				"target_frame",
				"skipped_material",
				"target_frame",
				"committed_state",
				"ready_state",
			],
		),
		(
			"ReceiveReplayRejected",
			"finite receive exact accepted-frame replay",
			[
				"root",
				"first",
				"receiver_id",
				"sender_id",
				"root",
				"target_frame",
				"skipped_material",
				"target_frame",
				"committed_state",
				"ready_state",
			],
		),
	] {
		for (argument_index, replacement) in replacements.into_iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_short_{event}_argument_{argument_index}"),
				diagnostic,
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						short_scope,
						event,
						0,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"finite_receive_short_honest_gate_uses_forgery",
			"event ReceiveFutureAccepted(",
			"if accepted_candidate = target_frame then",
			"if accepted_candidate = forged_target_frame then",
			"finite receive honest future selection and delivery",
		),
		(
			"finite_receive_short_replay_gate_uses_honest_frame",
			"in(c, replay_candidate: bitstring);",
			"if replay_candidate = accepted_candidate then",
			"if replay_candidate = target_frame then",
			"finite receive exact accepted-frame replay",
		),
	] {
		assert_finite_receive_fixture_rejected(name, diagnostic, move |snapshot| {
			replace_once_after(&mut snapshot.environment, marker, from, to);
		});
		mutation_count += 1;
	}

	for (argument_index, replacement) in [
		"root",
		"server_role()",
		"beacon_to_server()",
		"first",
		"root",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_target_unavailable_argument_{argument_index}"),
			"finite receive short target consumption",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"MessageKeyUnavailable",
					1,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in
		["first", "root", "committed_cache"].into_iter().enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_delayed_state_argument_{argument_index}"),
			"finite receive delayed cached-key consumption",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"receive_state",
					2,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"root",
		"server_role()",
		"beacon_to_server()",
		"first",
		"root",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_delayed_unavailable_argument_{argument_index}"),
			"finite receive delayed key unavailability",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"MessageKeyUnavailable",
					2,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"root",
		"first",
		"receiver_id",
		"sender_id",
		"root",
		"skipped_frame",
		"target_material",
		"delayed_state",
		"committed_state",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_short_delayed_event_argument_{argument_index}"),
			"finite receive delayed cached acceptance",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					short_scope,
					"ReceiveDelayedCachedAccepted",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	assert_finite_receive_fixture_rejected(
		"finite_receive_short_retains_target_in_cache",
		"finite receive short target retained in cache",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				short_scope,
				"let committed_cache = receive_cache_entry(",
				"let forbidden_target_cache = receive_cache_entry(target_sequence, target_material, empty_cache) in\n          let committed_cache = receive_cache_entry(",
			);
		},
	);
	mutation_count += 1;

	let capacity_scope = "let StateNeutralCapacityReceive() =";
	for sequence in 2..=54 {
		let previous = sequence - 1;
		let from = format!(
			"let capacity_sequence_{sequence} = next_sequence(capacity_sequence_{previous}) in"
		);
		let to = format!(
			"let capacity_sequence_{sequence} = next_sequence(next_sequence(capacity_sequence_{previous})) in"
		);
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_sequence_{sequence}_drifts"),
			"finite receive capacity sequence chain",
			move |snapshot| {
				replace_once_after(&mut snapshot.environment, capacity_scope, &from, &to);
			},
		);
		mutation_count += 1;
	}
	for chain in 2..=55 {
		let previous = chain - 1;
		let from =
			format!("let capacity_chain_{chain} = ratchet_next(capacity_chain_{previous}) in");
		let to = format!(
			"let capacity_chain_{chain} = ratchet_next(ratchet_next(capacity_chain_{previous})) in"
		);
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_chain_{chain}_drifts"),
			"finite receive capacity ratchet chain",
			move |snapshot| {
				replace_once_after(&mut snapshot.environment, capacity_scope, &from, &to);
			},
		);
		mutation_count += 1;
	}
	for material in 1..=54 {
		let from = format!(
			"let capacity_material_{material} = ratchet_material(capacity_chain_{material}) in"
		);
		let to =
			format!("let capacity_material_{material} = ratchet_material(capacity_chain_55) in");
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_material_{material}_drifts"),
			"finite receive capacity material chain",
			move |snapshot| {
				replace_once_after(&mut snapshot.environment, capacity_scope, &from, &to);
			},
		);
		mutation_count += 1;
	}

	let capacity_frame_replacements = [
		"capacity_root",
		"capacity_root",
		"next_sequence(capacity_sequence_54)",
		"capacity_receiver_id",
		"capacity_root",
	];
	for call_index in 0..4 {
		for (argument_index, replacement) in capacity_frame_replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_capacity_seal_{call_index}_argument_{argument_index}"),
				"finite receive capacity honest frame",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"seal_frame",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}
	for call_index in 0..4 {
		for (argument_index, replacement) in [
			"capacity_root",
			"beacon_to_server()",
			"next_sequence(capacity_sequence_54)",
			"capacity_receiver_id",
			"capacity_sender_id",
			"capacity_root",
		]
		.into_iter()
		.enumerate()
		{
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_capacity_sent_{call_index}_argument_{argument_index}"),
				"finite receive capacity sent message",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"MessageSent",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (argument_index, replacement) in [
		"capacity_root",
		"maximum_gap_frame",
		"cached_frame",
		"capacity_sequence_53",
		"capacity_receiver_id",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_rejected_frame_argument_{argument_index}"),
			"finite receive capacity rejected frame",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"crypto_frame",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for call_index in 0..4 {
		for (argument_index, replacement) in capacity_frame_replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_capacity_open_{call_index}_argument_{argument_index}"),
				match call_index {
					0 => "finite receive capacity initial open",
					1 => "finite receive maximum-gap open",
					2 => "finite receive cached release open",
					_ => "finite receive after-release open",
				},
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"open_frame",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}
	for call_index in 0..4 {
		for (argument_index, replacement) in [
			"capacity_root",
			"beacon_to_server()",
			"next_sequence(capacity_sequence_54)",
			"capacity_receiver_id",
			"capacity_sender_id",
			"capacity_root",
		]
		.into_iter()
		.enumerate()
		{
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_capacity_received_{call_index}_argument_{argument_index}"),
				match call_index {
					0 => "finite receive capacity first delivery",
					1 => "finite receive maximum-gap delivery",
					2 => "finite receive cached delivery",
					_ => "finite receive after-release delivery",
				},
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"MessageReceived",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (argument_index, replacement) in [
		"capacity_sequence_54",
		"capacity_root",
		"receive_cache_entry(capacity_sequence_1,capacity_material_1,capacity_cache_empty)",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_ready_state_argument_{argument_index}"),
			"finite receive capacity entry state",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"receive_state",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for skipped in 2..=51 {
		let event_index = skipped - 2;
		for (argument_index, replacement) in [
			"capacity_root",
			"server_role()",
			"beacon_to_server()",
			"capacity_sequence_1",
			"capacity_material_1",
		]
		.into_iter()
		.enumerate()
		{
			assert_finite_receive_fixture_rejected(
				&format!(
					"finite_receive_capacity_cached_event_{event_index}_argument_{argument_index}"
				),
				"finite receive maximum-gap cached-key event",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"MessageKeyCached",
						event_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
		for (argument_index, replacement) in [
			"capacity_sequence_1",
			"capacity_material_1",
			"receive_cache_entry(capacity_sequence_1,capacity_material_1,capacity_cache_empty)",
		]
		.into_iter()
		.enumerate()
		{
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_capacity_cache_{skipped}_argument_{argument_index}"),
				"finite receive maximum-gap cache construction",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.environment,
						capacity_scope,
						"receive_cache_entry",
						event_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}

	for (argument_index, replacement) in
		["capacity_sequence_51", "capacity_root", "capacity_cache_50"]
			.into_iter()
			.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_max_state_argument_{argument_index}"),
			"finite receive maximum-gap state",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"receive_state",
					1,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in [
		"capacity_root",
		"server_role()",
		"beacon_to_server()",
		"capacity_sequence_51",
		"capacity_material_51",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_max_unavailable_argument_{argument_index}"),
			"finite receive maximum-gap target consumption",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"MessageKeyUnavailable",
					1,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"capacity_sequence_51",
		"capacity_receiver_id",
		"capacity_sender_id",
		"capacity_root",
		"maximum_gap_frame",
		"capacity_material_51",
		"maximum_gap_state",
		"capacity_ready_state",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_max_event_argument_{argument_index}"),
			"finite receive maximum-gap acceptance",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"ReceiveMaximumGapAccepted",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	assert_finite_receive_fixture_rejected(
		"finite_receive_capacity_gate_uses_honest_after_release_frame",
		"finite receive full-cache exact-frame gate",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"in(c, capacity_rejected_candidate: bitstring);",
				"if capacity_rejected_candidate = capacity_rejected_frame then",
				"if capacity_rejected_candidate = after_release_frame then",
			);
		},
	);
	mutation_count += 1;
	for (argument_index, replacement) in [
		"capacity_root",
		"capacity_sequence_53",
		"after_release_frame",
		"capacity_ready_state",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_rejected_event_argument_{argument_index}"),
			"finite receive full-cache rejection",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"ReceiveCapacityRejected",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in
		["capacity_sequence_51", "capacity_root", "capacity_cache_51"]
			.into_iter()
			.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_released_state_argument_{argument_index}"),
			"finite receive cached capacity release",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"receive_state",
					2,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"server_role()",
		"beacon_to_server()",
		"capacity_sequence_52",
		"capacity_material_52",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_cached_unavailable_argument_{argument_index}"),
			"finite receive cached key unavailability",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"MessageKeyUnavailable",
					2,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"capacity_sequence_52",
		"capacity_material_52",
		"released_state",
		"maximum_gap_state",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_cached_consumed_argument_{argument_index}"),
			"finite receive cached last-slot consumption event",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"ReceiveCachedKeyConsumed",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (argument_index, replacement) in [
		"capacity_sequence_52",
		"capacity_material_52",
		"capacity_cache_51",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_after_cache_argument_{argument_index}"),
			"finite receive after-release state",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"receive_cache_entry",
					50,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in
		["capacity_sequence_52", "capacity_root", "capacity_cache_50"]
			.into_iter()
			.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_after_state_argument_{argument_index}"),
			"finite receive after-release state",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"receive_state",
					3,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"server_role()",
		"beacon_to_server()",
		"capacity_sequence_52",
		"capacity_material_52",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_after_cached_event_argument_{argument_index}"),
			"finite receive after-release skipped-key event",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"MessageKeyCached",
					50,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"server_role()",
		"beacon_to_server()",
		"capacity_sequence_53",
		"capacity_material_53",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_after_unavailable_argument_{argument_index}"),
			"finite receive after-release target consumption",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"MessageKeyUnavailable",
					3,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}
	for (argument_index, replacement) in [
		"capacity_root",
		"capacity_sequence_53",
		"capacity_receiver_id",
		"capacity_sender_id",
		"capacity_root",
		"after_release_frame",
		"capacity_material_53",
		"released_state",
		"maximum_gap_state",
		"released_state",
	]
	.into_iter()
	.enumerate()
	{
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_after_event_argument_{argument_index}"),
			"finite receive after-release acceptance",
			move |snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.environment,
					capacity_scope,
					"ReceiveAfterCapacityReleaseAccepted",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (target, scope_anchor, insertion_anchor) in [
		(
			"capacity_sequence_52",
			capacity_scope,
			"let maximum_gap_state = receive_state(",
		),
		(
			"capacity_sequence_54",
			"let after_release_state = receive_state(",
			"event MessageReceived(",
		),
	] {
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_capacity_retains_target_{target}"),
			"finite receive target retained in capacity cache",
			move |snapshot| {
				replace_once_after(
					&mut snapshot.environment,
					scope_anchor,
					insertion_anchor,
					&format!(
						"let forbidden_target_cache = receive_cache_entry({target}, capacity_material_54, capacity_cache_empty) in\n  {insertion_anchor}"
					),
				);
			},
		);
		mutation_count += 1;
	}

	for secret in [
		"RECEIVE_PAST_SECRET",
		"RECEIVE_SKIPPED_SECRET",
		"RECEIVE_TARGET_SECRET",
		"RECEIVE_MAX_GAP_SECRET",
		"RECEIVE_CACHED_SECRET",
		"RECEIVE_AFTER_RELEASE_SECRET",
	] {
		assert_finite_receive_fixture_rejected(
			&format!("finite_receive_secrecy_query_{secret}_drifts"),
			"finite receive secrecy query",
			move |snapshot| {
				replace_once(
					&mut snapshot.failed_receive_queries,
					&format!("query attacker({secret})."),
					"query attacker(forged_frame_component()).",
				);
			},
		);
		mutation_count += 1;
	}

	let correspondence_event_shapes: &[(&str, usize, &[&str])] = &[
		(
			"ReceiveRejectionRetried",
			2,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveRejectedNeutral",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveFutureAccepted",
			4,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveHonestFutureDelivered",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveReplayRejected",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveDelayedCachedAccepted",
			2,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveMaximumGapAccepted",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveCachedKeyConsumed",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveAfterCapacityReleaseAccepted",
			1,
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"MessageKeyCached",
			1,
			&[
				"forged_frame_component()",
				"server_role()",
				"beacon_to_server()",
				"first_sequence()",
				"forged_frame_component()",
			],
		),
		(
			"MessageKeyUnavailable",
			5,
			&[
				"forged_frame_component()",
				"server_role()",
				"beacon_to_server()",
				"first_sequence()",
				"forged_frame_component()",
			],
		),
		(
			"MessageReceived",
			1,
			&[
				"forged_frame_component()",
				"beacon_to_server()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
			],
		),
		(
			"MessageSent",
			1,
			&[
				"forged_frame_component()",
				"beacon_to_server()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
			],
		),
	];
	for &(event, occurrences, replacements) in correspondence_event_shapes {
		for occurrence in 0..occurrences {
			for (argument_index, replacement) in replacements.iter().enumerate() {
				assert_finite_receive_fixture_rejected(
					&format!(
						"finite_receive_correspondence_{event}_{occurrence}_argument_{argument_index}"
					),
					"finite receive exact correspondence query",
					move |snapshot| {
						replace_nth_call_argument_after(
							&mut snapshot.failed_receive_queries,
							"query ",
							event,
							occurrence,
							argument_index,
							replacement,
						);
					},
				);
				mutation_count += 1;
			}
		}
	}
	assert_finite_receive_fixture_rejected(
		"finite_receive_correspondence_count_drops",
		"finite receive correspondence query count changed",
		|snapshot| {
			replace_once(
				&mut snapshot.failed_receive_queries,
				")) ==>\n  inj-event(",
				")) &&\n  inj-event(",
			);
		},
	);
	mutation_count += 1;

	let reachability_event_shapes: &[(&str, &[&str])] = &[
		(
			"ReceiveRejectedNeutral",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveRejectionRetried",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveFutureAccepted",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveHonestFutureDelivered",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveReplayRejected",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveDelayedCachedAccepted",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveMaximumGapAccepted",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveCapacityRejected",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveCachedKeyConsumed",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
		(
			"ReceiveAfterCapacityReleaseAccepted",
			&[
				"forged_frame_component()",
				"first_sequence()",
				"SERVER_KEY_ID",
				"SERVER_KEY_ID",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
				"forged_frame_component()",
			],
		),
	];
	for &(event, replacements) in reachability_event_shapes {
		for (argument_index, replacement) in replacements.iter().enumerate() {
			assert_finite_receive_fixture_rejected(
				&format!("finite_receive_reachability_{event}_argument_{argument_index}"),
				"finite receive exact event reachability query",
				move |snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.failed_receive_reachability_queries,
						"query ",
						event,
						0,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}
	assert_finite_receive_fixture_rejected(
		"finite_receive_reachability_query_count_drops",
		"finite receive reachability query count changed",
		|snapshot| {
			replace_once(
				&mut snapshot.failed_receive_reachability_queries,
				"query attacker(MALICIOUS_TASK_SECRET).",
				"event(MaliciousRegistrationCommitted(transcript, plaintext)).",
			);
		},
	);
	mutation_count += 1;

	assert_eq!(mutation_count, FINITE_RECEIVE_STATE_FIXTURE_MUTATION_COUNT);
}

const REGISTRATION_LIFECYCLE_MUTATION_COUNT: usize = 177;

#[test]
fn registration_lifecycle_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	let lifecycle_facts = parse_facts(INTERFACE)
		.unwrap()
		.into_iter()
		.filter(|fact| fact.starts_with("registration.lifecycle."))
		.collect::<Vec<_>>();
	assert_eq!(lifecycle_facts.len(), 60);
	for fact in lifecycle_facts {
		let (key, _) = fact.split_once('=').unwrap();
		assert_registration_lifecycle_rejected(
			&format!("registration_lifecycle_fact_{key}"),
			key,
			|snapshot| mutate_fact(&mut snapshot.interface, key, "mutated"),
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"registration_identity_width_drifts",
			"pub const SIGN_PUBLIC_KEY_SIZE: usize = 32;",
			"pub const SIGN_PUBLIC_KEY_SIZE: usize = 31;",
			"registration replay identity width",
		),
		(
			"registration_one_time_width_drifts",
			"pub const X25519_PUBLIC_KEY_SIZE: usize = 32;",
			"pub const X25519_PUBLIC_KEY_SIZE: usize = 31;",
			"registration replay one-time-key width",
		),
		(
			"registration_identifier_width_uses_pq",
			"pub const REGISTRATION_ID_SIZE: usize = SIGN_PUBLIC_KEY_SIZE + X25519_PUBLIC_KEY_SIZE;",
			"pub const REGISTRATION_ID_SIZE: usize = SIGN_PUBLIC_KEY_SIZE + MLKEM768_PUBLIC_KEY_SIZE;",
			"registration replay identifier width expression",
		),
		(
			"registration_identifier_assertion_drifts",
			"const _: () = assert!(REGISTRATION_ID_SIZE == 64);",
			"const _: () = assert!(REGISTRATION_ID_SIZE == 63);",
			"registration replay identifier 64-byte assertion",
		),
		(
			"registration_identifier_first_half_uses_prekey",
			"self.beacon_identity_public_key[i]",
			"self.beacon_prekey_public_key[i]",
			"registration replay identity-then-one-time layout",
		),
		(
			"registration_identifier_second_half_uses_prekey",
			"self.beacon_one_time_public_key[i - SIGN_PUBLIC_KEY_SIZE]",
			"self.beacon_prekey_public_key[i - SIGN_PUBLIC_KEY_SIZE]",
			"registration replay identity-then-one-time layout",
		),
		(
			"registration_identifier_second_half_offset_drifts",
			"i - SIGN_PUBLIC_KEY_SIZE",
			"i - X25519_PUBLIC_KEY_SIZE",
			"registration replay identity-then-one-time layout",
		),
		(
			"registration_identifier_wrapper_bypasses_method",
			"registration.registration_id()",
			"RegistrationId { bytes: [0; REGISTRATION_ID_SIZE] }",
			"registration replay identifier wrapper",
		),
		(
			"registration_beacon_start_result_stays_fresh",
			"pub state: BeaconInitSent,",
			"pub state: BeaconFresh,",
			"registration beacon-start result typestate",
		),
		(
			"registration_beacon_start_maps_fresh_state",
			"state: BeaconInitSent {",
			"state: BeaconFresh {",
			"registration beacon-start Fresh-to-InitSent mapping",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_pqxdh, from, to);
		});
		mutation_count += 1;
	}
	for (name, replacement) in [
		(
			"registration_proverif_projection_swaps_halves",
			"registration_identifier(one_time, identity)",
		),
		(
			"registration_proverif_projection_uses_prekey",
			"registration_identifier(identity, prekey)",
		),
		(
			"registration_proverif_projection_uses_pq",
			"registration_identifier(identity, pq)",
		),
	] {
		assert_registration_lifecycle_rejected(
			name,
			"registration replay ProVerif identity/one-time projection",
			|snapshot| {
				replace_once(
					&mut snapshot.extraction,
					"registration_identifier(identity, one_time)",
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"registration_beacon_identity_generation_changes",
			"identity_key: crypto_sign::KeyPair::generate().unwrap(),",
			"identity_key: crypto_kx::KeyPair::generate().unwrap(),",
			"registration Beacon identity generation",
		),
		(
			"registration_beacon_new_state_changes",
			"state: BeaconState::Fresh {",
			"state: BeaconState::InitSent {",
			"registration Beacon Fresh material co-location",
		),
		(
			"registration_beacon_prekey_generation_changes",
			"prekey: crypto_kx::KeyPair::generate().unwrap(),",
			"prekey: crypto_kem::mlkem768::KeyPair::generate().unwrap(),",
			"registration Beacon Fresh material co-location",
		),
		(
			"registration_beacon_pq_generation_changes",
			"pq_key: crypto_kem::mlkem768::KeyPair::generate().unwrap(),",
			"pq_key: crypto_kx::KeyPair::generate().unwrap(),",
			"registration Beacon Fresh material co-location",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_beacon, "pub fn new(", from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"registration_fresh_coin_condition_changes",
			"matches!(&self.state, BeaconState::Fresh { .. })",
			"matches!(&self.state, BeaconState::FreshWithCoins { .. })",
			"registration Fresh one-time generation",
		),
		(
			"registration_fresh_coin_generation_removed",
			"Some(crypto_kx::KeyPair::generate().ok()?)",
			"None",
			"registration Fresh one-time generation",
		),
		(
			"registration_fresh_arm_accepts_init_sent",
			"BeaconState::Fresh {\n\t\t\t\tcontrol,\n\t\t\t\tprekey,\n\t\t\t\tpq_key,\n\t\t\t}",
			"BeaconState::InitSent {\n\t\t\t\tcontrol,\n\t\t\t\tprekey,\n\t\t\t\tpq_key,\n\t\t\t}",
			"registration Fresh material selection",
		),
		(
			"registration_fresh_with_coins_arm_accepts_established",
			"BeaconState::FreshWithCoins {\n\t\t\t\tcontrol,\n\t\t\t\tprekey,\n\t\t\t\tonetime_key,\n\t\t\t\tpq_key,\n\t\t\t}",
			"BeaconState::Established {\n\t\t\t\tcontrol,\n\t\t\t\tprekey,\n\t\t\t\tonetime_key,\n\t\t\t\tpq_key,\n\t\t\t}",
			"registration FreshWithCoins material selection",
		),
		(
			"registration_ineligible_state_falls_through",
			"_ => return None,",
			"_ => unreachable!(),",
			"registration ineligible-state rejection",
		),
		(
			"registration_fresh_prekey_uses_pq",
			"prekey.public_key.as_bytes().try_into().ok()?,",
			"pq_key.public_key.as_bytes().try_into().ok()?,",
			"registration Fresh material selection",
		),
		(
			"registration_fresh_pq_uses_prekey",
			"*pq_key.public_key.as_bytes(),",
			"*prekey.public_key.as_bytes(),",
			"registration Fresh material selection",
		),
		(
			"registration_fresh_one_time_uses_prekey",
			"generated_onetime\n\t\t\t\t\t.as_ref()?",
			"Some(prekey)\n\t\t\t\t\t.as_ref()?",
			"registration Fresh material selection",
		),
		(
			"registration_stored_one_time_uses_prekey",
			"onetime_key.public_key.as_bytes().try_into().ok()?,",
			"prekey.public_key.as_bytes().try_into().ok()?,",
			"registration FreshWithCoins material selection",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon",
				from,
				to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to) in [
		(
			"registration_start_identity_uses_server",
			"identity_public_key: *self.identity_pk().as_bytes(),",
			"identity_public_key: *self.server_id().as_bytes(),",
		),
		(
			"registration_start_prekey_uses_one_time",
			"prekey_public_key: prekey_public,",
			"prekey_public_key: onetime_public,",
		),
		(
			"registration_start_pq_uses_prekey",
			"pq_public_key: pq_public,",
			"pq_public_key: prekey_public,",
		),
		(
			"registration_start_one_time_uses_prekey",
			"one_time_public_key: onetime_public,",
			"one_time_public_key: prekey_public,",
		),
	] {
		assert_registration_lifecycle_rejected(
			name,
			"registration Beacon-start input mapping",
			|snapshot| {
				replace_once_after(
					&mut snapshot.adapter_beacon,
					"impl ProviderBeacon for Beacon",
					from,
					to,
				);
			},
		);
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"registration_builder_type_changes",
			"TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default()",
			"TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default()",
			"registration typed InitKex builder",
		),
		(
			"registration_identity_setter_uses_prekey",
			"bundle.set_identity_key(started.message.identity_key());",
			"bundle.set_identity_key(started.message.prekey());",
			"registration serialized identity field",
		),
		(
			"registration_prekey_setter_uses_one_time",
			"bundle.set_pre_key(&prekey_sig);",
			"bundle.set_pre_key(&onetime_sig);",
			"registration serialized prekey field",
		),
		(
			"registration_one_time_setter_uses_prekey",
			"bundle.set_one_time_key(&onetime_sig);",
			"bundle.set_one_time_key(&prekey_sig);",
			"registration serialized one-time field",
		),
		(
			"registration_pq_setter_uses_prekey",
			"bundle.set_pq_key(&pq_sig);",
			"bundle.set_pq_key(&prekey_sig);",
			"registration serialized PQ field",
		),
		(
			"registration_serialization_call_removed",
			"capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).ok()?;",
			"let _ = (&mut buffer, msg.borrow_inner());",
			"registration completed InitKex serialization",
		),
		(
			"registration_success_returns_none",
			"Some(buffer)\n\t}",
			"None\n\t}",
			"registration serialized bundle return",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	assert_registration_lifecycle_rejected(
		"registration_state_transition_precedes_serialization",
		"registration serialization-to-InitSent order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon",
				"\t\tlet mut buffer = vec![];\n\t\tcapnp::serialize::write_message(&mut buffer, msg.borrow_inner()).ok()?;\n\n\t\tlet fallback = BeaconState::Aborted {\n\t\t\tcontrol: verified_pqxdh::beacon_abort_fresh(control),\n\t\t};\n\t\tlet previous = std::mem::replace(&mut self.state, fallback);",
				"\t\tlet mut buffer = vec![];\n\n\t\tlet fallback = BeaconState::Aborted {\n\t\t\tcontrol: verified_pqxdh::beacon_abort_fresh(control),\n\t\t};\n\t\tlet previous = std::mem::replace(&mut self.state, fallback);\n\t\tcapnp::serialize::write_message(&mut buffer, msg.borrow_inner()).ok()?;",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_pretransition_failure_changes_state",
		"registration Beacon state changed before successful serialization",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon",
				"let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();",
				"self.state = BeaconState::Aborted { control: verified_pqxdh::beacon_abort_fresh(control) };\n\t\tlet mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();",
			);
		},
	);
	mutation_count += 1;
	for (name, marker, from, to, diagnostic) in [
		(
			"registration_fresh_success_reopens_fresh",
			"capnp::serialize::write_message",
			"self.state = BeaconState::InitSent {",
			"self.state = BeaconState::Fresh {",
			"registration Fresh success transition and restoration",
		),
		(
			"registration_fresh_success_uses_old_control",
			"capnp::serialize::write_message",
			"control: started.state,",
			"control,",
			"registration Fresh success transition and restoration",
		),
		(
			"registration_fresh_success_drops_generated_one_time",
			"capnp::serialize::write_message",
			"onetime_key,\n\t\t\t\t\tpq_key,",
			"onetime_key: crypto_kx::KeyPair::generate().unwrap(),\n\t\t\t\t\tpq_key,",
			"registration Fresh success transition and restoration",
		),
		(
			"registration_fresh_take_failure_aborts",
			"let Some(onetime_key) = generated_onetime.take() else {",
			"self.state = BeaconState::Fresh {",
			"self.state = BeaconState::Aborted {",
			"registration Fresh success transition and restoration",
		),
		(
			"registration_stored_success_reopens_fresh_with_coins",
			"BeaconState::FreshWithCoins {\n\t\t\t\tprekey,",
			"self.state = BeaconState::InitSent {",
			"self.state = BeaconState::FreshWithCoins {",
			"registration FreshWithCoins success transition",
		),
		(
			"registration_stored_success_uses_old_control",
			"BeaconState::FreshWithCoins {\n\t\t\t\tprekey,",
			"control: started.state,",
			"control,",
			"registration FreshWithCoins success transition",
		),
		(
			"registration_stored_success_swaps_one_time_and_prekey",
			"BeaconState::FreshWithCoins {\n\t\t\t\tprekey,",
			"prekey,\n\t\t\t\t\tonetime_key,",
			"prekey: onetime_key,\n\t\t\t\t\tonetime_key: prekey,",
			"registration FreshWithCoins success transition",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_beacon, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"registration_new_one_time_accepts_init_sent",
			"pub fn new_onetime_keypair",
			"BeaconState::Fresh { control, .. } => *control,",
			"BeaconState::InitSent { control, .. } => *control,",
			"registration post-Init one-time regeneration rejection",
		),
		(
			"registration_abort_reopens_fresh",
			"fn abort_registration",
			"self.state = BeaconState::Aborted {",
			"self.state = BeaconState::Fresh {",
			"registration Beacon eligible-state publication graph",
		),
		(
			"registration_delete_one_time_reopens_init",
			"pub fn delete_onetime_keypair",
			"BeaconState::InitSent { control, .. } => BeaconState::Aborted {",
			"BeaconState::InitSent { control, .. } => BeaconState::Fresh {",
			"registration InitSent one-time deletion transition",
		),
		(
			"registration_delete_pq_uses_fresh_abort",
			"pub fn delete_pq_keypair",
			"Some(verified_pqxdh::beacon_abort_init(*control))",
			"Some(verified_pqxdh::beacon_abort_fresh(*control))",
			"registration InitSent PQ deletion transition",
		),
		(
			"registration_finish_accepts_fresh",
			"impl ProviderBeacon for Beacon",
			"BeaconState::InitSent { control, .. } => *control,",
			"BeaconState::Fresh { control, .. } => *control,",
			"registration finish InitSent gate",
		),
		(
			"registration_finish_failure_keeps_init",
			"impl ProviderBeacon for Beacon",
			"self.abort_registration(control);\n\t\t\treturn None;",
			"return None;",
			"registration failed finish abort",
		),
		(
			"registration_finish_success_reopens_fresh",
			"impl ProviderBeacon for Beacon",
			"self.state = BeaconState::Established {",
			"self.state = BeaconState::Fresh {",
			"registration Beacon eligible-state publication graph",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_beacon, marker, from, to);
		});
		mutation_count += 1;
	}
	for (name, from, diagnostic) in [
		(
			"registration_finish_server_key_id_mismatch_keeps_init",
			"if self.server_kid() != server_kid {\n\t\t\tself.abort_registration(control);\n\t\t\treturn None;\n\t\t}",
			"registration server-key-ID mismatch abort",
		),
		(
			"registration_finish_server_identity_mismatch_keeps_init",
			"if self.server_id.as_bytes() != &server_binding.identity_public_key {\n\t\t\tself.abort_registration(control);\n\t\t\treturn None;\n\t\t}",
			"registration server-identity mismatch abort",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			let to = from.replace("\n\t\t\tself.abort_registration(control);", "");
			replace_once_after(
				&mut snapshot.adapter_beacon,
				"impl ProviderBeacon for Beacon",
				from,
				&to,
			);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"registration_server_peer_map_replaced_by_replay_set",
			"known_ids: HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>",
			"known_ids: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>",
			"registration numeric peer map",
		),
		(
			"registration_server_replay_set_uses_numeric_ids",
			"consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>",
			"consumed_registrations: HashSet<u64>",
			"registration consumed-ID set",
		),
		(
			"registration_server_id_uses_peer_key_id",
			"*verified_pqxdh::registration_id(&verified_registration).as_bytes()",
			"self.identity_key_kid.to_le_bytes()",
			"registration Server ID source",
		),
		(
			"registration_server_status_uses_peer_map",
			"self.consumed_registrations.contains(&registration_id)",
			"self.known_ids.contains_key(&self.identity_key_kid)",
			"registration Server replay-status polarity",
		),
		(
			"registration_server_status_polarity_reverses_consumed",
			"verified_pqxdh::RegistrationStatus::Consumed\n\t\t} else {\n\t\t\tverified_pqxdh::RegistrationStatus::Fresh",
			"verified_pqxdh::RegistrationStatus::Fresh\n\t\t} else {\n\t\t\tverified_pqxdh::RegistrationStatus::Consumed",
			"registration Server replay-status polarity",
		),
		(
			"registration_server_status_gate_removed",
			"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
			"let _ = registration_status;",
			"registration Server replay-status gate",
		),
		(
			"registration_server_reservation_removed",
			"self.consumed_registrations.try_reserve(1).ok()?;",
			"let _ = self.consumed_registrations.capacity();",
			"registration Server consumed-set reservation",
		),
		(
			"registration_server_shared_secrets_reuses_dh3",
			"shared_secrets(dh1, dh2, dh3, dh4, &kem_shared)?",
			"shared_secrets(dh1, dh2, dh3, dh3, &kem_shared)?",
			"registration Server complete post-validation PQXDH inputs",
		),
		(
			"registration_server_insert_uses_derived_secret",
			"self.consumed_registrations.insert(registration_id)",
			"self.consumed_registrations.insert(*derived_secret.as_array())",
			"registration Server exact-ID consumption",
		),
		(
			"registration_server_output_removed",
			"Some(RegistrationOutput {",
			"Ok(RegistrationOutput {",
			"registration Server pending output",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_server, "pub struct Server", from, to);
		});
		mutation_count += 1;
	}

	for (name, argument_index, replacement) in [
		(
			"registration_server_accept_uses_unvalidated_init",
			1,
			"init_kex",
		),
		(
			"registration_server_accept_forces_fresh",
			2,
			"verified_pqxdh::RegistrationStatus::Fresh",
		),
	] {
		assert_registration_lifecycle_rejected(
			name,
			"registration Server accepted registration/status mapping changed",
			|snapshot| {
				replace_nth_call_argument_after(
					&mut snapshot.adapter_server,
					"fn get_shared_secret",
					"verified_pqxdh::server_accept",
					0,
					argument_index,
					replacement,
				);
			},
		);
		mutation_count += 1;
	}

	assert_registration_lifecycle_rejected(
		"registration_server_status_gate_moves_after_ephemeral_generation",
		"registration Server validate-reserve-derive-consume order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn get_shared_secret",
				"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
				"let _status_gate_moved = registration_status;",
			);
			replace_once_after(
				&mut snapshot.adapter_server,
				"let ephemeral = crypto_kx::KeyPair::generate().ok()?;",
				"let pq_pub =",
				"verified_pqxdh::validate_registration_status(registration_status).ok()?;\n\t\tlet pq_pub =",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_reservation_moves_after_ephemeral_generation",
		"registration Server validate-reserve-derive-consume order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn get_shared_secret",
				"self.consumed_registrations.try_reserve(1).ok()?;",
				"let _reservation_moved = self.consumed_registrations.capacity();",
			);
			replace_once_after(
				&mut snapshot.adapter_server,
				"let ephemeral = crypto_kx::KeyPair::generate().ok()?;",
				"let pq_pub =",
				"self.consumed_registrations.try_reserve(1).ok()?;\n\t\tlet pq_pub =",
			);
		},
	);
	mutation_count += 1;
	for (name, binding, expression) in [
		(
			"registration_server_dh2_moves_before_status_gate",
			"dh2",
			"crypto_scalarmult::scalarmult(&id_kex_sk, beacon_prekey.as_bytes()).ok()?.into()",
		),
		(
			"registration_server_dh3_moves_before_status_gate",
			"dh3",
			"crypto_scalarmult::scalarmult(&id_kex_sk, beacon_prekey.as_bytes()).ok()?.into()",
		),
		(
			"registration_server_dh4_moves_before_status_gate",
			"dh4",
			"crypto_scalarmult::scalarmult(&id_kex_sk, beacon_onetime.as_bytes()).ok()?.into()",
		),
	] {
		assert_registration_lifecycle_rejected(
			name,
			"registration Server validate-reserve-derive-consume order",
			|snapshot| {
				let original = if binding == "dh2" {
					format!("let {binding}: DhSecret =")
				} else {
					format!("let {binding}: DhSecret = crypto_scalarmult::scalarmult(")
				};
				let renamed = original.replacen(binding, &format!("{binding}_after_gate"), 1);
				replace_once_after(
					&mut snapshot.adapter_server,
					"fn get_shared_secret",
					&original,
					&renamed,
				);
				replace_once_after(
					&mut snapshot.adapter_server,
					"fn get_shared_secret",
					"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
					&format!(
						"let {binding}: DhSecret = {expression};\n\t\tverified_pqxdh::validate_registration_status(registration_status).ok()?;"
					),
				);
			},
		);
		mutation_count += 1;
	}
	assert_registration_lifecycle_rejected(
		"registration_server_root_derivation_uses_registration_id",
		"registration Server validate-reserve-derive-consume order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn get_shared_secret",
				"derive_root_key_input(pending.root_key_input_mut())?",
				"derive_root_key_input(&mut registration_id)?",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_consumes_before_root_derivation",
		"registration Server validate-reserve-derive-consume order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn get_shared_secret",
				"let inserted = self.consumed_registrations.insert(registration_id);\n\t\tdebug_assert!(inserted);",
				"let _insert_moved = inserted;",
			);
			replace_once_after(
				&mut snapshot.adapter_server,
				"let derived_secret = derive_root_key_input(pending.root_key_input_mut())?;",
				"let derived_secret = derive_root_key_input(pending.root_key_input_mut())?;",
				"let inserted = self.consumed_registrations.insert(registration_id);\n\t\tdebug_assert!(inserted);\n\t\tlet derived_secret = derive_root_key_input(pending.root_key_input_mut())?;",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_consumes_different_id_before_crypto",
		"registration Server consumed-ID insertion family count changed",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"fn get_shared_secret",
				"verified_pqxdh::validate_registration_status(registration_status).ok()?;",
				"self.consumed_registrations.insert([0; verified_pqxdh::REGISTRATION_ID_SIZE]);\n\t\tverified_pqxdh::validate_registration_status(registration_status).ok()?;",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_explicit_failure_after_consumption",
		"registration explicit failure moved after consumption insertion",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"let inserted = self.consumed_registrations.insert(registration_id);",
				"debug_assert!(inserted);",
				"debug_assert!(inserted);\n\t\tif !inserted { return None; }",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_fallible_work_after_consumption",
		"registration fallible work moved after consumption insertion",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"let inserted = self.consumed_registrations.insert(registration_id);",
				"debug_assert!(inserted);",
				"debug_assert!(inserted);\n\t\tlet _late = Some(())?;",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_response_failure_removes_consumed_id",
		"registration replay-set mutation during later response construction",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_server,
				"Some(RegistrationOutput {",
				"let control = self.control;",
				"self.consumed_registrations.clear();\n\t\tlet control = self.control;",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"registration_guard_first_identity_not_publicly_bound",
			"=beacon_identity,\n      accepted_init:",
			"accepted_identity: bitstring,\n      accepted_init:",
			"registration replay first public input",
		),
		(
			"registration_guard_first_init_type_changes",
			"accepted_init: beaconcrypt_core__pqxdh__t_InitKex",
			"accepted_init: bitstring",
			"registration replay first public input",
		),
		(
			"registration_guard_consumed_event_uses_replay_init",
			"accepted_init,\n    accepted_registration_id,",
			"replay_init,\n    accepted_registration_id,",
			"registration replay consumed event",
		),
		(
			"registration_guard_first_reply_is_consumed",
			"out(first_reply, replay_fresh());",
			"out(first_reply, replay_consumed());",
			"registration replay first Fresh reply",
		),
		(
			"registration_guard_later_identity_not_bound",
			"=beacon_identity,\n      replay_init:",
			"replay_identity: bitstring,\n      replay_init:",
			"registration replay replicated later input",
		),
		(
			"registration_guard_later_reply_is_fresh",
			"out(replay_reply, replay_consumed()).",
			"out(replay_reply, replay_fresh()).",
			"registration replay later Consumed reply",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let RegistrationReplayGuard(",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	assert_registration_lifecycle_rejected(
		"registration_guard_first_input_is_replicated",
		"registration replay first input replication",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let RegistrationReplayGuard(",
				"  in(\n    replay_requests,",
				"  !in(\n    replay_requests,",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_guard_later_input_loses_replication",
		"registration replay replicated later input",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"out(first_reply, replay_fresh());",
				"  !in(\n    replay_requests,",
				"  in(\n    replay_requests,",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_guard_consumed_event_moves_after_fresh_reply",
		"registration replay Fresh-to-Consumed owner order",
		|snapshot| {
			let event = "  event RegistrationConsumed(\n    server_identity,\n    beacon_identity,\n    accepted_init,\n    accepted_registration_id,\n    origin\n  );\n";
			replace_once_after(
				&mut snapshot.environment,
				"let RegistrationReplayGuard(",
				event,
				"",
			);
			replace_once_after(
				&mut snapshot.environment,
				"out(first_reply, replay_fresh());",
				"out(first_reply, replay_fresh());",
				&format!("out(first_reply, replay_fresh());\n{event}"),
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"registration_honest_guard_uses_wrong_identity",
			"RegistrationReplayGuard(\n    server_identity,\n    beacon_identity,",
			"RegistrationReplayGuard(\n    server_identity,\n    beacon_prekey,",
			"registration honest replay owner",
		),
		(
			"registration_honest_guard_is_replicated",
			"  RegistrationReplayGuard(\n",
			"  !RegistrationReplayGuard(\n",
			"registration replicated honest replay owner",
		),
		(
			"registration_honest_bundle_is_replicated",
			"  out(\n    c,\n    signed_init_kex(",
			"  !out(\n    c,\n    signed_init_kex(",
			"registration replicated honest signed bundle",
		),
		(
			"registration_honest_guard_and_bundle_are_sequential",
			"  )\n  |\n  out(\n    c,\n    signed_init_kex(",
			"  );\n  out(\n    c,\n    signed_init_kex(",
			"registration honest parallel bundle-and-guard topology",
		),
		(
			"registration_honest_bundle_identity_uses_prekey",
			"tag_ed25519(beacon_identity),",
			"tag_ed25519(beacon_prekey),",
			"registration honest single signed bundle",
		),
		(
			"registration_honest_bundle_prekey_uses_one_time",
			"sign(tag_x25519_prekey(beacon_prekey), beacon_identity_secret),",
			"sign(tag_x25519_prekey(beacon_one_time), beacon_identity_secret),",
			"registration honest single signed bundle",
		),
		(
			"registration_honest_bundle_one_time_uses_prekey",
			"sign(tag_x25519_one_time(beacon_one_time), beacon_identity_secret),",
			"sign(tag_x25519_one_time(beacon_prekey), beacon_identity_secret),",
			"registration honest single signed bundle",
		),
		(
			"registration_honest_bundle_pq_uses_one_time",
			"sign(tag_mlkem768(beacon_pq), beacon_identity_secret)",
			"sign(tag_mlkem768(beacon_one_time), beacon_identity_secret)",
			"registration honest single signed bundle",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			let marker = if name.starts_with("registration_honest_bundle_") {
				"  out(\n    c,\n    signed_init_kex("
			} else {
				"let HonestBeacon("
			};
			replace_once_after(&mut snapshot.environment, marker, from, to);
		});
		mutation_count += 1;
	}
	assert_registration_lifecycle_rejected(
		"registration_honest_bundle_is_duplicated",
		"registration honest single signed bundle",
		|snapshot| {
			let output = "  out(\n    c,\n    signed_init_kex(\n      tag_ed25519(beacon_identity),\n      sign(tag_x25519_prekey(beacon_prekey), beacon_identity_secret),\n      sign(tag_x25519_one_time(beacon_one_time), beacon_identity_secret),\n      sign(tag_mlkem768(beacon_pq), beacon_identity_secret)\n    )\n  );";
			replace_once_after(
				&mut snapshot.environment,
				"let HonestBeacon(",
				output,
				&format!("{output}\n{output}"),
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_honest_different_guard_is_duplicated",
		"registration honest replay-owner family count changed",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let HonestBeacon(",
				"  RegistrationReplayGuard(\n    server_identity,",
				"  RegistrationReplayGuard(server_identity, beacon_prekey, registration_session)\n  |\n  RegistrationReplayGuard(\n    server_identity,",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_honest_different_bundle_is_duplicated",
		"registration honest signed-bundle family count changed",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let HonestBeacon(",
				"  out(\n    c,\n    signed_init_kex(",
				"  out(c, signed_init_kex(tag_ed25519(beacon_prekey), signed_prekey, signed_one_time, signed_pq));\n  out(\n    c,\n    signed_init_kex(",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"registration_server_role_replay_request_uses_prekey",
			"(beacon_identity, core_init, registration_id, replay_reply)",
			"(beacon_prekey, core_init, registration_id, replay_reply)",
			"registration Server public replay request",
		),
		(
			"registration_server_role_replay_request_uses_wire_init",
			"(beacon_identity, core_init, registration_id, replay_reply)",
			"(beacon_identity, incoming_init, registration_id, replay_reply)",
			"registration Server public replay request",
		),
		(
			"registration_server_role_replay_request_uses_root",
			"(beacon_identity, core_init, registration_id, replay_reply)",
			"(beacon_identity, core_init, root, replay_reply)",
			"registration Server public replay request",
		),
		(
			"registration_server_role_accepts_consumed",
			"if replay_result = replay_fresh() then",
			"if replay_result = replay_consumed() then",
			"registration symbolic derive-consume-accept-abort order",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.environment, "let Server(", from, to);
		});
		mutation_count += 1;
	}
	assert_registration_lifecycle_rejected(
		"registration_server_role_root_moves_after_guard",
		"registration symbolic derive-consume-accept-abort order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let Server(",
				"let root = pqxdh_root(",
				"let root_before_guard = pqxdh_root(",
			);
			replace_once_after(
				&mut snapshot.environment,
				"if replay_result = replay_fresh() then",
				"if replay_result = replay_fresh() then",
				"if replay_result = replay_fresh() then\n  let root = pqxdh_root(root_input) in",
			);
		},
	);
	mutation_count += 1;
	assert_registration_lifecycle_rejected(
		"registration_server_role_abort_moves_before_guard",
		"registration symbolic derive-consume-accept-abort order",
		|snapshot| {
			replace_once_after(
				&mut snapshot.environment,
				"let Server(",
				"event ServerResponseAborted(",
				"event ServerResponseAbortedAfterGuard(",
			);
			replace_once_after(
				&mut snapshot.environment,
				"out(\n    replay_requests,",
				"out(\n    replay_requests,",
				"event ServerResponseAborted(\n    server_identity,\n    beacon_identity,\n    core_init,\n    registration_id,\n    root_input,\n    root,\n    registration_session\n  );\n  out(\n    replay_requests,",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"registration_malicious_server_adds_replay_guard",
			"  in(c, registration_control: bitstring);",
			"  RegistrationReplayGuard(server_identity, beacon_identity, registration_session) |\n  in(c, registration_control: bitstring);",
			"registration malicious replay guard",
		),
		(
			"registration_malicious_server_requires_replay_fresh",
			"  in(c, registration_control: bitstring);",
			"  if replay_fresh() = replay_consumed() then\n  in(c, registration_control: bitstring);",
			"registration malicious replay guard",
		),
		(
			"registration_malicious_server_drops_direct_continue",
			"let registration_continue(=registration_id) = registration_control in",
			"let registration_continue(replayed_registration_id) = registration_control in",
			"registration malicious direct response path",
		),
	] {
		assert_registration_lifecycle_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.environment, "let MaliciousServer()", from, to);
		});
		mutation_count += 1;
	}

	for (call_index, label) in [(0usize, "old"), (1usize, "new")] {
		for (argument_index, replacement) in [
			(0usize, "tag_ed25519(MALICIOUS_TASK_SECRET)"),
			(
				1usize,
				"sign(tag_x25519_prekey(MALICIOUS_TASK_SECRET), beacon_identity_secret)",
			),
			(
				2usize,
				"sign(tag_x25519_one_time(MALICIOUS_TASK_SECRET), beacon_identity_secret)",
			),
			(
				3usize,
				"sign(tag_mlkem768(MALICIOUS_TASK_SECRET), beacon_identity_secret)",
			),
		] {
			assert_registration_lifecycle_rejected(
				&format!("registration_hb49_{label}_bundle_argument_{argument_index}"),
				&format!("registration HB-49 {label} bundle"),
				|snapshot| {
					replace_nth_call_argument_after(
						&mut snapshot.mlkem_reencapsulation_control,
						"let KemSameIdentityMultiEpoch()",
						"kem_epoch_bundle",
						call_index,
						argument_index,
						replacement,
					);
				},
			);
			mutation_count += 1;
		}
	}
	for (name, from, to) in [
		(
			"registration_hb49_new_pq_reuses_old_key",
			"let pqpk_new = mlkem_public(pqsk_new) in",
			"let pqpk_new = mlkem_public(pqsk_old) in",
		),
		(
			"registration_hb49_bundle_publication_order_reverses",
			"out(kem_multi_epoch_channel, bundle_old);\n  out(kem_multi_epoch_channel, bundle_new);",
			"out(kem_multi_epoch_channel, bundle_new);\n  out(kem_multi_epoch_channel, bundle_old);",
		),
	] {
		assert_registration_lifecycle_rejected(
			name,
			"registration HB-49 same-classical-material PQ-only rotation fixture",
			|snapshot| {
				replace_once_after(
					&mut snapshot.mlkem_reencapsulation_control,
					"let KemSameIdentityMultiEpoch()",
					from,
					to,
				);
			},
		);
		mutation_count += 1;
	}

	assert_eq!(mutation_count, REGISTRATION_LIFECYCLE_MUTATION_COUNT);
}
const INITIAL_RATCHET_MUTATION_COUNT: usize = 223;

#[test]
fn initial_ratchet_mutation_matrix_is_complete_and_rejected() {
	let mut mutation_count = 0usize;
	let facts = parse_facts(INTERFACE)
		.unwrap()
		.into_iter()
		.filter(|fact| fact.starts_with("initial_ratchet."))
		.collect::<Vec<_>>();
	assert_eq!(facts.len(), 71);
	for fact in facts {
		let (key, _) = fact.split_once('=').unwrap();
		assert_initial_ratchet_rejected(&format!("initial_ratchet_fact_{key}"), key, |snapshot| {
			mutate_fact(&mut snapshot.interface, key, "mutated")
		});
		mutation_count += 1;
	}
	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_derived_root_output_width_drifts",
			"pub const KEX_KDF_OUT_LEN",
			"pub const KEX_KDF_OUT_LEN: usize = 32usize;",
			"pub const KEX_KDF_OUT_LEN: usize = 31usize;",
			"derived-root output width",
		),
		(
			"initial_ratchet_derived_root_width_link_drifts",
			"const _: () = assert!(KEX_KDF_OUT_LEN",
			"KEX_KDF_OUT_LEN == KDF_STATE_SIZE",
			"KEX_KDF_OUT_LEN == KDF_STATE_SIZE + 1",
			"derived-root width link",
		),
		(
			"initial_ratchet_derived_root_alias_size_drifts",
			"pub type KexDerivedSecret",
			"SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>",
			"SecretArr<31, systems::Pqxdh, roles::DerivedSecret>",
			"derived-root alias",
		),
		(
			"initial_ratchet_derived_root_alias_system_drifts",
			"pub type KexDerivedSecret",
			"SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>",
			"SecretArr<KDF_STATE_SIZE, systems::X25519, roles::DerivedSecret>",
			"derived-root alias",
		),
		(
			"initial_ratchet_derived_root_alias_role_drifts",
			"pub type KexDerivedSecret",
			"SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>",
			"SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::SendChain>",
			"derived-root alias",
		),
		(
			"initial_ratchet_derived_root_accessor_signature_drifts",
			"pub fn as_array",
			"pub fn as_array(&self) -> &[u8; S]",
			"pub fn as_array(&self) -> &[u8]",
			"derived-root accessor signature",
		),
		(
			"initial_ratchet_derived_root_accessor_substitutes_data",
			"pub fn as_array",
			"&self.data",
			"&replacement.data",
			"derived-root accessor body",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_shared, marker, from, to);
		});
		mutation_count += 1;
	}
	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_server_output_return_type_drifts",
			"impl ProviderServer for Server",
			"fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput>",
			"fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<ReplacementOutput>",
			"RegistrationOutput return signature",
		),
		(
			"initial_ratchet_server_output_consumer_borrows_value",
			"impl ProviderServer for Server",
			"reg_out: RegistrationOutput",
			"reg_out: &RegistrationOutput",
			"RegistrationOutput by-value consumer signature",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.adapter_server, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_server_output_drops_root",
			"\tpub(crate) derived_secret: KexDerivedSecret,\n",
			"",
			"RegistrationOutput storage",
		),
		(
			"initial_ratchet_server_output_root_type_substituted",
			"pub(crate) derived_secret: KexDerivedSecret",
			"pub(crate) derived_secret: [u8; 32]",
			"RegistrationOutput storage",
		),
		(
			"initial_ratchet_server_root_uses_control_input",
			"derive_root_key_input(pending.root_key_input_mut())?",
			"derive_root_key_input(control.root_key_input_mut())?",
			"Server derived-root output",
		),
		(
			"initial_ratchet_server_output_substitutes_root",
			"Some(RegistrationOutput {\n\t\t\tderived_secret,",
			"Some(RegistrationOutput {\n\t\t\tderived_secret: replacement_secret,",
			"Server derived-root output",
		),
		(
			"initial_ratchet_server_output_substitutes_pending",
			"control: pending,\n\t\t})",
			"control: replacement_pending,\n\t\t})",
			"Server derived-root output",
		),
		(
			"initial_ratchet_server_response_drops_root_destructure",
			"\t\t\tderived_secret,\n\t\t\tcontrol: pending,\n\t\t} = reg_out;",
			"\t\t\tcontrol: pending,\n\t\t} = reg_out;",
			"RegistrationOutput destructure",
		),
		(
			"initial_ratchet_server_response_substitutes_root_destructure",
			"let RegistrationOutput {\n\t\t\tderived_secret,",
			"let RegistrationOutput {\n\t\t\tderived_secret: replacement_secret,",
			"RegistrationOutput destructure",
		),
		(
			"initial_ratchet_server_start_swaps_role",
			"start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"Server root and candidate handoff",
		),
		(
			"initial_ratchet_server_start_substitutes_candidate",
			"start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_server_candidate_ratchet_kdf(&replacement_candidate, derived_secret.as_array())",
			"Server root and candidate handoff",
		),
		(
			"initial_ratchet_server_start_substitutes_root",
			"start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_server_candidate_ratchet_kdf(&candidate, replacement_secret.as_array())",
			"Server root and candidate handoff",
		),
		(
			"initial_ratchet_server_start_is_duplicated",
			"let pending = start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"let pending = start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array());\n\t\tlet duplicate = start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"Server root and candidate handoff",
		),
		(
			"initial_ratchet_server_finish_uses_different_pending",
			"finish_initial_ratchet_kdf(pending)",
			"finish_initial_ratchet_kdf(replacement_pending)",
			"Server pending completion",
		),
		(
			"initial_ratchet_server_finish_is_duplicated",
			"finish_initial_ratchet_kdf(pending)",
			"finish_initial_ratchet_kdf(pending); finish_initial_ratchet_kdf(pending)",
			"Server pending completion",
		),
		(
			"initial_ratchet_server_finish_is_bypassed",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"RatchetManager::from_kernel(replacement_kernel)",
			"Server pending completion",
		),
		(
			"initial_ratchet_server_kernel_wrapper_is_bypassed",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"finish_initial_ratchet_kdf(pending)",
			"Server kernel wrapper",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_server, from, to);
		});
		mutation_count += 1;
	}
	for (name, marker, insertion, diagnostic) in [
		(
			"initial_ratchet_server_get_root_is_shadowed",
			"let derived_secret = derive_root_key_input(pending.root_key_input_mut())?;",
			"\n\t\tlet derived_secret = replacement_secret;",
			"Server derived-root binding count",
		),
		(
			"initial_ratchet_server_handoff_root_is_shadowed",
			"} = reg_out;",
			"\n\t\tlet derived_secret = replacement_secret;",
			"Server derived root was shadowed",
		),
		(
			"initial_ratchet_server_kdf_pending_is_shadowed",
			"let pending = start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"\n\t\tlet pending = replacement_pending;",
			"Server KDF pending binding count",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			let replacement = format!("{marker}{insertion}");
			replace_once(&mut snapshot.adapter_server, marker, &replacement);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_beacon_root_uses_prepared_input",
			"derive_root_key_input(candidate.root_key_input_mut())?",
			"derive_root_key_input(prepared.root_key_input_mut())?",
			"Beacon candidate-root derivation",
		),
		(
			"initial_ratchet_beacon_start_swaps_role",
			"start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_server_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"Beacon root and candidate handoff",
		),
		(
			"initial_ratchet_beacon_start_substitutes_candidate",
			"start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_beacon_candidate_ratchet_kdf(&replacement_candidate, derived_secret.as_array())",
			"Beacon root and candidate handoff",
		),
		(
			"initial_ratchet_beacon_start_substitutes_root",
			"start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array())",
			"start_beacon_candidate_ratchet_kdf(&candidate, replacement_secret.as_array())",
			"Beacon root and candidate handoff",
		),
		(
			"initial_ratchet_beacon_start_is_duplicated",
			"let pending = start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"let pending = start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array());\n\t\t\tlet duplicate = start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"Beacon root and candidate handoff",
		),
		(
			"initial_ratchet_beacon_finish_uses_different_pending",
			"finish_initial_ratchet_kdf(pending)",
			"finish_initial_ratchet_kdf(replacement_pending)",
			"Beacon pending completion",
		),
		(
			"initial_ratchet_beacon_finish_is_duplicated",
			"finish_initial_ratchet_kdf(pending)",
			"finish_initial_ratchet_kdf(pending); finish_initial_ratchet_kdf(pending)",
			"Beacon pending completion",
		),
		(
			"initial_ratchet_beacon_finish_is_bypassed",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"RatchetManager::from_kernel(replacement_kernel)",
			"Beacon pending completion",
		),
		(
			"initial_ratchet_beacon_kernel_wrapper_is_bypassed",
			"RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending))",
			"finish_initial_ratchet_kdf(pending)",
			"Beacon kernel wrapper",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_beacon, from, to);
		});
		mutation_count += 1;
	}
	for (name, marker, insertion, diagnostic) in [
		(
			"initial_ratchet_beacon_root_is_shadowed",
			"let derived_secret = derive_root_key_input(candidate.root_key_input_mut())?;",
			"\n\t\t\tlet derived_secret = replacement_secret;",
			"Beacon derived-root binding count",
		),
		(
			"initial_ratchet_beacon_kdf_pending_is_shadowed",
			"let pending = start_beacon_candidate_ratchet_kdf(&candidate, derived_secret.as_array());",
			"\n\t\t\tlet pending = replacement_pending;",
			"Beacon KDF pending binding count",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			let replacement = format!("{marker}{insertion}");
			replace_once(&mut snapshot.adapter_beacon, marker, &replacement);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_chain_width_drifts",
			"pub const RATCHET_CHAIN_SIZE: usize = crate::ratchet::RATCHET_CHAIN_SIZE;",
			"pub const RATCHET_CHAIN_SIZE: usize = 31;",
			"root and chain width",
		),
		(
			"initial_ratchet_output_width_expression_drifts",
			"pub const INITIAL_RATCHET_KDF_OUTPUT_SIZE: usize = RATCHET_CHAIN_SIZE * 2;",
			"pub const INITIAL_RATCHET_KDF_OUTPUT_SIZE: usize = RATCHET_CHAIN_SIZE * 3;",
			"output-width expression",
		),
		(
			"initial_ratchet_output_width_assertion_drifts",
			"const _: () = assert!(INITIAL_RATCHET_KDF_OUTPUT_SIZE == 64);",
			"const _: () = assert!(INITIAL_RATCHET_KDF_OUTPUT_SIZE == 76);",
			"output 64-byte assertion",
		),
		(
			"initial_ratchet_beacon_send_offset_drifts",
			"send_offset: RATCHET_CHAIN_SIZE as u8,\n\treceive_offset: 0,",
			"send_offset: 0,\n\treceive_offset: 0,",
			"Beacon role offsets",
		),
		(
			"initial_ratchet_beacon_receive_offset_drifts",
			"send_offset: RATCHET_CHAIN_SIZE as u8,\n\treceive_offset: 0,",
			"send_offset: RATCHET_CHAIN_SIZE as u8,\n\treceive_offset: RATCHET_CHAIN_SIZE as u8,",
			"Beacon role offsets",
		),
		(
			"initial_ratchet_server_send_offset_drifts",
			"send_offset: 0,\n\treceive_offset: RATCHET_CHAIN_SIZE as u8,",
			"send_offset: RATCHET_CHAIN_SIZE as u8,\n\treceive_offset: RATCHET_CHAIN_SIZE as u8,",
			"Server role offsets",
		),
		(
			"initial_ratchet_server_receive_offset_drifts",
			"send_offset: 0,\n\treceive_offset: RATCHET_CHAIN_SIZE as u8,",
			"send_offset: 0,\n\treceive_offset: 0,",
			"Server role offsets",
		),
		(
			"initial_ratchet_beacon_candidate_role_swaps",
			"pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tBEACON_RATCHETS\n\t}",
			"pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tSERVER_RATCHETS\n\t}",
			"Beacon candidate role",
		),
		(
			"initial_ratchet_server_candidate_role_swaps",
			"pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tSERVER_RATCHETS\n\t}",
			"pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tBEACON_RATCHETS\n\t}",
			"Server candidate role",
		),
		(
			"initial_ratchet_left_slice_bound_drifts",
			"let left = core::array::from_fn(|i| output[i]);",
			"let left = core::array::from_fn(|i| output[i + 1]);",
			"left 0..32 slice",
		),
		(
			"initial_ratchet_right_slice_duplicates_left",
			"let right = core::array::from_fn(|i| output[i + RATCHET_CHAIN_SIZE]);",
			"let right = core::array::from_fn(|i| output[i]);",
			"right 32..64 slice",
		),
		(
			"initial_ratchet_right_slice_bound_drifts",
			"let right = core::array::from_fn(|i| output[i + RATCHET_CHAIN_SIZE]);",
			"let right = core::array::from_fn(|i| output[i + RATCHET_CHAIN_SIZE - 1]);",
			"right 32..64 slice",
		),
		(
			"initial_ratchet_server_branch_swaps_chain_arguments",
			"send_chain: crate::ratchet::RatchetChain::from_bytes(left),\n\t\t\treceive_chain: crate::ratchet::RatchetChain::from_bytes(right),",
			"send_chain: crate::ratchet::RatchetChain::from_bytes(right),\n\t\t\treceive_chain: crate::ratchet::RatchetChain::from_bytes(left),",
			"role-ordered split",
		),
		(
			"initial_ratchet_beacon_branch_duplicates_left",
			"send_chain: crate::ratchet::RatchetChain::from_bytes(right),\n\t\t\treceive_chain: crate::ratchet::RatchetChain::from_bytes(left),",
			"send_chain: crate::ratchet::RatchetChain::from_bytes(left),\n\t\t\treceive_chain: crate::ratchet::RatchetChain::from_bytes(left),",
			"role-ordered split",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_pqxdh, from, to);
		});
		mutation_count += 1;
	}
	assert_initial_ratchet_rejected(
		"initial_ratchet_candidate_role_methods_swap_together",
		"Beacon candidate role",
		|snapshot| {
			let beacon = "pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tBEACON_RATCHETS\n\t}";
			let server = "pub const fn ratchet_initialization(&self) -> RatchetInitialization {\n\t\tSERVER_RATCHETS\n\t}";
			replace_once(
				&mut snapshot.core_pqxdh,
				beacon,
				"HB64_BEACON_ROLE_SENTINEL",
			);
			replace_once(&mut snapshot.core_pqxdh, server, beacon);
			replace_once(
				&mut snapshot.core_pqxdh,
				"HB64_BEACON_ROLE_SENTINEL",
				server,
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_left_and_right_slices_swap",
		"left 0..32 slice",
		|snapshot| {
			replace_once(
				&mut snapshot.core_pqxdh,
				"let left = core::array::from_fn(|i| output[i]);\n\tlet right = core::array::from_fn(|i| output[i + RATCHET_CHAIN_SIZE]);",
				"let left = core::array::from_fn(|i| output[i + RATCHET_CHAIN_SIZE]);\n\tlet right = core::array::from_fn(|i| output[i]);",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_request_input_width_drifts",
			"pub const RATCHET_CHAIN_SIZE: usize = 32;",
			"pub const RATCHET_CHAIN_SIZE: usize = 31;",
			"request input width",
		),
		(
			"initial_ratchet_request_label_width_drifts",
			"pub const SYM_RATCHET_INFO_SIZE: usize = 41;",
			"pub const SYM_RATCHET_INFO_SIZE: usize = 40;",
			"request label width",
		),
		(
			"initial_ratchet_request_label_drifts",
			"b\"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305\"",
			"b\"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1304\"",
			"request label",
		),
		(
			"initial_ratchet_step_response_width_expression_drifts",
			"crate::commitment::AEAD_KEY_SIZE + RATCHET_CHAIN_SIZE + crate::commitment::AEAD_NONCE_SIZE",
			"crate::commitment::AEAD_KEY_SIZE + RATCHET_CHAIN_SIZE",
			"step-response width expression",
		),
		(
			"initial_ratchet_step_response_width_assertion_drifts",
			"const _: () = assert!(RATCHET_KDF_OUTPUT_SIZE == 76);",
			"const _: () = assert!(RATCHET_KDF_OUTPUT_SIZE == 64);",
			"distinct 76-byte step response",
		),
		(
			"initial_ratchet_step_response_type_uses_initial_width",
			"bytes: [u8; RATCHET_KDF_OUTPUT_SIZE],",
			"bytes: [u8; pqxdh::INITIAL_RATCHET_KDF_OUTPUT_SIZE],",
			"distinct step-response type",
		),
		(
			"initial_ratchet_request_uses_other_label",
			"info: *SYM_RATCHET_INFO,",
			"info: *PQXDH_INFO,",
			"fixed-domain request construction",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_ratchet, from, to);
		});
		mutation_count += 1;
	}
	for (name, from, to) in [
		(
			"initial_ratchet_request_input_field_type_drifts",
			"input: [u8; RATCHET_CHAIN_SIZE]",
			"input: [u8; 31]",
		),
		(
			"initial_ratchet_request_info_field_type_drifts",
			"info: [u8; SYM_RATCHET_INFO_SIZE]",
			"info: [u8; 40]",
		),
	] {
		assert_initial_ratchet_rejected(name, "request field types", |snapshot| {
			replace_once_after(
				&mut snapshot.core_ratchet,
				"pub struct SymmetricRatchetKdfRequest",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_request_input_accessor_substituted",
			"pub const fn input",
			"&self.input",
			"&replacement.input",
			"request input accessor",
		),
		(
			"initial_ratchet_request_info_accessor_substituted",
			"pub const fn info",
			"&self.info",
			"&replacement.info",
			"request info accessor",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.core_ratchet, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_pending_derives_clone",
			"pub struct InitialRatchetKdfPending {",
			"#[derive(Clone)]\npub struct InitialRatchetKdfPending {",
			"pending Clone/Copy derivation",
		),
		(
			"initial_ratchet_pending_derives_copy",
			"pub struct InitialRatchetKdfPending {",
			"#[derive(Copy)]\npub struct InitialRatchetKdfPending {",
			"pending Clone/Copy derivation",
		),
		(
			"initial_ratchet_pending_drops_request",
			"\trequest: SymmetricRatchetKdfRequest,\n",
			"",
			"pending fields",
		),
		(
			"initial_ratchet_pending_drops_initialization",
			"\tinitialization: RatchetInitialization,\n",
			"",
			"pending fields",
		),
		(
			"initial_ratchet_response_confuses_76_byte_step_type",
			"bytes: [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE],",
			"bytes: [u8; crate::ratchet::RATCHET_KDF_OUTPUT_SIZE],",
			"distinct 64-byte response type",
		),
		(
			"initial_ratchet_response_claims_pending_provenance",
			"pub struct InitialRatchetKdfResponse {\n\tbytes:",
			"pub struct InitialRatchetKdfResponse {\n\tpending: InitialRatchetKdfPending,\n\tbytes:",
			"falsely gains type-level provenance",
		),
		(
			"initial_ratchet_start_substitutes_root",
			"request: SymmetricRatchetKdfRequest::new(*root),",
			"request: SymmetricRatchetKdfRequest::new([0; RATCHET_CHAIN_SIZE]),",
			"exact root request and initialization",
		),
		(
			"initial_ratchet_start_substitutes_plan",
			"\t\tinitialization,\n\t}",
			"\t\tinitialization: SERVER_RATCHETS,\n\t}",
			"exact root request and initialization",
		),
		(
			"initial_ratchet_direct_beacon_start_swaps_role",
			"start_initial_ratchet_kdf(root, BEACON_RATCHETS)",
			"start_initial_ratchet_kdf(root, SERVER_RATCHETS)",
			"direct Beacon role start",
		),
		(
			"initial_ratchet_direct_server_start_swaps_role",
			"start_initial_ratchet_kdf(root, SERVER_RATCHETS)",
			"start_initial_ratchet_kdf(root, BEACON_RATCHETS)",
			"direct Server role start",
		),
		(
			"initial_ratchet_resume_substitutes_response_bytes",
			"split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization)",
			"split_initial_ratchet_kdf_output(replacement_response.as_bytes(), pending.initialization)",
			"response split with same pending plan",
		),
		(
			"initial_ratchet_resume_substitutes_pending_plan",
			"split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization)",
			"split_initial_ratchet_kdf_output(response.as_bytes(), replacement_pending.initialization)",
			"response split with same pending plan",
		),
		(
			"initial_ratchet_resume_is_duplicated",
			"let chains = split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization);",
			"let chains = split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization);\n\tlet duplicate = split_initial_ratchet_kdf_output(response.as_bytes(), pending.initialization);",
			"response split with same pending plan",
		),
		(
			"initial_ratchet_kernel_arguments_swap",
			"ConcreteRatchetKernel::new(send_chain, receive_chain)",
			"ConcreteRatchetKernel::new(receive_chain, send_chain)",
			"kernel chain order",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.core_pqxdh_concrete, from, to);
		});
		mutation_count += 1;
	}
	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_pending_request_accessor_substituted",
			"impl InitialRatchetKdfPending",
			"&self.request",
			"&replacement.request",
			"pending request accessor",
		),
		(
			"initial_ratchet_response_bytes_accessor_substituted",
			"impl InitialRatchetKdfResponse",
			"&self.bytes",
			"&replacement.bytes",
			"response bytes accessor",
		),
		(
			"initial_ratchet_response_constructor_substitutes_bytes",
			"impl InitialRatchetKdfResponse",
			"Self { bytes }",
			"Self { bytes: replacement }",
			"response byte constructor",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.core_pqxdh_concrete, marker, from, to);
		});
		mutation_count += 1;
	}
	for (name, marker, replacement, diagnostic) in [
		(
			"initial_ratchet_beacon_candidate_start_bypasses_candidate",
			"pub fn start_beacon_candidate_ratchet_kdf",
			"start_initial_ratchet_kdf(root, BEACON_RATCHETS)",
			"Beacon candidate role start",
		),
		(
			"initial_ratchet_server_candidate_start_bypasses_candidate",
			"pub fn start_server_candidate_ratchet_kdf",
			"start_initial_ratchet_kdf(root, SERVER_RATCHETS)",
			"Server candidate role start",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.core_pqxdh_concrete,
				marker,
				"start_initial_ratchet_kdf(root, candidate.ratchet_initialization())",
				replacement,
			);
		});
		mutation_count += 1;
	}
	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_base_start_root_signature_drifts",
			"pub fn start_initial_ratchet_kdf",
			"root: &[u8; RATCHET_CHAIN_SIZE]",
			"root: &[u8; 31]",
			"typed base start signature",
		),
		(
			"initial_ratchet_beacon_candidate_signature_swaps_type",
			"pub fn start_beacon_candidate_ratchet_kdf",
			"candidate: &BeaconRegistrationCandidate",
			"candidate: &ServerRegistrationCandidate",
			"typed Beacon candidate start signature",
		),
		(
			"initial_ratchet_server_candidate_signature_swaps_type",
			"pub fn start_server_candidate_ratchet_kdf",
			"candidate: &ServerRegistrationCandidate",
			"candidate: &BeaconRegistrationCandidate",
			"typed Server candidate start signature",
		),
		(
			"initial_ratchet_candidate_start_root_signature_drifts",
			"pub fn start_beacon_candidate_ratchet_kdf",
			"root: &[u8; RATCHET_CHAIN_SIZE]",
			"root: &[u8; 31]",
			"typed Beacon candidate start signature",
		),
		(
			"initial_ratchet_server_candidate_start_root_signature_drifts",
			"pub fn start_server_candidate_ratchet_kdf",
			"root: &[u8; RATCHET_CHAIN_SIZE]",
			"root: &[u8; 31]",
			"typed Server candidate start signature",
		),
		(
			"initial_ratchet_base_start_return_type_drifts",
			"pub fn start_initial_ratchet_kdf",
			") -> InitialRatchetKdfPending {",
			") -> ReplacementPending {",
			"typed base start signature",
		),
		(
			"initial_ratchet_beacon_candidate_start_return_type_drifts",
			"pub fn start_beacon_candidate_ratchet_kdf",
			") -> InitialRatchetKdfPending {",
			") -> ReplacementPending {",
			"typed Beacon candidate start signature",
		),
		(
			"initial_ratchet_server_candidate_start_return_type_drifts",
			"pub fn start_server_candidate_ratchet_kdf",
			") -> InitialRatchetKdfPending {",
			") -> ReplacementPending {",
			"typed Server candidate start signature",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.core_pqxdh_concrete, marker, from, to);
		});
		mutation_count += 1;
	}
	for (name, from, to) in [
		(
			"initial_ratchet_kernel_initial_sequence_is_nonzero",
			"Self::from_counters(0, 0, send_chain, receive_chain)",
			"Self::from_counters(1, 0, send_chain, receive_chain)",
		),
		(
			"initial_ratchet_kernel_initial_chains_swap",
			"Self::from_counters(0, 0, send_chain, receive_chain)",
			"Self::from_counters(0, 0, receive_chain, send_chain)",
		),
	] {
		assert_initial_ratchet_rejected(name, "zero-counter kernel initialization", |snapshot| {
			replace_once(&mut snapshot.core_ratchet_concrete, from, to);
		});
		mutation_count += 1;
	}

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_adapter_hkdf_uses_different_pending",
			"initial_ratchet_hkdf(pending.request())",
			"initial_ratchet_hkdf(replacement_pending.request())",
			"adapter exact pending request",
		),
		(
			"initial_ratchet_adapter_hkdf_is_duplicated",
			"initial_ratchet_hkdf(pending.request())",
			"initial_ratchet_hkdf(pending.request()); initial_ratchet_hkdf(pending.request())",
			"adapter exact pending request",
		),
		(
			"initial_ratchet_adapter_hkdf_is_bypassed",
			"initial_ratchet_hkdf(pending.request())",
			"[0; INITIAL_RATCHET_KDF_OUTPUT_SIZE]",
			"adapter exact pending request",
		),
		(
			"initial_ratchet_adapter_response_confuses_step_type",
			"beaconcrypt_core::pqxdh::InitialRatchetKdfResponse::from_bytes",
			"verified_ratchet::RatchetKdfResponse::from_bytes",
			"adapter exact response bytes",
		),
		(
			"initial_ratchet_adapter_response_bytes_substituted",
			"initial_ratchet_hkdf(pending.request())",
			"replacement_bytes",
			"adapter exact pending request",
		),
		(
			"initial_ratchet_adapter_resume_uses_different_pending",
			"resume_initial_ratchet_kdf(pending, response)",
			"resume_initial_ratchet_kdf(replacement_pending, response)",
			"adapter same pending response resume",
		),
		(
			"initial_ratchet_adapter_resume_uses_different_response",
			"resume_initial_ratchet_kdf(pending, response)",
			"resume_initial_ratchet_kdf(pending, replacement_response)",
			"adapter same pending response resume",
		),
		(
			"initial_ratchet_adapter_resume_is_duplicated",
			"resume_initial_ratchet_kdf(pending, response)",
			"resume_initial_ratchet_kdf(pending, response); resume_initial_ratchet_kdf(pending, response)",
			"adapter same pending response resume",
		),
		(
			"initial_ratchet_adapter_resume_is_bypassed",
			"beaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(pending, response)",
			"replacement_kernel",
			"adapter same pending response resume",
		),
		(
			"initial_ratchet_adapter_step_response_uses_initial_type",
			"verified_ratchet::RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))",
			"beaconcrypt_core::pqxdh::InitialRatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))",
			"distinct 76-byte adapter response",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.adapter_ratchet, from, to);
		});
		mutation_count += 1;
	}
	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_adapter_executor_substitutes_input",
			"request.input()",
			"replacement.input()",
			"adapter executor input",
		),
		(
			"initial_ratchet_adapter_executor_substitutes_label",
			"request.info()",
			"replacement.info()",
			"adapter executor label",
		),
		(
			"initial_ratchet_adapter_executor_substitutes_output_bytes",
			"output.copy_from_slice(&expanded);",
			"output.copy_from_slice(&replacement);",
			"adapter executor output",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"fn symmetric_ratchet_hkdf",
				from,
				to,
			);
		});
		mutation_count += 1;
	}
	assert_initial_ratchet_rejected(
		"initial_ratchet_adapter_initial_executor_uses_step_wrapper",
		"adapter HKDF executor",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn initial_ratchet_hkdf",
				"symmetric_ratchet_hkdf(request)",
				"ratchet_hkdf(request)",
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_adapter_initial_hkdf_uses_76_byte_width",
		"adapter 64-byte HKDF signature",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn initial_ratchet_hkdf",
				"[u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE]",
				"[u8; RATCHET_KDF_OUTPUT_SIZE]",
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_adapter_response_is_shadowed",
		"adapter response binding count",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn finish_initial_ratchet_kdf",
				");\n\tbeaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(pending, response)",
				");\n\tlet response = replacement_response;\n\tbeaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(pending, response)",
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_adapter_pending_parameter_is_shadowed",
		"adapter pending parameter was shadowed",
		|snapshot| {
			replace_once_after(
				&mut snapshot.adapter_ratchet,
				"pub(crate) fn finish_initial_ratchet_kdf",
				") -> verified_ratchet::ConcreteRatchetKernel {",
				") -> verified_ratchet::ConcreteRatchetKernel {\n\tlet pending = replacement_pending;",
			);
		},
	);
	mutation_count += 1;

	for (name, from, to, diagnostic) in [
		(
			"initial_ratchet_lean_start_root_substituted",
			"request := { input := root, info := ratchet.SYM_RATCHET_INFO },",
			"request := { input := replacement, info := ratchet.SYM_RATCHET_INFO },",
			"Lean exact request interpretation",
		),
		(
			"initial_ratchet_lean_request_accessor_substituted",
			"ok pending.request := by",
			"ok replacement.request := by",
			"Lean exact request accessor",
		),
		(
			"initial_ratchet_lean_beacon_offsets_swap",
			"initialization := { send_offset := 32#u8, receive_offset := 0#u8 }",
			"initialization := { send_offset := 0#u8, receive_offset := 32#u8 }",
			"Lean Beacon offsets",
		),
		(
			"initial_ratchet_lean_server_offsets_swap",
			"initialization := { send_offset := 0#u8, receive_offset := 32#u8 }",
			"initialization := { send_offset := 32#u8, receive_offset := 0#u8 }",
			"Lean Server offsets",
		),
		(
			"initial_ratchet_lean_resume_response_substituted",
			"split_initial_ratchet_kdf_output response.bytes pending.initialization",
			"split_initial_ratchet_kdf_output replacement.bytes pending.initialization",
			"Lean response partition",
		),
		(
			"initial_ratchet_lean_resume_plan_substituted",
			"split_initial_ratchet_kdf_output response.bytes pending.initialization",
			"split_initial_ratchet_kdf_output response.bytes replacement.initialization",
			"Lean response partition",
		),
		(
			"initial_ratchet_lean_kernel_arguments_swap",
			"ConcreteRatchetKernel.new chains.send_chain chains.receive_chain",
			"ConcreteRatchetKernel.new chains.receive_chain chains.send_chain",
			"Lean kernel chain order",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once(&mut snapshot.lean_ratchet_effect, from, to);
		});
		mutation_count += 1;
	}
	assert_initial_ratchet_rejected(
		"initial_ratchet_lean_ideal_left_slice_drifts",
		"Lean ideal root-chain split anchor",
		|snapshot| {
			replace_once(
				&mut snapshot.lean_pqxdh_kdf,
				"(c.hkdf ds INFO_R 64).take 32",
				"(c.hkdf ds INFO_R 64).take 31",
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_lean_ideal_right_slice_drifts",
		"Lean ideal root-chain split anchor",
		|snapshot| {
			replace_once(
				&mut snapshot.lean_pqxdh_kdf,
				"(c.hkdf ds INFO_R 64).drop 32",
				"(c.hkdf ds INFO_R 64).drop 31",
			);
		},
	);
	mutation_count += 1;
	assert_initial_ratchet_rejected(
		"initial_ratchet_lean_ideal_chain_agreement_anchor_renamed",
		"Lean ideal post-record complementarity anchor",
		|snapshot| {
			replace_once(
				&mut snapshot.lean_pqxdh_theorems,
				"theorem chain_agreement :",
				"theorem chain_alignment :",
			);
		},
	);
	mutation_count += 1;

	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_pv_server_definition_swaps_projection",
			"letfun server_to_beacon_chain",
			"hkdf_first_32(",
			"hkdf_second_32(",
			"ProVerif server-to-beacon definition",
		),
		(
			"initial_ratchet_pv_server_definition_substitutes_root",
			"letfun server_to_beacon_chain",
			"hkdf_sha512_no_salt(root, symmetric_ratchet_domain())",
			"hkdf_sha512_no_salt(replacement_root, symmetric_ratchet_domain())",
			"ProVerif server-to-beacon definition",
		),
		(
			"initial_ratchet_pv_server_definition_substitutes_label",
			"letfun server_to_beacon_chain",
			"symmetric_ratchet_domain()",
			"pqxdh_domain()",
			"ProVerif server-to-beacon definition",
		),
		(
			"initial_ratchet_pv_beacon_definition_swaps_projection",
			"letfun beacon_to_server_chain",
			"hkdf_second_32(",
			"hkdf_first_32(",
			"ProVerif beacon-to-server definition",
		),
		(
			"initial_ratchet_pv_beacon_definition_substitutes_root",
			"letfun beacon_to_server_chain",
			"hkdf_sha512_no_salt(root, symmetric_ratchet_domain())",
			"hkdf_sha512_no_salt(replacement_root, symmetric_ratchet_domain())",
			"ProVerif beacon-to-server definition",
		),
		(
			"initial_ratchet_pv_beacon_definition_substitutes_label",
			"letfun beacon_to_server_chain",
			"symmetric_ratchet_domain()",
			"pqxdh_domain()",
			"ProVerif beacon-to-server definition",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.crypto, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_pv_honest_beacon_root_constructor_drifts",
			"let HonestBeacon(",
			"let root = pqxdh_root(\n      beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n    ) in",
			"let root = replacement_root(\n      beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n    ) in",
			"HonestBeacon exact root derivation",
		),
		(
			"initial_ratchet_pv_honest_beacon_root_input_drifts",
			"let HonestBeacon(",
			"let root = pqxdh_root(\n      beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n    ) in",
			"let root = pqxdh_root(\n      beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(replacement_input)\n    ) in",
			"HonestBeacon exact root derivation",
		),
		(
			"initial_ratchet_pv_server_root_constructor_drifts",
			"let Server(",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"let root = replacement_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"Server exact root derivation",
		),
		(
			"initial_ratchet_pv_server_root_input_drifts",
			"let Server(",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(replacement_input)\n  ) in",
			"Server exact root derivation",
		),
		(
			"initial_ratchet_pv_malicious_server_root_constructor_drifts",
			"let MaliciousServer()",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"let root = replacement_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"MaliciousServer exact root derivation",
		),
		(
			"initial_ratchet_pv_malicious_server_root_input_drifts",
			"let MaliciousServer()",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(root_input)\n  ) in",
			"let root = pqxdh_root(\n    beaconcrypt_core__pqxdh__t_RootKeyInput_to_bitstring(replacement_input)\n  ) in",
			"MaliciousServer exact root derivation",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.environment, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_pv_honest_beacon_initial_open_swaps_chain",
			"let HonestBeacon(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"let server_chain_1 = beacon_to_server_chain(root) in",
			"HonestBeacon scoped chain occurrence count",
		),
		(
			"initial_ratchet_pv_honest_beacon_initial_open_substitutes_root",
			"let HonestBeacon(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"let server_chain_1 = server_to_beacon_chain(replacement_root) in",
			"HonestBeacon initial-open chain",
		),
		(
			"initial_ratchet_pv_honest_beacon_outgoing_swaps_chain",
			"let HonestBeacon(",
			"let beacon_send_chain_1 = beacon_to_server_chain(root) in",
			"let beacon_send_chain_1 = server_to_beacon_chain(root) in",
			"HonestBeacon scoped chain occurrence count",
		),
		(
			"initial_ratchet_pv_honest_beacon_outgoing_substitutes_root",
			"let HonestBeacon(",
			"let beacon_send_chain_1 = beacon_to_server_chain(root) in",
			"let beacon_send_chain_1 = beacon_to_server_chain(replacement_root) in",
			"HonestBeacon outgoing chain",
		),
		(
			"initial_ratchet_pv_server_initial_seal_swaps_chain",
			"let Server(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"let server_chain_1 = beacon_to_server_chain(root) in",
			"Server scoped chain occurrence count",
		),
		(
			"initial_ratchet_pv_server_initial_seal_substitutes_root",
			"let Server(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"let server_chain_1 = server_to_beacon_chain(replacement_root) in",
			"Server initial-seal chain",
		),
		(
			"initial_ratchet_pv_server_initial_open_swaps_chain",
			"let Server(",
			"ratchet_material(beacon_to_server_chain(root))",
			"ratchet_material(server_to_beacon_chain(root))",
			"Server scoped chain occurrence count",
		),
		(
			"initial_ratchet_pv_server_initial_open_substitutes_root",
			"let Server(",
			"ratchet_material(beacon_to_server_chain(root))",
			"ratchet_material(beacon_to_server_chain(replacement_root))",
			"Server incoming chain",
		),
		(
			"initial_ratchet_pv_malicious_server_initial_seal_swaps_chain",
			"let MaliciousServer()",
			"ratchet_material(server_to_beacon_chain(root))",
			"ratchet_material(beacon_to_server_chain(root))",
			"MaliciousServer scoped chain occurrence count",
		),
		(
			"initial_ratchet_pv_malicious_server_initial_seal_substitutes_root",
			"let MaliciousServer()",
			"ratchet_material(server_to_beacon_chain(root))",
			"ratchet_material(server_to_beacon_chain(replacement_root))",
			"MaliciousServer initial-seal chain",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.environment, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, from, to, diagnostic) in [
		(
			"initial_ratchet_pv_honest_beacon_initial_material_uses_wrong_chain",
			"let HonestBeacon(",
			"let server_material_1 = ratchet_material(server_chain_1) in",
			"let server_material_1 = ratchet_material(beacon_send_chain_1) in",
			"HonestBeacon chain-to-open material",
		),
		(
			"initial_ratchet_pv_honest_beacon_initial_material_is_shadowed",
			"let HonestBeacon(",
			"let server_material_1 = ratchet_material(server_chain_1) in",
			"let server_material_1 = ratchet_material(server_chain_1) in\n    let server_material_1 = replacement_material in",
			"HonestBeacon binding count",
		),
		(
			"initial_ratchet_pv_honest_beacon_outgoing_material_uses_wrong_chain",
			"let HonestBeacon(",
			"let beacon_material_1 = ratchet_material(beacon_send_chain_1) in",
			"let beacon_material_1 = ratchet_material(server_chain_1) in",
			"HonestBeacon chain-to-seal material",
		),
		(
			"initial_ratchet_pv_honest_beacon_outgoing_material_is_shadowed",
			"let HonestBeacon(",
			"let beacon_material_1 = ratchet_material(beacon_send_chain_1) in",
			"let beacon_material_1 = ratchet_material(beacon_send_chain_1) in\n    let beacon_material_1 = replacement_material in",
			"HonestBeacon binding count",
		),
		(
			"initial_ratchet_pv_server_initial_material_uses_wrong_chain",
			"let Server(",
			"let server_material_1 = ratchet_material(server_chain_1) in",
			"let server_material_1 = ratchet_material(replacement_chain) in",
			"Server initial material",
		),
		(
			"initial_ratchet_pv_server_initial_material_is_shadowed",
			"let Server(",
			"let server_material_1 = ratchet_material(server_chain_1) in",
			"let server_material_1 = ratchet_material(server_chain_1) in\n      let server_material_1 = replacement_material in",
			"Server binding count",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			replace_once_after(&mut snapshot.environment, marker, from, to);
		});
		mutation_count += 1;
	}

	for (name, marker, binding, diagnostic) in [
		(
			"initial_ratchet_pv_honest_beacon_root_is_shadowed",
			"let HonestBeacon(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"HonestBeacon root binding count",
		),
		(
			"initial_ratchet_pv_server_root_is_shadowed",
			"let Server(",
			"let server_chain_1 = server_to_beacon_chain(root) in",
			"Server root binding count",
		),
		(
			"initial_ratchet_pv_malicious_server_root_is_shadowed",
			"let MaliciousServer()",
			"let server_material_1 = ratchet_material(server_to_beacon_chain(root)) in",
			"MaliciousServer root binding count",
		),
	] {
		assert_initial_ratchet_rejected(name, diagnostic, |snapshot| {
			let replacement = format!("let root = replacement_root in\n  {binding}");
			replace_once_after(&mut snapshot.environment, marker, binding, &replacement);
		});
		mutation_count += 1;
	}

	assert_eq!(mutation_count, INITIAL_RATCHET_MUTATION_COUNT);
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

#[test]
fn main_registration_completion_schedules_preserve_the_checked_prefixes() {
	let environment = compact(&uncommented_pv(ENVIRONMENT_MODEL).unwrap());
	let baseline =
		compact(&uncommented_pv(include_str!("../proofs/pro-verif/baseline.pv")).unwrap());
	for role in [
		"!HonestBeacon(BEACON_RECORD_SECRET)",
		"!MainLaterBeacon(BEACON_RECORD_SECRET)",
		"!MainLaterServer(INITIAL_SECRET,CACHED_SECRET,ADVANCE_SECRET,FUTURE_SECRET)",
		"!Server(INITIAL_SECRET,CACHED_SECRET,ADVANCE_SECRET,FUTURE_SECRET)",
	] {
		require_once(&baseline, role, "live main registration role").unwrap();
	}
	let server = section_between(
		&environment,
		"letServer(",
		"letMaliciousServer(",
		"first server",
	)
	.unwrap();
	let later_server = environment.split_once("letMainLaterServer(").unwrap().1;
	let later_server = format!("letServer({later_server}").replace("main_", "");
	assert_eq!(
		server.split_once("letthird_frame=seal_frame(").unwrap().0,
		later_server
			.split_once("in(c,completion_kind:bitstring);")
			.unwrap()
			.0,
		"later server must retain the entire checked authentication, replay, root, response and first-two-record prefix"
	);
	assert_eq!(
		server.split_once("out(c,third_frame);").unwrap().1,
		later_server.split_once("out(c,third_frame);").unwrap().1,
		"later server must retain the checked suffix after its alternative third payload"
	);
	let beacon = section_between(
		&environment,
		"letHonestBeacon(",
		"letMaliciousBeacon(",
		"first beacon",
	)
	.unwrap();
	let later_beacon = section_between(
		&environment,
		"letMainLaterBeacon(",
		"letMainLaterServer(",
		"later beacon",
	)
	.unwrap()
	.replace("MainLaterBeacon", "HonestBeacon")
	.replace("main_", "");
	assert_eq!(
		beacon.split_once("letserver_material_1=").unwrap().0,
		later_beacon.split_once("letserver_chain_2=").unwrap().0,
		"later beacon must retain the checked single-use lifecycle, response parsing, root and associated-data derivation prefix"
	);
	require_ordered(&later_beacon, &[
		"letserver_chain_2=ratchet_next(server_chain_1)in",
		"letserver_chain_3=ratchet_next(server_chain_2)in",
		"letserver_material_3=ratchet_material(server_chain_3)in",
		"letopened_initial=open_frame(server_material_3,associated_data,next_sequence(next_sequence(first_sequence())),SERVER_KEY_ID,initial_frame)in",
		"letregistration_payload(=expected_binding,initial_plaintext)=opened_initialin",
		"eventBeaconRegistrationCompleted(establishment_session(beacon_establishment),next_sequence(next_sequence(first_sequence())),opened_initial,initial_frame,response,assigned_key_id);",
		"eventMessageKeyCached(session,beacon_role(),server_to_beacon(),first_sequence(),server_material_1);",
		"eventMessageKeyCached(session,beacon_role(),server_to_beacon(),next_sequence(first_sequence()),server_material_2);",
		"eventMessageKeyUnavailable(session,beacon_role(),server_to_beacon(),next_sequence(next_sequence(first_sequence())),server_material_3);",
	], "later completion authentication and state ordering").unwrap();
	assert_eq!(count(&later_beacon, "open_frame("), 1);
	let queries =
		compact(&uncommented_pv(include_str!("../proofs/pro-verif/queries.pvl")).unwrap());
	for conclusion in [
		"inj-event(ServerRegistrationSessionCommitted(main_agreement,main_server_assigned))",
		"inj-event(RegistrationRecordSent(main_agreement,main_sequence,main_payload,main_frame,main_server_assigned))",
	] {
		require_once(&queries, conclusion, "general completion origin").unwrap();
	}
	let controls = compact(
		&uncommented_pv(include_str!(
			"../proofs/pro-verif/main-registration-control-queries.pvl"
		))
		.unwrap(),
	);
	assert_eq!(count(&controls, "query"), 8);
	require_once(
		&controls,
		"inj-event(BeaconAnyCommitted(main_transcript))==>inj-event(ServerCommitted(main_transcript))",
		"unqualified exact-response negative control",
	)
	.unwrap();
	require_once(
		&controls,
		"event(MainRegistrationRelabelCompleted(main_agreement,main_payload,main_frame,main_response))",
		"reachable relabel control",
	)
	.unwrap();
}
