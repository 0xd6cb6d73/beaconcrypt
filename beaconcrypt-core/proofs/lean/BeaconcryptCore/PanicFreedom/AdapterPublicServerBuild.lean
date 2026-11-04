-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterCallers
import BeaconcryptCore.PanicFreedom.PeerOwnership
import BeaconcryptCore.PanicFreedom.RegistrationPublication
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.PanicFreedom.Trivial
import BeaconcryptCore.PanicFreedom.AdapterStandard

/-! Native response construction admits allocator and primitive refusals as normal returns. Container contracts separately specify preservation of every populated remote slot through reservation and the two mutable entry lenses. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace BeaconcryptCore.PanicFreedom.AdapterPublicServerBuild
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [wire : AdapterWirePrimitive.Operations] [writer : RegistrationWriterPrimitive.Operations]
attribute [local irreducible] beaconcrypt_registration_writer.wire.encode_response

abbrev Remote := shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey
abbrev PeerMap := hashbrown.map.HashMap U64 Remote collections.KeyedHasher hashbrown.alloc.inner.Global
abbrev Entry := hashbrown.map.Entry U64 Remote collections.KeyedHasher hashbrown.alloc.inner.Global
abbrev Vacant := hashbrown.map.VacantEntry U64 Remote collections.KeyedHasher hashbrown.alloc.inner.Global

abbrev mapContains (map : PeerMap) (key : U64) : RustM Bool :=
  hashbrown.map.HashMap.contains_key core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) map key

abbrev mapReserve (map : PeerMap) :=
  hashbrown.map.HashMap.try_reserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator map 1#usize

abbrev mapEntry (map : PeerMap) (key : U64) :=
  hashbrown.map.HashMap.entry core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator map key

abbrev vacantInsert (entry : Vacant) (remote : Remote) :=
  hashbrown.map.VacantEntry.insert hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    core.U64.Insts.CoreHashHash collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13 entry remote

structure Contracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  allocation : AdapterWire.Contracts
  serialization : AdapterRegistrationWriterCallers.ResponseCallerContracts
  parse : ∀ input, Normal (primitive.parse input)
  initial : ∀ request, Normal (localOps.ratchet_initial_ratchet_hkdf request)
  kdf : ∀ request, Normal (recordOps.kdf request)
  commitment : ∀ transcript, Normal (recordOps.hash transcript)
  sealing : ∀ request, Normal (localOps.ratchet_execute_seal_request request)
  writing : ∀ request, Normal (localOps.ratchet_execute_write_request request)
  sign : ∀ identity request, Normal (localOps.auth_MldsaIdentity_sign_requested identity request)
  contains : ∀ map key, Normal (mapContains map key)
  reserve : ∀ map, Normal (mapReserve map)
  entry : ∀ map key, Normal (mapEntry map key)
  insert : ∀ entry remote, Normal (vacantInsert entry remote)

theorem registration_application_bytes_total (input : transport.RegistrationApplication) :
    ∃ result, server.registration_application_bytes input = ok result := by
  cases input <;> exact ⟨_, rfl⟩

theorem build_detached_closure_total
    (capture : server.ProviderServerServer.build_registration_response.closure)
    (input : alloc.vec.Vec U8 × Std.Array U8 16#usize) :
    ∃ result, server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816.call_once capture input = ok result :=
  ⟨_, rfl⟩

theorem registration_response_len_total (application : Usize) (assigned : U64) :
    ∃ result, server.registration_response_len application assigned = ok result :=
  Transport.registration_response_len_total application assigned

theorem build_registration_response_total (contracts : Contracts) (self : server.Server)
    (reg_out : server.RegistrationOutput) (data : core.option.Option (Slice U8)) :
    ∃ result, server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self reg_out data = ok result := by
  unfold server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
  simp only [AdapterOptionDeref.byte_vector, lift,
    beaconcrypt.auth.execute_hash, beaconcrypt.ratchet.ratchet_hkdf,
    beaconcrypt.ratchet.execute_commitment_hash,
    beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
    PublicWrapperPlatform.peerBinding, PublicWrapperPlatform.beaconIdentity,
    core.slice.Slice.len, rust_primitives.slice.slice_length]
  repeat'
    try simp only [uncurry, bind_tc_ok]
    first
      | with_reducible exact AdapterRegistrationWriterCallers.response_native_total contracts.serialization (by assumption)
      | with_reducible apply normal_bind_at
      | with_reducible exact AdapterPublicTrivial.server_authentication_pin_total contracts.publicLeaves _
      | with_reducible exact registration_application_bytes_total _
      | with_reducible exact registration_response_len_total _ _
      | with_reducible exact contracts.parse _
      | with_reducible exact contracts.initial _
      | with_reducible exact contracts.kdf _
      | with_reducible exact contracts.commitment _
      | with_reducible exact contracts.sealing _
      | with_reducible exact contracts.writing _
      | with_reducible exact contracts.sign _ _
      | with_reducible exact contracts.publicLeaves.hash _
      | with_reducible exact contracts.contains _ _
      | with_reducible exact contracts.reserve _
      | with_reducible exact contracts.entry _ _
      | with_reducible exact contracts.insert _ _
      | with_reducible exact AdapterPublicTrivial.established_remote_from_peer_total _ _ _
      | with_reducible exact PeerOwnership.CompletionLookup_request_total _
      | with_reducible exact PeerOwnership.CompletionLookup_resume_total _ _
      | with_reducible exact PeerOwnership.PeerInsert_into_parts_total _
      | with_reducible exact PeerOwnership.PeerInsert_request_total _
      | with_reducible exact PeerOwnership.PublicationFinish_finish_total _ _
      | with_reducible exact PeerOwnership.PublishedPeer_into_parts_total _
      | with_reducible exact PeerOwnership.begin_completion_lookup_total _ _ _ _
      | with_reducible exact PeerOwnership.begin_peer_insert_total _ _
      | with_reducible exact Trivial.pqxdh_concrete_InitialRatchetKdfResponse_from_bytes_total _
      | with_reducible exact RegistrationTrivial.ServerInitialKdf_request_total _
      | with_reducible exact RegistrationPublication.ServerInitialKdf_resume_total _ _
      | with_reducible exact RegistrationPublication.ServerInitialSeal_request_total _
      | with_reducible exact RegistrationPublication.ServerInitialSeal_resume_total _ _
      | with_reducible exact RegistrationPublication.ServerRecordAead_request_total _
      | with_reducible exact RegistrationPublication.ServerRecordAead_resume_total _ _
      | with_reducible exact RegistrationPublication.ServerRecordCommitment_resume_total _ _
      | with_reducible exact RegistrationPublication.ServerRecordCommitment_transcript_mut_total _
      | with_reducible exact RegistrationPublication.ServerRecordWrite_request_total _
      | with_reducible exact RegistrationPublication.ServerRecordWrite_resume_total _ _
      | with_reducible exact RegistrationTrivial.ServerResponseHash_request_total _
      | with_reducible exact RegistrationPublication.ServerResponseHash_resume_total _ _
      | with_reducible exact RegistrationTrivial.ServerResponseReady_message_total _
      | with_reducible exact RegistrationTrivial.ServerResponseReady_publish_total _ _
      | with_reducible exact RegistrationTrivial.ServerResponseSigning_request_total _
      | with_reducible exact RegistrationPublication.ServerResponseSigning_resume_total _ _
      | with_reducible exact Transport.normalize_registration_application_total _
      | with_reducible exact AdapterStandard.result_ok_total _
      | with_reducible exact AdapterStandard.option_branch_total _
      | with_reducible exact AdapterStandard.option_ref_total _
      | with_reducible exact AdapterStandard.option_residual_of_branch _ _ (by assumption)
      | with_reducible exact AdapterStandard.option_map_total _ _ _ (fun input => build_detached_closure_total _ input)
      | with_reducible exact normal_ok _
      | (intro value returned; rcases (show _ × _ × _ from value) with ⟨left, middle, right⟩)
      | (intro value returned; rcases (show _ × _ from value) with ⟨left, right⟩)
      | (intro value returned)
      | (split)

end BeaconcryptCore.PanicFreedom.AdapterPublicServerBuild
