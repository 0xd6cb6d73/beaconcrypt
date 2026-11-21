-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAd
import BeaconcryptCore.Refinement.PqxdhSurface
import BeaconcryptCore.Computational.RegistrationAuthenticationShared
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! Two actual owned AD phases with the same retained Init buffers and response fields query the same public preimage. Receipts in one reached hash cache therefore give the same digest and complete session AD. The hypotheses are exact reached source receipts; this module supplies neither a fabricated AD digest nor a new hash-injectivity premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationAdHashAgreement
open BeaconcryptCore.Refinement
open RegistrationAd
open SessionBinding

/-- Matching actual preimages have one literal value in the common reached hash cache. -/
theorem reached_digest (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (fields : server.binding.init_fields = beacon.pending.binding.init_fields)
    (responseFields : serverView server.candidate = responseView beacon.packet.public)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public))
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), absBytes beacon.input) = some beaconDigest) :
    serverDigest = beaconDigest := by
  have same := matching_role_preimages server beacon fields responseFields serverInput beaconInput
  rw [same] at serverCached
  exact Option.some.inj (serverCached.symm.trans beaconCached)

/-- Equal reached request digests bind every raw attached Init buffer outside the actual common-cache collision event. -/
theorem init_fields_from_cache (cache : CtxRomAuth.CtxRO.QueryCache)
    (state : registration.BeaconInitState) (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) (digest : CtxRomAuth.CtxDigest)
    (sourceCached : cache ((), (RegistrationNativeInitStageContents.sourcePayload state).transcript) = some digest)
    (acceptedCached : cache ((), RegistrationAuthentication.initPreimage pin packet) = some digest)
    (collisionFree : ¬ CacheHasCollision cache) :
    RegistrationNativeInitTupleSource.ownedFields state = RegistrationAuthentication.ownedFields packet := by
  have querySame := cache_lookup_eq_of_noCollision collisionFree sourceCached ⟨digest, acceptedCached, HEq.rfl⟩
  have bytes := congrArg Prod.snd querySame
  have fields := RegistrationNativeInitStageContents.native_fields state pin packet
    (congrArg (MldsaTranscriptAuth.Payload.mk .beacon) bytes)
  simp only [RegistrationNativeInitTupleSource.ownedFields, RegistrationAuthentication.ownedFields,
    fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1]

/-- A real completed-binding continuation retains its exact digest and fixed AD context. -/
theorem complete_metadata (pending : session.RegistrationBinding)
    (digest : Std.Array Std.U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (actual : pending.complete digest = .ok completed) :
    completed.session_transcript_hash = digest ∧ registrationConsistent completed := by
  obtain ⟨expected, ran, _pin, _initHash, _identity, digestEq, consistent⟩ := complete_refines pending digest
  have same : expected = completed := RustM.ok.inj (ran.symm.trans actual)
  exact same ▸ ⟨digestEq, consistent⟩

/-- Both actual hash continuations retain equal session hashes and complete AD, before any record opener can infer agreement. -/
theorem resumed_agreement (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (fields : server.binding.init_fields = beacon.pending.binding.init_fields)
    (responseFields : serverView server.candidate = responseView beacon.packet.public)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public))
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), absBytes beacon.input) = some beaconDigest)
    (initial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray beaconDigest)) = .ok (.Ok authenticated)) :
    initial.binding.session_transcript_hash = authenticated.binding.session_transcript_hash ∧
      initial.binding.associated_data = authenticated.binding.associated_data := by
  have digestSame := reached_digest cache server beacon fields responseFields serverInput beaconInput
    serverDigest beaconDigest serverCached beaconCached
  subst beaconDigest
  obtain ⟨serverBinding, completedAt, initialBinding, _consistent, _candidate⟩ :=
    server_ad_resume_binding server (RegistrationAuthenticationShared.digestArray serverDigest) initial serverResumed
  have serverMetadata := complete_metadata server.binding _ serverBinding completedAt
  obtain ⟨expected, ran, _control, _packet, beaconHash, beaconConsistent⟩ :=
    beacon_digest_completes_binding beacon (RegistrationAuthenticationShared.digestArray serverDigest)
  have same : expected = authenticated := core.result.Result.Ok.inj (RustM.ok.inj (ran.symm.trans beaconResumed))
  subst expected
  have serverHash : initial.binding.session_transcript_hash = RegistrationAuthenticationShared.digestArray serverDigest :=
    initialBinding ▸ serverMetadata.1
  have hashSame := serverHash.trans beaconHash.symm
  refine ⟨hashSame, ?_⟩
  apply PqxdhSurface.bytes_eq_of_abs_eq
  have serverConsistent : registrationConsistent initial.binding := initialBinding ▸ serverMetadata.2
  change absBytes initial.binding.associated_data = boundAssociatedData (absBytes initial.binding.session_transcript_hash) at serverConsistent
  change absBytes authenticated.binding.associated_data = boundAssociatedData (absBytes authenticated.binding.session_transcript_hash) at beaconConsistent
  exact serverConsistent.trans ((congrArg (fun digest => boundAssociatedData (absBytes digest)) hashSame).trans beaconConsistent.symm)

/-- Actual successful role cuts with matching full public fields complete the same AD before any record-opening argument. -/
theorem accepted_response_agreement (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket)
    (fields : server.binding.init_fields = pending.binding.init_fields)
    (responseFields : serverView server.candidate = responseView packet.public)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), RegistrationResponseExecutor.adPayload pending packet) = some beaconDigest)
    (initial : registration.ServerInitialKdf)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial)) :
    initial.binding.session_transcript_hash =
        (RegistrationResponseExecutor.acceptedResponse pending packet beaconDigest).binding.session_transcript_hash ∧
      initial.binding.associated_data =
        (RegistrationResponseExecutor.acceptedResponse pending packet beaconDigest).binding.associated_data := by
  obtain ⟨input, _built, inputBytes⟩ := pending_transcript_exact pending.binding (responseView packet.public)
  let beacon : registration.BeaconAdHash := ⟨pending, packet, input⟩
  have beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public) := inputBytes
  have beaconAt : cache ((), absBytes beacon.input) = some beaconDigest := by
    rw [beaconInput]
    exact beaconCached
  exact resumed_agreement cache server beacon fields responseFields serverInput beaconInput
    serverDigest beaconDigest serverCached beaconAt initial
    (RegistrationResponseExecutor.acceptedResponse pending packet beaconDigest) serverResumed
      (RegistrationResponseExecutor.ad_accept_exact beacon beaconDigest)

end BeaconcryptCore.Computational.RegistrationAdHashAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashAgreement.reached_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashAgreement.reached_digest

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashAgreement.complete_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashAgreement.complete_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashAgreement.resumed_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashAgreement.resumed_agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashAgreement.init_fields_from_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashAgreement.init_fields_from_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashAgreement.accepted_response_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashAgreement.accepted_response_agreement
