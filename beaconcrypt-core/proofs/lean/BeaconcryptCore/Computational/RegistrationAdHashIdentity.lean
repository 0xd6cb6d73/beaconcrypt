-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAdHashAgreement
import BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity

/-! Current identity recovery uses the two real transcript-hash cache receipts outside the existing collision event. AD151 is opaque apart from its digest suffix: identities are recovered from equal reached2638-byte preimages, never from an identity substring in AD or an unrelated completed binding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationAdHashIdentity
open BeaconcryptCore.Refinement
open RegistrationAd SessionBinding

private theorem completed_digest_of_ad_eq (left right : session.CompletedRegistrationBinding)
    (leftConsistent : registrationConsistent left) (rightConsistent : registrationConsistent right)
    (same : left.associated_data = right.associated_data) :
    left.session_transcript_hash = right.session_transcript_hash := by
  apply PqxdhSurface.bytes_eq_of_abs_eq
  apply Pqxdh.SessionTranscript.associatedData_inj
  exact leftConsistent.symm.trans ((congrArg absBytes same).trans rightConsistent)

/-- Equality of actual completed AD preserves the exact digest consumed by each owned role continuation. -/
theorem resumed_digest_of_ad_eq (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (initial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray beaconDigest)) = .ok (.Ok authenticated))
    (same : initial.binding.associated_data = authenticated.binding.associated_data) :
    serverDigest = beaconDigest := by
  obtain ⟨completed, completedAt, initialBinding, consistent, _candidate⟩ :=
    server_ad_resume_binding server (RegistrationAuthenticationShared.digestArray serverDigest) initial serverResumed
  have serverMetadata := RegistrationAdHashAgreement.complete_metadata server.binding _ completed completedAt
  obtain ⟨expected, ran, _control, _packet, beaconHash, beaconConsistent⟩ :=
    beacon_digest_completes_binding beacon (RegistrationAuthenticationShared.digestArray beaconDigest)
  have acceptedSame : expected = authenticated := core.result.Result.Ok.inj (RustM.ok.inj (ran.symm.trans beaconResumed))
  subst expected
  have hashEq := completed_digest_of_ad_eq initial.binding authenticated.binding (initialBinding ▸ consistent) beaconConsistent same
  have serverHash : initial.binding.session_transcript_hash = RegistrationAuthenticationShared.digestArray serverDigest :=
    initialBinding ▸ serverMetadata.1
  apply List.Vector.toList_injective
  have bytes := congrArg absBytes (serverHash.symm.trans (hashEq.trans beaconHash))
  simpa only [RegistrationAuthenticationShared.digest_array_bytes] using bytes

/-- The already counted common-cache collision exception turns equal actual AD into equal reached transcript inputs. -/
theorem reached_preimage_of_ad_eq (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), absBytes beacon.input) = some beaconDigest)
    (initial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray beaconDigest)) = .ok (.Ok authenticated))
    (same : initial.binding.associated_data = authenticated.binding.associated_data)
    (collisionFree : ¬ CacheHasCollision cache) :
    absBytes server.input = absBytes beacon.input := by
  have digestSame := resumed_digest_of_ad_eq server beacon serverDigest beaconDigest initial authenticated serverResumed beaconResumed same
  subst beaconDigest
  have querySame := cache_lookup_eq_of_noCollision collisionFree serverCached ⟨serverDigest, beaconCached, HEq.rfl⟩
  exact congrArg Prod.snd querySame

private theorem owned_eq_of_abs (left right : authentication.OwnedInitFields)
    (same : SessionTranscriptRefinement.absInit (initView left) = SessionTranscriptRefinement.absInit (initView right)) :
    left = right := by
  have identity : left.identity_key = right.identity_key := PqxdhSurface.bytes_eq_of_abs_eq
    (congrArg Pqxdh.SessionTranscript.InitFields.identityKey same)
  have pre : left.pre_key = right.pre_key := PqxdhSurface.bytes_eq_of_abs_eq
    (congrArg Pqxdh.SessionTranscript.InitFields.preKey same)
  have one : left.one_time_key = right.one_time_key := PqxdhSurface.bytes_eq_of_abs_eq
    (congrArg Pqxdh.SessionTranscript.InitFields.oneTimeKey same)
  have kem : left.pq_key = right.pq_key := PqxdhSurface.bytes_eq_of_abs_eq
    (congrArg Pqxdh.SessionTranscript.InitFields.pqKey same)
  cases left
  cases right
  cases identity
  cases pre
  cases one
  cases kem
  rfl

/-- Fixed framing recovers the complete original signed Init buffers and every response public field from the actual reached preimages. -/
theorem raw_fields_of_ad_eq (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public))
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), absBytes beacon.input) = some beaconDigest)
    (initial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray beaconDigest)) = .ok (.Ok authenticated))
    (same : initial.binding.associated_data = authenticated.binding.associated_data)
    (collisionFree : ¬ CacheHasCollision cache) :
    server.binding.init_fields = beacon.pending.binding.init_fields ∧
      SessionTranscriptRefinement.absResponse (serverView server.candidate) =
        SessionTranscriptRefinement.absResponse (responseView beacon.packet.public) := by
  have inputSame := reached_preimage_of_ad_eq cache server beacon serverDigest beaconDigest serverCached beaconCached
    initial authenticated serverResumed beaconResumed same collisionFree
  rw [serverInput, beaconInput] at inputSame
  have serverInitWidth : (SessionTranscriptRefinement.absInit (initView server.binding.init_fields)).WellFormed := by
    constructor <;> simp [SessionTranscriptRefinement.absInit, initView]
  have beaconInitWidth : (SessionTranscriptRefinement.absInit (initView beacon.pending.binding.init_fields)).WellFormed := by
    constructor <;> simp [SessionTranscriptRefinement.absInit, initView]
  have serverResponseWidth : (SessionTranscriptRefinement.absResponse (serverView server.candidate)).WellFormed := by
    constructor <;> simp [SessionTranscriptRefinement.absResponse, serverView]
  have beaconResponseWidth : (SessionTranscriptRefinement.absResponse (responseView beacon.packet.public)).WellFormed := by
    constructor <;> simp [SessionTranscriptRefinement.absResponse, responseView]
  have fields := Pqxdh.SessionTranscript.encode_inj serverInitWidth beaconInitWidth serverResponseWidth beaconResponseWidth inputSame
  exact ⟨owned_eq_of_abs _ _ fields.1, fields.2⟩

/-- Ordered current identities follow from actual cached transcripts and owned identity extraction, rather than identity bytes inside AD. The Server ML pin is a separate authentication obligation. -/
theorem completed_identities_of_ad_eq (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (beacon : registration.BeaconAdHash)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (beaconInput : absBytes beacon.input = preimage beacon.pending.binding (responseView beacon.packet.public))
    (serverDigest beaconDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (beaconCached : cache ((), absBytes beacon.input) = some beaconDigest)
    (initial : registration.ServerInitialKdf) (authenticated : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray beaconDigest)) = .ok (.Ok authenticated))
    (same : initial.binding.associated_data = authenticated.binding.associated_data)
    (collisionFree : ¬ CacheHasCollision cache) :
    server.candidate.server_identity_public_key = beacon.packet.public.identity_key ∧
      initial.binding.beacon_identity_public_key = authenticated.binding.beacon_identity_public_key := by
  obtain ⟨fields, response⟩ := raw_fields_of_ad_eq cache server beacon serverInput beaconInput
    serverDigest beaconDigest serverCached beaconCached initial authenticated serverResumed beaconResumed same collisionFree
  have serverIdentity : server.candidate.server_identity_public_key = beacon.packet.public.identity_key :=
    PqxdhSurface.bytes_eq_of_abs_eq (congrArg Pqxdh.SessionTranscript.ResponseFields.identityKey response)
  obtain ⟨completed, completedAt, initialBinding, _consistent, _candidate⟩ :=
    server_ad_resume_binding server (RegistrationAuthenticationShared.digestArray serverDigest) initial serverResumed
  have serverOwned := complete_identity server.binding (RegistrationAuthenticationShared.digestArray serverDigest) completed completedAt
  have initialOwned : authentication.OwnedInitFields.identity_public_key server.binding.init_fields =
      .ok initial.binding.beacon_identity_public_key := by
    rw [initialBinding]
    exact serverOwned
  have authenticatedSame : authenticated = RegistrationResponseExecutor.acceptedResponse beacon.pending beacon.packet beaconDigest :=
    core.result.Result.Ok.inj (RustM.ok.inj (beaconResumed.symm.trans (RegistrationResponseExecutor.ad_accept_exact beacon beaconDigest)))
  have beaconOwned := complete_identity beacon.pending.binding (RegistrationAuthenticationShared.digestArray beaconDigest)
    (RegistrationResponseExecutor.completedBinding beacon.pending beaconDigest) (RegistrationResponseExecutor.completedBinding_run beacon.pending beaconDigest)
  have authenticatedOwned : authentication.OwnedInitFields.identity_public_key beacon.pending.binding.init_fields =
      .ok authenticated.binding.beacon_identity_public_key := by
    rw [authenticatedSame]
    exact beaconOwned
  rw [fields] at initialOwned
  exact ⟨serverIdentity, RustM.ok.inj (initialOwned.symm.trans authenticatedOwned)⟩

/-- The identity copied by the actual completed binding is the key from the same validated original Init, so a retained pending-tuple receipt can identify its generated owner without an identity-coherence assumption. -/
theorem completed_identity_from_validated (pending : session.RegistrationBinding)
    (message : pqxdh.InitKex) (verified : pqxdh.VerifiedInitKex)
    (digest : Std.Array U8 64#usize) (completed : session.CompletedRegistrationBinding)
    (identity : pending.init_fields.identity_key = message.identity_key)
    (validated : pqxdh.validate_init_kex message = .ok (.Ok verified))
    (resumed : pending.complete digest = .ok completed) :
    completed.beacon_identity_public_key = verified.beacon_identity_public_key := by
  have tagged : message.identity_key.val[0]! = pqxdh.SIGN_TYPE_ED25519 := by
    by_contra different
    have noKey : pqxdh.untag_sign_key message.identity_key = .ok .None := by
      unfold pqxdh.untag_sign_key
      rw [index_usize_eq message.identity_key 0#usize (by simp)]
      simp only [bind_tc_ok, usize_val_0, ite_eq_right different]
    simp only [pqxdh.validate_init_kex, noKey, bind_tc_ok] at validated
    cases validated
  obtain ⟨key, _keyRun, keyBytes⟩ := TranscriptAuthInputsRefinement.identity_public_key_exact pending.init_fields
  rw [identity] at keyBytes
  have matching := RegistrationAuthenticationParsedIdentity.matches_of_values message.identity_key key tagged keyBytes
  have verifiedKey := RegistrationAuthenticationParsedIdentity.validated message key matching verified validated
  have ownedKey := RegistrationAuthenticationParsedIdentity.owned_identity pending.init_fields key
    (by simpa only [identity] using matching)
  have completedKey := complete_identity pending digest completed resumed
  exact (RustM.ok.inj (completedKey.symm.trans ownedKey)).trans verifiedKey.symm

/-- Two genuine successful Beacon cuts matching the same actual Server stage have the same owned Ed identity outside the existing collision event. This is the source-identity implication needed before the independent collision-reduction probability bound. -/
theorem shared_stage_identity (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : registration.ServerAdHash) (first second : registration.BeaconAdHash)
    (serverInput : absBytes server.input = preimage server.binding (serverView server.candidate))
    (firstInput : absBytes first.input = preimage first.pending.binding (responseView first.packet.public))
    (secondInput : absBytes second.input = preimage second.pending.binding (responseView second.packet.public))
    (serverDigest firstDigest secondDigest : CtxRomAuth.CtxDigest)
    (serverCached : cache ((), absBytes server.input) = some serverDigest)
    (firstCached : cache ((), absBytes first.input) = some firstDigest)
    (secondCached : cache ((), absBytes second.input) = some secondDigest)
    (initial : registration.ServerInitialKdf) (firstAccepted secondAccepted : registration.AuthenticatedResponse)
    (serverResumed : server.resume (.Some (RegistrationAuthenticationShared.digestArray serverDigest)) = .ok (.Ok initial))
    (firstResumed : first.resume (.Some (RegistrationAuthenticationShared.digestArray firstDigest)) = .ok (.Ok firstAccepted))
    (secondResumed : second.resume (.Some (RegistrationAuthenticationShared.digestArray secondDigest)) = .ok (.Ok secondAccepted))
    (firstMatches : initial.binding.associated_data = firstAccepted.binding.associated_data)
    (secondMatches : initial.binding.associated_data = secondAccepted.binding.associated_data)
    (collisionFree : ¬ CacheHasCollision cache) :
    firstAccepted.binding.beacon_identity_public_key = secondAccepted.binding.beacon_identity_public_key := by
  have one := completed_identities_of_ad_eq cache server first serverInput firstInput serverDigest firstDigest
    serverCached firstCached initial firstAccepted serverResumed firstResumed firstMatches collisionFree
  have two := completed_identities_of_ad_eq cache server second serverInput secondInput serverDigest secondDigest
    serverCached secondCached initial secondAccepted serverResumed secondResumed secondMatches collisionFree
  exact one.2.symm.trans two.2

/-- Distinct real Build completions of the same accepted Init retain its same owned Ed identity even when their response fields, transcript digests and assigned IDs differ. -/
theorem completed_identity_of_fields_eq (first second : session.RegistrationBinding)
    (firstDigest secondDigest : Std.Array U8 64#usize)
    (firstCompleted secondCompleted : session.CompletedRegistrationBinding)
    (firstResumed : first.complete firstDigest = .ok firstCompleted)
    (secondResumed : second.complete secondDigest = .ok secondCompleted)
    (fields : first.init_fields = second.init_fields) :
    firstCompleted.beacon_identity_public_key = secondCompleted.beacon_identity_public_key := by
  have firstIdentity := BeaconcryptCore.Refinement.SessionBinding.complete_identity first firstDigest firstCompleted firstResumed
  have secondIdentity := BeaconcryptCore.Refinement.SessionBinding.complete_identity second secondDigest secondCompleted secondResumed
  rw [fields] at firstIdentity
  exact RustM.ok.inj (firstIdentity.symm.trans secondIdentity)

end BeaconcryptCore.Computational.RegistrationAdHashIdentity
/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.resumed_digest_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.resumed_digest_of_ad_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.reached_preimage_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.reached_preimage_of_ad_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.raw_fields_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.raw_fields_of_ad_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identities_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identities_of_ad_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identity_from_validated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identity_from_validated

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.shared_stage_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.shared_stage_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identity_of_fields_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAdHashIdentity.completed_identity_of_fields_eq
