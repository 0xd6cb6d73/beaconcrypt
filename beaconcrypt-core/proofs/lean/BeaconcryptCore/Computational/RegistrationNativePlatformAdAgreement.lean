-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage
import BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication
import BeaconcryptCore.Computational.RegistrationNativeAdInitFields
import BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut
import BeaconcryptCore.Computational.RegistrationAdHashIdentity

/-! Actual same-run pending, accepted Init, Server AD hash and Beacon response authentication cuts establish complete session AD agreement before record opening. Both hashes use their reached entries in the one shared cache. Full attached Init buffers are recovered from the original outgoing request receipt and actual accepted request outside the existing common-cache collision event; neither role's AD digest is supplied as a new premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower project)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerNativeSource.authenticate

/-- Actual matched input and original pending publication retain exactly the same attached Init buffers. -/
theorem matched_fields (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (token : peer.ConsumedRegistration)
    (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (original : RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime cache)
    (initHash : token.agreement.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision cache) :
    token.agreement.binding.init_fields = pending.binding.init_fields := by
  have tokenBinding : token.agreement.binding = server.authenticated.binding :=
    congrArg (fun accepted : agreement.ServerAgreement => accepted.binding) server.root.completedEq
  have authHash : server.authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray original.digest :=
    (congrArg (fun binding : session.RegistrationBinding => binding.init_hash) tokenBinding.symm).trans
      (initHash.trans original.initHash)
  have fields := RegistrationNativeAdInitFields.same_request_fields setup (RegistrationNativeWire.ledgerCodec wire)
    route source.verify created server.packet server.before server.afterAuthentication server.events server.authenticated
      server.checked cache server.cacheExtension original.hashing.state original.digest original.cached authHash collisionFree
  exact (congrArg (fun binding : session.RegistrationBinding => binding.init_fields) tokenBinding).trans
    (fields.trans original.retained.symm)

/-- A real lowered native callback preserves every earlier shared hash receipt, including failed continuations. -/
theorem lower_cache {Value : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before after : Local n KemSK source) (value : Value)
    (supported : (value, after) ∈ support ((lower setup checks representation created work).run before)) :
    (project before).2 ≤ (project after).2 := by
  simp only [lower, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have extension := RegistrationNativeWorldCache.program setup checks representation created
    ((work.run before.1).run before.2.1) before.2.2 inner called
  cases same
  exact extension

/-- A physical source Builder hash receipt gives the same pre-opening agreement without selecting a second issuance stage. -/
theorem from_hash_cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin matchedPin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (hashed : registration.ServerResponseHash) (path : RegistrationServerRecordExecutor.Path initial hashed)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n := n)
      (Auxiliary := RegistrationServerRoleBackend.State) coins token control pin availability application initial cache)
    (server : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token matchedPin cache)
    (original : RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime cache)
    (initHash : token.agreement.binding.init_hash = pending.binding.init_hash)
    (responseFields : RegistrationAd.serverView hashed.candidate = RegistrationAd.responseView packet.public)
    (authBefore authAfter : Local n KemSK source) (authenticated : registration.AuthenticatedResponse)
    (authenticatedAt : (.ok (.Ok authenticated), authAfter) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run authBefore))
    (authExtension : (project authAfter).2 ≤ cache)
    (collisionFree : ¬ CacheHasCollision cache) :
    initial.binding.session_transcript_hash = authenticated.binding.session_transcript_hash ∧
      initial.binding.associated_data = authenticated.binding.associated_data := by
  have rawFields := matched_fields setup checks wire route representation created owner pending oneTime
    token matchedPin cache server original initHash collisionFree
  obtain ⟨serverDigest, resumed, serverCached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token control pin availability application initial cache cut
  have origin := RegistrationAd.server_ad_origin control pin availability token.agreement application cut.pendingAd cut.selected
  have fields : cut.pendingAd.binding.init_fields = pending.binding.init_fields :=
    (congrArg (fun binding : session.RegistrationBinding => binding.init_fields) origin.2.1).trans rawFields
  have input := RegistrationAd.server_ad_selected_input control pin availability token.agreement application cut.pendingAd cut.selected
  obtain ⟨_completed, _completedAt, _binding, _consistent, candidate⟩ :=
    RegistrationAd.server_ad_resume_binding cut.pendingAd (RegistrationAuthenticationShared.digestArray serverDigest) initial resumed
  have candidateSame := (RegistrationNativeServerContents.path_contents initial hashed path).2.1.trans candidate
  have publicFields : RegistrationAd.serverView cut.pendingAd.candidate = RegistrationAd.responseView packet.public :=
    (congrArg RegistrationAd.serverView candidateSame).symm.trans responseFields
  obtain ⟨_signatureDigest, adDigest, same, _verified, _history, _extension, _signatureCached, adCached⟩ :=
    RegistrationNativeResponseAuthentication.accepted_ad_receipt setup checks representation created wire pending packet
      authBefore authAfter authenticated authenticatedAt
  rw [same]
  exact RegistrationAdHashAgreement.accepted_response_agreement cache cut.pendingAd pending packet fields publicFields input
    serverDigest adDigest serverCached (authExtension adCached) initial resumed

/-- A matching record AD identifies the ordered current identities through the same physical Server hash and actual successful Beacon authentication cache cuts. No identity is parsed from AD151 itself. -/
theorem identities_from_hash_cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (hashed : registration.ServerResponseHash) (path : RegistrationServerRecordExecutor.Path initial hashed)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n := n)
      (Auxiliary := RegistrationServerRoleBackend.State) coins token control pin availability application initial cache)
    (authBefore authAfter : Local n KemSK source) (authenticated : registration.AuthenticatedResponse)
    (authenticatedAt : (.ok (.Ok authenticated), authAfter) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run authBefore))
    (authExtension : (project authAfter).2 ≤ cache)
    (sameAd : initial.binding.associated_data = authenticated.binding.associated_data)
    (collisionFree : ¬ CacheHasCollision cache) :
    hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
      initial.binding.beacon_identity_public_key = authenticated.binding.beacon_identity_public_key := by
  obtain ⟨serverDigest, resumed, serverCached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token control pin availability application initial cache cut
  have input := RegistrationAd.server_ad_selected_input control pin availability token.agreement application cut.pendingAd cut.selected
  obtain ⟨bytes, _built, inputBytes⟩ := RegistrationAd.pending_transcript_exact pending.binding (RegistrationAd.responseView packet.public)
  let beacon : registration.BeaconAdHash := ⟨pending, packet, bytes⟩
  have beaconInput : absBytes beacon.input = RegistrationAd.preimage pending.binding (RegistrationAd.responseView packet.public) := inputBytes
  obtain ⟨_signatureDigest, adDigest, same, _verified, _history, _extension, _signatureCached, adCached⟩ :=
    RegistrationNativeResponseAuthentication.accepted_ad_receipt setup checks representation created wire pending packet
      authBefore authAfter authenticated authenticatedAt
  have beaconCached : cache ((), absBytes beacon.input) = some adDigest := by
    rw [beaconInput]
    exact authExtension adCached
  have beaconResumed : beacon.resume (.Some (RegistrationAuthenticationShared.digestArray adDigest)) = .ok (.Ok authenticated) := by
    rw [same]
    exact RegistrationResponseExecutor.ad_accept_exact beacon adDigest
  have identities := RegistrationAdHashIdentity.completed_identities_of_ad_eq cache cut.pendingAd beacon input beaconInput
    serverDigest adDigest serverCached beaconCached initial authenticated resumed beaconResumed sameAd collisionFree
  obtain ⟨_completed, _completedAt, _binding, _consistent, candidate⟩ :=
    RegistrationAd.server_ad_resume_binding cut.pendingAd (RegistrationAuthenticationShared.digestArray serverDigest) initial resumed
  have candidateSame := (RegistrationNativeServerContents.path_contents initial hashed path).2.1.trans candidate
  exact ⟨(congrArg (fun value : pqxdh.ServerRegistrationCandidate => value.server_identity_public_key) candidateSame).trans identities.1,
    identities.2⟩

/-- The same physical Server AD completion and original matching Init source receipts identify this owner's actual generated Ed key. -/
theorem owner_key_from_hash_cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin matchedPin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf) (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n := n)
      (Auxiliary := RegistrationServerRoleBackend.State) coins token control pin availability application initial cache)
    (server : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token matchedPin cache)
    (original : RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime cache)
    (initHash : token.agreement.binding.init_hash = pending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision cache) :
    initial.binding.beacon_identity_public_key =
      PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  have fields := matched_fields setup checks wire route representation created owner pending oneTime token matchedPin cache
    server original initHash collisionFree
  obtain ⟨digest, resumed, _cached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token control pin availability application initial cache cut
  have origin := RegistrationAd.server_ad_origin control pin availability token.agreement application cut.pendingAd cut.selected
  have sameFields : cut.pendingAd.binding.init_fields = pending.binding.init_fields :=
    (congrArg (fun binding : session.RegistrationBinding => binding.init_fields) origin.2.1).trans fields
  have retained : cut.pendingAd.binding.init_fields.identity_key = original.hashing.state.started.message.identity_key :=
    (congrArg (fun init : authentication.OwnedInitFields => init.identity_key) sameFields).trans original.identity
  obtain ⟨completed, completedAt, initialBinding, _consistent, _candidate⟩ := RegistrationAd.server_ad_resume_binding
    cut.pendingAd (RegistrationAuthenticationShared.digestArray digest) initial resumed
  have identity := RegistrationNativeInitOwnerIdentity.completed_identity original.started original.hashing.state owner.pin _
    cut.pendingAd.binding _ (RegistrationAuthenticationShared.digestArray digest) completed original.fixed retained original.validated completedAt
  rw [initialBinding]
  exact identity

/-- Two matched owners of one accepted Server token have equal generated Ed keys even when they select different physical Builds, response fields or AD digests. The actual source/cache cuts remain separate receipts, and their common accepted Init is the same token. -/
theorem shared_token_owner_identity (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first second : RegistrationNativeBeaconFrontend.Owner source)
    (firstPending secondPending : registration.BeaconPending)
    (firstOneTime secondOneTime : PqxdhJointGapDh.ScalarBytes)
    (token : peer.ConsumedRegistration) (firstControl secondControl : pqxdh.ServerState)
    (firstPin secondPin matchedPin : session.ServerAuthenticationPin)
    (firstAvailability secondAvailability : pqxdh.KeyIdAvailability)
    (firstApplication secondApplication : Slice U8) (firstInitial secondInitial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (firstCut : RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n := n)
      (Auxiliary := RegistrationServerRoleBackend.State) coins token firstControl firstPin firstAvailability firstApplication firstInitial cache)
    (secondCut : RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n := n)
      (Auxiliary := RegistrationServerRoleBackend.State) coins token secondControl secondPin secondAvailability secondApplication secondInitial cache)
    (firstServer : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created first firstOneTime token matchedPin cache)
    (secondServer : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created second secondOneTime token matchedPin cache)
    (firstOriginal : RegistrationNativePlatformPendingTuple.Receipt setup first firstPending firstOneTime cache)
    (secondOriginal : RegistrationNativePlatformPendingTuple.Receipt setup second secondPending secondOneTime cache)
    (firstInitHash : token.agreement.binding.init_hash = firstPending.binding.init_hash)
    (secondInitHash : token.agreement.binding.init_hash = secondPending.binding.init_hash)
    (collisionFree : ¬ CacheHasCollision cache) :
    (setup.joint.publicKeys first.identitySeed).ed25519 = (setup.joint.publicKeys second.identitySeed).ed25519 := by
  have firstKey := owner_key_from_hash_cut coins setup checks wire route representation created first firstPending firstOneTime token
    firstControl firstPin matchedPin firstAvailability firstApplication firstInitial cache firstCut firstServer firstOriginal firstInitHash collisionFree
  have secondKey := owner_key_from_hash_cut coins setup checks wire route representation created second secondPending secondOneTime token
    secondControl secondPin matchedPin secondAvailability secondApplication secondInitial cache secondCut secondServer secondOriginal secondInitHash collisionFree
  obtain ⟨firstDigest, firstResumed, _firstCached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token firstControl firstPin firstAvailability firstApplication firstInitial cache firstCut
  obtain ⟨secondDigest, secondResumed, _secondCached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token secondControl secondPin secondAvailability secondApplication secondInitial cache secondCut
  have firstOrigin := RegistrationAd.server_ad_origin firstControl firstPin firstAvailability token.agreement firstApplication firstCut.pendingAd firstCut.selected
  have secondOrigin := RegistrationAd.server_ad_origin secondControl secondPin secondAvailability token.agreement secondApplication secondCut.pendingAd secondCut.selected
  obtain ⟨firstCompleted, firstAt, firstBinding, _firstConsistent, _firstCandidate⟩ := RegistrationAd.server_ad_resume_binding
    firstCut.pendingAd (RegistrationAuthenticationShared.digestArray firstDigest) firstInitial firstResumed
  obtain ⟨secondCompleted, secondAt, secondBinding, _secondConsistent, _secondCandidate⟩ := RegistrationAd.server_ad_resume_binding
    secondCut.pendingAd (RegistrationAuthenticationShared.digestArray secondDigest) secondInitial secondResumed
  have rawSame : firstCut.pendingAd.binding.init_fields = secondCut.pendingAd.binding.init_fields :=
    congrArg (fun binding : session.RegistrationBinding => binding.init_fields) (firstOrigin.2.1.trans secondOrigin.2.1.symm)
  have completedSame := RegistrationAdHashIdentity.completed_identity_of_fields_eq firstCut.pendingAd.binding secondCut.pendingAd.binding
    (RegistrationAuthenticationShared.digestArray firstDigest) (RegistrationAuthenticationShared.digestArray secondDigest)
    firstCompleted secondCompleted firstAt secondAt rawSame
  have initialSame : firstInitial.binding.beacon_identity_public_key = secondInitial.binding.beacon_identity_public_key := by
    rw [firstBinding, secondBinding]
    exact completedSame
  exact RegistrationNativeInitOwnerIdentity.public_key_eq _ _ (firstKey.symm.trans (initialSame.trans secondKey))

variable [primitive : AdapterSealPrimitive.Operations]

/-- The actual earlier Server hash and successful pinned response authentication agree on both the session hash and complete AD before any opener is used. -/
theorem from_cuts (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before after : RegistrationServerFrontendCompiler.State n)
    (receipt : RegistrationSigningShared.Receipt)
    (stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased helper handle application before after receipt)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (server : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime stage.token pin cache)
    (original : RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime cache)
    (initHash : stage.token.agreement.binding.init_hash = pending.binding.init_hash)
    (responseFields : RegistrationAd.serverView stage.hashed.candidate = RegistrationAd.responseView packet.public)
    (serverExtension : after.world.world.1.primitive.2 ≤ cache)
    (authBefore authAfter : Local n KemSK source) (authenticated : registration.AuthenticatedResponse)
    (authenticatedAt : (.ok (.Ok authenticated), authAfter) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run authBefore))
    (authExtension : (project authAfter).2 ≤ cache)
    (collisionFree : ¬ CacheHasCollision cache) :
    stage.initial.binding.session_transcript_hash = authenticated.binding.session_transcript_hash ∧
      stage.initial.binding.associated_data = authenticated.binding.associated_data := by
  have rawFields := matched_fields setup checks wire route representation created owner pending oneTime
    stage.token pin cache server original initHash collisionFree
  obtain ⟨serverDigest, resumed, serverCached⟩ := stage.ad_cached
  have origin := RegistrationAd.server_ad_origin stage.current.control stage.pin stage.availability
    stage.token.agreement stage.plaintext stage.pendingAd stage.adStarted
  have fields : stage.pendingAd.binding.init_fields = pending.binding.init_fields :=
    (congrArg (fun binding : session.RegistrationBinding => binding.init_fields) origin.2.1).trans rawFields
  have input := RegistrationAd.server_ad_selected_input stage.current.control stage.pin stage.availability
    stage.token.agreement stage.plaintext stage.pendingAd stage.adStarted
  obtain ⟨_completed, _completedAt, _binding, _consistent, candidate⟩ :=
    RegistrationAd.server_ad_resume_binding stage.pendingAd (RegistrationAuthenticationShared.digestArray serverDigest) stage.initial resumed
  have candidateSame := (RegistrationNativeServerContents.path_contents stage.initial stage.hashed stage.path).2.1.trans candidate
  have publicFields : RegistrationAd.serverView stage.pendingAd.candidate = RegistrationAd.responseView packet.public :=
    (congrArg RegistrationAd.serverView candidateSame).symm.trans responseFields
  obtain ⟨_signatureDigest, adDigest, same, _verified, _history, _extension, _signatureCached, adCached⟩ :=
    RegistrationNativeResponseAuthentication.accepted_ad_receipt setup checks representation created wire pending packet
      authBefore authAfter authenticated authenticatedAt
  rw [same]
  exact RegistrationAdHashAgreement.accepted_response_agreement cache stage.pendingAd pending packet fields publicFields input
    serverDigest adDigest (serverExtension serverCached) (authExtension adCached) stage.initial resumed

end BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.matched_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.matched_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.from_cuts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.from_cuts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.lower_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.lower_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.from_hash_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.from_hash_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.identities_from_hash_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.identities_from_hash_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.owner_key_from_hash_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.owner_key_from_hash_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.shared_token_owner_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement.shared_token_owner_identity
