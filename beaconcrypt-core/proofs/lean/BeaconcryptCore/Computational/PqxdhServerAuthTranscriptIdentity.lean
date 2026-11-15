-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance

/-!
# From equal associated data to the partner's verified identity

In the generic Server-authentication game the record associated data of both honest roles is `context87 ‖ BLAKE2b-512(T)` of the 2638-byte registration transcript `T`, read from the shared lazy oracle on `GameState.ctx` (design §4.3). This module is the only place in the generic model where equality of associated data becomes equality of identities (design §5).

- `sourceAccept_identity`: the identity the Server's source acceptance returns is the parse of the received identity buffer.
- `tokenAt_init`: a pending token's accepting occurrence retained the received Phase 1 candidate of its own verified input (`PqxdhServerRelatedRootConsumer.Returned.init`).
- `path_identity`: on one source path, if the Beacon accepted a record whose sealing context is a Server build's first seal, then the Server's and the Beacon's transcript digests coincide (from the associated data alone), and unless the final BLAKE2b cache has a collision (VCVio `CacheHasCollision`) the two transcripts are equal, so the identity the Server verified is the target Beacon's identity key.

The collision event is an explicit hypothesis; its probability is bounded in `PqxdhServerAuthTranscriptCollision`. No assumption is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The identity returned by the Server's source acceptance is the parse of the received identity buffer. -/
theorem sourceAccept_identity
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept attachedVerify candidate = some (identity, keys)) :
    PqxdhEd25519EufCma.parseIdentity candidate.identityKey = some identity := by
  unfold PqxdhJointPhase1Reports.sourceAccept at accepted
  cases parsed : PqxdhEd25519EufCma.parseIdentity candidate.identityKey with
  | none => simp [parsed] at accepted
  | some pk =>
      simp only [parsed, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same, _⟩ := accepted
      rw [same]

/-- A pending token's actual accepting occurrence is a successful accept of some raw Phase 1 at that index whose complete original prefix verified an input; the token carries that input's cleared pending fields and its received Phase 1 candidate. -/
theorem tokenAt_init (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (first final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar first calls final)
    (cache : HmacOracle.QueryCache) (call : Call KemSK) (member : call ∈ calls) (index : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : PqxdhServerAuthRootProvenance.TokenAt setup codec checks publicValue seed scalar cache call index
      token) :
    ∃ raw input consumed,
      (⟨call.query, call.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.accept raw), some index⟩ ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run call.before.server.consumed) ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
      token.init = input.verified.candidate := by
  obtain ⟨found, raw, _, _, actual, _, _, _, _, _⟩ := receipt
  obtain ⟨_, _, primitive, middle, _, _, reached, _⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar first final calls path call member
  have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
  cases call with
  | mk query reply before after roots =>
      change (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = _ at actual
      cases actual
      obtain ⟨input, root, consumed, _, collected, _, _, _, stored, _⟩ :=
        PqxdhServerAuthRootInitialization.accept_receipt setup codec checks seed scalar publicValue raw
          (before, primitive) index (after, middle) source
      have same := Option.some.inj (stored.symm.trans found)
      subst same
      exact ⟨raw, input, consumed, rfl, collected, rfl, rfl⟩

/-- On one source path, a successful Server build and the Beacon's successful finish whose accepted record is that build's first seal read the same transcript digest: the Server's at the transcript of its token's retained Init buffers and its pre-hash candidate's response fields, the Beacon's at the transcript of its written candidate and the decoded Phase 2. Outside a collision of the final BLAKE2b cache the two transcripts are equal, hence the identity the Server verified at the token's accept is the target Beacon's identity key. The seal's associated data is context87 followed by that digest. -/
theorem path_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls final)
    (index : Nat) (data : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (serverBefore serverAfter : GameState KemSK) (serverRoots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (built : (⟨.inr (.build index data), some response, serverBefore, serverAfter, serverRoots⟩ : Call KemSK) ∈ calls)
    (raw payload : Pqxdh.Bytes) (beaconBefore beaconAfter : GameState KemSK)
    (beaconRoots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (finished : (⟨.inr (.finish raw), some payload, beaconBefore, beaconAfter, beaconRoots⟩ : Call KemSK) ∈ calls)
    (snap : Snapshot) (accepted : final.1.ghost.acceptance = some snap)
    (sealContext : RawCtxSourceSend.SealContext) (loggedBefore : (index, sealContext) ∈ snap.seals)
    (matched : sealed sealContext = snap.accepted)
    (collisionFree : ¬ CacheHasCollision final.1.ctx) :
    ∃ token candidate digest acceptCall acceptRaw input consumed init beaconResponse,
      serverBefore.pending index = some token ∧
      acceptCall ∈ calls ∧
      (⟨acceptCall.query, acceptCall.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.accept acceptRaw), some index⟩ ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks acceptRaw).run
        acceptCall.before.server.consumed) ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup (context.publicValue setup)) input ∧
      token.init = input.verified.candidate ∧
      PqxdhServerRegistrationPublication.prehash serverBefore.server token.pending data = some candidate ∧
      beaconBefore.beaconInit = some init ∧
      init = PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup) context.beaconSeed
        context.oneTime context.keys.1 ∧
      responseOf codec raw = some beaconResponse ∧
      final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
        (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
      final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) beaconResponse) = some digest ∧
      PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init) (PqxdhTranscriptAd.serverResponse candidate) =
        PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) beaconResponse ∧
      sealContext.associatedData = Pqxdh.SessionTranscript.associatedData digest.toList ∧
      input.verified.identity = (setup.joint.publicKeys context.beaconSeed).ed25519 := by
  obtain ⟨token, candidate, digest, _, _, found, _, _, _, _, _, passed, _, serverCached, sealMember⟩ :=
    PqxdhServerAuthRootSessionFields.path_build_context_transcript setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar (contextState setup context, initial) final calls path
      index data response serverBefore serverAfter serverRoots built
  obtain ⟨_, _, _, _, init, beaconResponse, beaconDigest, _, _, _, _, _, _, bundle, initEq, decoded, _,
      beaconCached, _, _, _, _, _, _, _, _, beaconAD⟩ :=
    PqxdhServerAuthRootAcceptance.path_finish_transcript setup codec checks context sampled initial final calls path
      raw payload beaconBefore beaconAfter beaconRoots finished snap accepted
  have initialInv := (PqxdhServerAuthEntryFactor.contextSample_invariant (Reader := Reader) (Response := Response)
    setup codec context sampled).1
  have finalInv := (PqxdhServerAuthRootProvenance.path_inv setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) final calls path
    initialInv).1
  have sealEq := congrArg Prod.snd (List.inj_on_of_nodup_map finalInv.sealOnce sealMember
    ((finalInv.frozen snap accepted).2.subset loggedBefore) rfl)
  have sealAD : sealContext.associatedData = absBytes (PqxdhTranscriptAd.adOf digest) :=
    (congrArg RawCtxSourceSend.SealContext.associatedData sealEq).symm
  have sameAD : absBytes (PqxdhTranscriptAd.adOf digest) = absBytes (PqxdhTranscriptAd.adOf beaconDigest) := by
    rw [← sealAD, PqxdhTranscriptAd.adOf_bytes beaconDigest, ← beaconAD]
    exact congrArg Accepted.associatedData matched
  have digestEq := PqxdhTranscriptAd.adOf_inj sameAD
  subst beaconDigest
  have transcriptEq := PqxdhTranscriptAd.transcript_eq_of_ad_eq final.1.ctx serverCached beaconCached rfl
    collisionFree
  obtain ⟨earlier, later, other, _, _, _, _, _, _, _, original, split, originalBefore, tokenAt, otherFound,
      _, _, _, _, _⟩ :=
    PqxdhServerAuthRootProvenance.path_build_transcript setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar context.published.2 context.beaconInit initial final calls path
      index data response serverBefore serverAfter serverRoots built
  have tokenEq : other = token := Option.some.inj (otherFound.symm.trans found)
  subst other
  have originalMember : original ∈ calls := by
    rw [split]
    exact List.mem_append_left _ originalBefore
  obtain ⟨acceptRaw, input, consumed, actualCall, collected, pendingEq, tokenInit⟩ :=
    tokenAt_init setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) final calls path _ original originalMember index token tokenAt
  have verified := PqxdhServerAuthPhase1Receipt.prefix_receipt setup codec checks acceptRaw
    original.before.server.consumed consumed input collected
  have parsed := sourceAccept_identity _ _ _ _ verified.2
  have identityEq : input.verified.identity = (setup.joint.publicKeys context.beaconSeed).ed25519 := by
    have same := transcriptEq
    rw [tokenInit, initEq] at same
    unfold PqxdhServerAuthNegativeControl.beaconCandidate at same
    exact PqxdhTranscriptAd.identity_of_transcript_eq _ _ _ _ _ _ _ parsed same
  exact ⟨token, candidate, digest, original, acceptRaw, input, consumed, init, beaconResponse, found, originalMember,
    actualCall, collected, pendingEq, tokenInit, passed, bundle, initEq, decoded, serverCached, beaconCached,
    transcriptEq, sealAD.trans (PqxdhTranscriptAd.adOf_bytes digest), identityEq⟩

end BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.sourceAccept_identity' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.sourceAccept_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.tokenAt_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.tokenAt_init

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.path_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity.path_identity
