import BeaconcryptCore.Computational.PqxdhServerAuthTranscriptIdentity
import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf

/-! The complete retained eleven-field session at actual source occurrences. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootSession
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhEd25519EufCma
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The eleven retained fields. The final coordinate denotes the actual designated R1 generation occurrence, with no uniqueness claim for equal keys in another execution or replicated owner. The associated-data coordinate holds the bytes of the registration v3 record associated data, context87 followed by the BLAKE2b-512 digest of the registration transcript (before the transcript-hash rebase it held the identity layout). -/
structure Session where
  serverIdentity : PqxdhBeaconPhase2Preparation.Word32
  beaconIdentity : PqxdhBeaconPhase2Preparation.Word32
  initKex : pqxdh.InitKex
  registrationId : Pqxdh.Bytes
  prekey : X25519PublicKey
  oneTime : X25519PublicKey
  pqKey : PqxdhKemIndCca.MlKem768PublicKey
  root : RootOutput
  associatedData : Pqxdh.Bytes
  pinnedServerId : Std.U64
  origin : PqxdhServerAuthPhase1Generation.Position

/-- The actual pre-build Server, consumed token, logged seal context and verified unsigned fields. No root is recovered from the installed kernel. -/
def serverSession (token : PqxdhServerRelatedRootConsumer.Returned)
    (server : ServerState) (context : RawCtxSourceSend.SealContext)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (origin : PqxdhServerAuthPhase1Generation.Position) : Session :=
  ⟨server.server.identity, token.pending.beacon_identity_public_key,
    PqxdhServerAuthPhase1Projection.unsigned verified.identity verified.keys,
    absBytes token.pending.registration_id.bytes, verified.keys.prekey, verified.keys.oneTime, verified.keys.pqKey,
    token.root, context.associatedData, server.identityKeyId, origin⟩

/-- The actual target generation's retained fields, with the literal root returned to the successful Beacon initializer and the transcript digest of its finish supplied separately. The associated-data coordinate is the registration v3 record associated data, context87 followed by that digest (it was the identity layout before the transcript-hash rebase). -/
def beaconSession (setup : Setup baseSpec KemSK) (context : Context KemSK) (root : RootOutput)
    (digest : CtxRomAuth.CtxDigest)
    (origin : PqxdhServerAuthPhase1Generation.Position) : Session :=
  ⟨PqxdhRootTableInitialization.rootArray (context.publicValue setup).identity.ed25519,
    PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519,
    PqxdhServerAuthPhase1Projection.unsigned (setup.joint.publicKeys context.beaconSeed).ed25519
      (PqxdhServerAuthPhase1Identity.contextMaterial setup context).keyTuple,
    (setup.joint.publicKeys context.beaconSeed).ed25519.toList ++ (setup.dh.publicKey context.oneTime).toList,
    (context.publicValue setup).prekey, setup.dh.publicKey context.oneTime, context.keys.1, root,
    Pqxdh.SessionTranscript.associatedData digest.toList,
    setup.serverKeyId, origin⟩

/-- The existing winning event already isolates failure of a same-input partner's actual pre-acceptance seal to have the accepted fields. This is a deterministic event implication, not an authentication assumption. -/
theorem matching_seal (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (ghost : Ghost) (snap : Snapshot) (accepted : ghost.acceptance = some snap)
    (notWin : ¬ Win setup seed scalar ghost) :
    ∃ index context, Partner setup seed scalar snap index ∧
      (index, context) ∈ snap.seals ∧ sealed context = snap.accepted := by
  classical
  by_contra absent
  push Not at absent
  by_cases partner : ∃ index, Partner setup seed scalar snap index
  · exact notWin (Or.inr (Or.inl ⟨snap, accepted, partner, fun index related context found =>
      absent index context related found⟩))
  · exact notWin (Or.inl ⟨snap, accepted, fun index related => partner ⟨index, related⟩⟩)

/-- One actual matching partner, successful owner publication and successful Beacon finish yield the complete retained session, outside a collision of the final BLAKE2b cache. Both roles read one transcript digest: the Server at the transcript of its token's retained Init buffers and its pre-hash candidate's response fields, the Beacon at the transcript of its written candidate and the decoded Phase 2; both queries hold that digest in the final cache. Changed signed fields remain the existing all-attempt joint-use event, and both native initializations use the actual same-cache root. This replaces `path_session`, which is false once associated data is hashed: without the collision-freedom premise equal associated data does not force equal identities. -/
theorem path_session_of_noCollision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
    (partner : Partner setup context.seed context.scalar snap index)
    (sealContext : RawCtxSourceSend.SealContext) (loggedBefore : (index, sealContext) ∈ snap.seals)
    (matched : sealed sealContext = snap.accepted)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (unchanged : PqxdhServerAuthJointIdentityEuf.changed setup.joint
      (setup.joint.publicKeys context.beaconSeed) (PqxdhServerAuthPhase1Identity.contextMaterial setup context)
      (PqxdhServerAuthJointIdentityEuf.candidates codec (calls.map PqxdhServerAuthRootExecution.publicCall)) = false)
    (collisionFree : ¬ CacheHasCollision final.1.ctx) :
    ∃ token candidate digest hashed published kernel logged cache acceptCall acceptRaw input consumed init
        beaconResponse beaconHashed pending root staged,
      serverBefore.pending index = some token ∧
      acceptCall ∈ calls ∧
      (⟨acceptCall.query, acceptCall.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.accept acceptRaw), some index⟩ ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks acceptRaw).run acceptCall.before.server.consumed) ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup (context.publicValue setup)) input ∧
      token.init = input.verified.candidate ∧
      PqxdhServerAuthPhase1Receipt.Decoded codec acceptRaw input.verified ∧
      PqxdhServerAuthPhase1Projection.Projected setup (context.publicValue setup) token input.verified ∧
      serverSession token serverBefore.server sealContext input.verified .targetPhase1 =
        beaconSession setup context root digest .targetPhase1 ∧
      token.root = root ∧ Installed setup.source root kernel ∧
      PqxdhServerRegistrationPublication.prehash serverBefore.server token.pending data = some candidate ∧
      (digest, hashed) ∈ support ((CtxRomAuth.ctxRandomOracle (PqxdhTranscriptAd.query
        (PqxdhTranscriptAd.initOf token.init) (PqxdhTranscriptAd.serverResponse candidate))).run serverBefore.ctx) ∧
      serverAfter.server = PqxdhServerRegistrationPublication.publish serverBefore.server published kernel
        (PqxdhTranscriptAd.adOf digest) ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish serverBefore.server published kernel
          (PqxdhTranscriptAd.adOf digest)), (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build (associatedData := PqxdhTranscriptAd.adOf digest) setup.source
            token.pending token.root data (PqxdhTranscriptAd.adOf digest) serverBefore.server)).run ([], hashed)) ∧
      RootAt setup context.seed context.scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) root ∧
      (some staged, ((), beaconAfter.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), beaconHashed)) ∧
      beaconAfter.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      ∃ control prekey oneTime kem,
        beaconBefore.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
        beaconBefore.beaconInit = some init ∧
        init = PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup) context.beaconSeed
          context.oneTime context.keys.1 ∧
        responseOf codec raw = some beaconResponse ∧
        (digest, beaconHashed) ∈ support ((CtxRomAuth.ctxRandomOracle (PqxdhTranscriptAd.query
          (PqxdhTranscriptAd.initOf init) beaconResponse)).run beaconBefore.ctx) ∧
        some pending ∈ support ((beaconPrefix (PqxdhTranscriptAd.completedOf control digest) setup codec
          context.beaconSeed control beaconBefore.beacon.beacon.identity oneTime kem raw).run' ()) ∧
        firstBeacon final.1.ghost.touches = some
          (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) ∧
        final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
          (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
        final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) beaconResponse) = some digest := by
  -- The Server's build occurrence.
  obtain ⟨_, buildLater, buildPrior, buildNext, _, _, buildReached, buildSuffix⟩ :=
    path_occurrence setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) final calls path _ built
  have buildSource := callback_source setup codec checks (context.publicValue setup) context.beaconSeed
    context.seed context.scalar _ buildPrior buildNext buildReached
  obtain ⟨token, candidate, digest, hashed, published, kernel, logged, cache, found, passed, hashRun, _, _,
      serverEq, installed, buildRun, cacheEq, _⟩ :=
    PqxdhServerAuthRootInitialization.build_receipt_transcript setup codec checks context.seed context.scalar index
      data (serverBefore, buildPrior) response (serverAfter, buildNext) buildSource
  have serverFinal : final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
      (PqxdhTranscriptAd.serverResponse candidate)) = some digest := by
    apply (PqxdhServerAuthRootProvenance.path_grows setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar (serverAfter, buildNext) final buildLater buildSuffix).ctx
    change serverAfter.ctx _ = _
    rw [cacheEq]
    exact tail_run_grows setup codec checks _ ([], hashed) _ buildRun
      (PqxdhServerAuthTranscriptCache.query_cached hashRun).2
  -- The Beacon's finish occurrence.
  obtain ⟨control, prekey, oneTime, kem, init, beaconResponse, beaconDigest, beaconHashed, pending, root, staged,
      active, _, bundle, initEq, decoded, beaconHashRun, beaconFinal, _, _, prepared, beaconRooted, finishOrigin,
      finishRun, phaseEq, _, _⟩ :=
    PqxdhServerAuthRootAcceptance.path_finish_transcript setup codec checks context sampled initial final calls path
      raw payload beaconBefore beaconAfter beaconRoots finished snap accepted
  -- The transcript identity.
  obtain ⟨otherToken, otherCandidate, otherDigest, acceptCall, acceptRaw, input, consumed, otherInit, otherResponse,
      otherFound, acceptMember, actualCall, collected, tokenFields, tokenInit, otherPassed, otherBundle, _,
      otherDecoded, serverCached, beaconCached, _, sealAD, identityEq⟩ :=
    PqxdhServerAuthTranscriptIdentity.path_identity setup codec checks context sampled initial final calls path index
      data response serverBefore serverAfter serverRoots built raw payload beaconBefore beaconAfter beaconRoots
      finished snap accepted sealContext loggedBefore matched collisionFree
  have sameToken : token = otherToken := Option.some.inj (found.symm.trans otherFound)
  subst sameToken
  have sameCandidate : candidate = otherCandidate := Option.some.inj (passed.symm.trans otherPassed)
  subst sameCandidate
  have sameInit : init = otherInit := Option.some.inj (bundle.symm.trans otherBundle)
  subst sameInit
  have sameResponse : beaconResponse = otherResponse := Option.some.inj (decoded.symm.trans otherDecoded)
  subst sameResponse
  have sameDigest : digest = otherDigest := Option.some.inj (serverFinal.symm.trans serverCached)
  subst sameDigest
  have beaconSame : digest = beaconDigest := Option.some.inj (beaconCached.symm.trans beaconFinal)
  subst beaconSame
  -- The partner relation links the token root to the Beacon root.
  have first := (PqxdhServerAuthEntryFactor.contextSample_invariant (Reader := Reader) (Response := Response)
    setup codec context sampled).1
  have last := (PqxdhServerAuthRootProvenance.path_inv setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar _ final calls path first).1
  obtain ⟨earlier, _, other, _, _, _, _, _, _, _, original, split, inEarlier, receipt, otherFound', _⟩ :=
    PqxdhServerAuthRootProvenance.path_build_transcript setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar context.published.2 context.beaconInit initial final calls path
      index data response serverBefore serverAfter serverRoots built
  have tokenEq : token = other := Option.some.inj (found.symm.trans otherFound')
  subst tokenEq
  have originalMember : original ∈ calls := by
    rw [split]
    exact List.mem_append_left _ inEarlier
  obtain ⟨rootInputValue, _, serverRooted, touched⟩ := PqxdhServerAuthRootProvenance.token_final setup codec checks
    (context.publicValue setup) context.beaconSeed context.seed context.scalar _ final calls path original
    originalMember index token receipt
  obtain ⟨message, reply, bytes, partnerTouch, inputEq, beaconEq⟩ := partner
  have snapshot := (last.frozen snap accepted).1
  have messageEq := (last.sessionOnce index _ _ message reply touched (snapshot.subset partnerTouch)).1
  have sameInput : rootInput setup context.seed context.scalar (PqxdhServerRelatedRootInput.message rootInputValue) =
      rootInput setup context.seed context.scalar
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) := by
    rw [messageEq, inputEq]
    have retained := beaconInput_prefix setup context.seed context.scalar _ _ bytes beaconEq snapshot
    simpa only [beaconInput, finishOrigin, Option.bind_some] using retained.symm
  have sameRoot := same_input setup context.seed context.scalar final.2.cache _ _ token.root root
    serverRooted beaconRooted sameInput
  -- The verified fields of the token's accept.
  have verified := PqxdhServerAuthPhase1Receipt.prefix_receipt setup codec checks acceptRaw
    acceptCall.before.server.consumed consumed input collected
  have tokenReceipt : PqxdhServerAuthPhase1Origins.TokenReceipt setup codec checks (context.publicValue setup)
      acceptRaw token := ⟨_, _, input, collected, tokenFields, verified⟩
  have projected := PqxdhServerAuthPhase1Projection.token_projection setup codec checks (context.publicValue setup)
    acceptRaw token tokenReceipt input.verified verified.1 verified.2
  have publicMember : (⟨.inr (.accept acceptRaw), some index⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      calls.map PqxdhServerAuthRootExecution.publicCall := by
    rw [← actualCall]
    exact List.mem_map.mpr ⟨acceptCall, acceptMember, rfl⟩
  have keysEq : input.verified.keys = (PqxdhServerAuthPhase1Identity.contextMaterial setup context).keyTuple := by
    rcases PqxdhServerAuthPhase1Receipt.prefix_fields_or_substitution setup codec checks acceptRaw
      acceptCall.before.server.consumed consumed input collected adapter
      (PqxdhServerAuthPhase1Identity.contextMaterial setup context) with same | changed
    · exact same
    · rw [identityEq] at changed
      obtain ⟨read, identity, pre, one, pq⟩ := verified.1
      have bad := PqxdhServerAuthJointIdentityEuf.changed_member codec setup.joint
        (setup.joint.publicKeys context.beaconSeed) (PqxdhServerAuthPhase1Identity.contextMaterial setup context)
        (calls.map PqxdhServerAuthRootExecution.publicCall) acceptRaw (some index) input.verified.candidate publicMember
        (PqxdhServerAuthJointIdentityEuf.rawCandidate_receipt codec acceptRaw input.verified.reader
          input.verified.candidate read identity pre one pq) changed
      rw [unchanged] at bad
      cases bad
  have nativeFields := PqxdhServerAuthPhase1Projection.context_registration setup codec checks context
    acceptRaw token tokenReceipt input.verified verified.1 verified.2 identityEq keysEq
  have currentBinding := PqxdhServerAuthRootSessionFields.native_binding (PqxdhTranscriptAd.adOf digest) setup codec
    checks token.pending token.root data serverBefore.server _ _ _ response buildRun
  have serverFields := currentBinding.symm.trans projected.1
  have serverIdentity := congrArg pqxdh.ServerBinding.identity_public_key serverFields
  have serverIdentifier := congrArg pqxdh.ServerBinding.identity_key_id serverFields
  refine ⟨token, candidate, digest, hashed, published, kernel, logged, cache, acceptCall, acceptRaw, input, consumed,
    init, beaconResponse, beaconHashed, pending, root, staged, found, acceptMember, actualCall, collected,
    tokenFields, tokenInit, verified.1, projected, ?_, sameRoot, sameRoot ▸ installed, passed, hashRun, serverEq,
    buildRun, beaconRooted, finishRun, phaseEq, control, prekey, oneTime, kem, active, bundle, initEq, decoded,
    beaconHashRun, prepared, finishOrigin, serverFinal, beaconFinal⟩
  dsimp only [binding] at serverIdentity serverIdentifier
  simp only [serverSession, beaconSession, serverIdentity, serverIdentifier, nativeFields.2.1,
    nativeFields.2.2, identityEq, keysEq, sameRoot, sealAD,
    PqxdhServerAuthPhase1Identity.contextMaterial, PqxdhServerAuthPhase1Identity.material,
    Phase1Material.keyTuple]

end BeaconcryptCore.Computational.PqxdhServerAuthRootSession

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSession.matching_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSession.matching_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSession.path_session_of_noCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSession.path_session_of_noCollision
