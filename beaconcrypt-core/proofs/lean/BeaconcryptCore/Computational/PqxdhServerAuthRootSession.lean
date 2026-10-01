import BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance
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

/-- The eleven retained fields. The final coordinate denotes the actual designated R1 generation occurrence, with no uniqueness claim for equal keys in another execution or replicated owner. -/
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

/-- The actual target generation's retained fields, with the literal root returned to the successful Beacon initializer supplied separately. -/
def beaconSession (setup : Setup baseSpec KemSK) (context : Context KemSK) (root : RootOutput)
    (origin : PqxdhServerAuthPhase1Generation.Position) : Session :=
  ⟨PqxdhRootTableInitialization.rootArray (context.publicValue setup).identity.ed25519,
    PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519,
    PqxdhServerAuthPhase1Projection.unsigned (setup.joint.publicKeys context.beaconSeed).ed25519
      (PqxdhServerAuthPhase1Identity.contextMaterial setup context).keyTuple,
    (setup.joint.publicKeys context.beaconSeed).ed25519.toList ++ (setup.dh.publicKey context.oneTime).toList,
    (context.publicValue setup).prekey, setup.dh.publicKey context.oneTime, context.keys.1, root,
    Pqxdh.assocData (context.publicValue setup).identity.ed25519.toList
      (setup.joint.publicKeys context.beaconSeed).ed25519.toList,
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

/-- One actual matching partner, successful owner publication and successful Beacon finish yield the complete retained session. Changed signed fields remain the existing all-attempt joint-use event, and both native initializations use the actual same-cache root. -/
theorem path_session (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
      (PqxdhServerAuthJointIdentityEuf.candidates codec (calls.map PqxdhServerAuthRootExecution.publicCall)) = false) :
    ∃ token candidate kernel logged cache acceptCall acceptRaw input consumed pending root staged,
      serverBefore.pending index = some token ∧
      acceptCall ∈ calls ∧
      (⟨acceptCall.query, acceptCall.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.accept acceptRaw), some index⟩ ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks acceptRaw).run acceptCall.before.server.consumed) ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup (context.publicValue setup)) input ∧
      PqxdhServerAuthPhase1Receipt.Decoded codec acceptRaw input.verified ∧
      PqxdhServerAuthPhase1Projection.Projected setup (context.publicValue setup) token input.verified ∧
      serverSession token serverBefore.server sealContext input.verified .targetPhase1 =
        beaconSession setup context root .targetPhase1 ∧
      token.root = root ∧ Installed setup.source root kernel ∧
      serverAfter.server = PqxdhServerRegistrationPublication.publish serverBefore.server candidate kernel () ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish serverBefore.server candidate kernel ()),
        (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root data () serverBefore.server)).run
            ([], serverBefore.ctx)) ∧
      RootAt setup context.seed context.scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) root ∧
      (some staged, ((), beaconAfter.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), beaconBefore.ctx)) ∧
      beaconAfter.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      ∃ control prekey oneTime kem,
        beaconBefore.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
        some pending ∈ support ((beaconPrefix setup codec context.beaconSeed control
          beaconBefore.beacon.beacon.identity oneTime kem raw).run' ()) ∧
        firstBeacon final.1.ghost.touches = some
          (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) := by
  obtain ⟨token, candidate, kernel, logged, cache, pending, root, staged, found, sameRoot, installed,
      serverEq, buildRun, beaconRoot, finishRun, phaseEq, finishOrigin⟩ :=
    PqxdhServerAuthRootProvenance.path_root_agreement setup codec checks context sampled initial final calls path
      index data response serverBefore serverAfter serverRoots built raw payload beaconBefore beaconAfter
      beaconRoots finished snap accepted partner
  obtain ⟨earlier, later, other, _, _, _, _, acceptCall, split, acceptBefore, tokenAt, otherFound, _⟩ :=
    PqxdhServerAuthRootProvenance.path_build setup codec checks (context.publicValue setup) context.beaconSeed
      context.seed context.scalar context.published.2 initial final calls path index data response
      serverBefore serverAfter serverRoots built
  have tokenEq : other = token := Option.some.inj (otherFound.symm.trans found)
  subst other
  obtain ⟨_, acceptRaw, input, consumed, actualCall, _, collected, tokenFields, _, _⟩ := tokenAt
  have verified := PqxdhServerAuthPhase1Receipt.prefix_receipt setup codec checks acceptRaw
    acceptCall.before.server.consumed consumed input collected
  have receipt : PqxdhServerAuthPhase1Origins.TokenReceipt setup codec checks (context.publicValue setup)
      acceptRaw token := ⟨_, _, input, collected, tokenFields, verified⟩
  have projected := PqxdhServerAuthPhase1Projection.token_projection setup codec checks (context.publicValue setup)
    acceptRaw token receipt input.verified verified.1 verified.2
  obtain ⟨other, nativeCandidate, initialKernel, otherFound, currentBinding, beaconField, serverField,
      pinnedField, initialRun, sourceAD, sealMember⟩ :=
    PqxdhServerAuthRootSessionFields.path_build_context setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar (contextState setup context, initial) final calls path
      index data response serverBefore serverAfter serverRoots built
  have tokenEq : other = token := Option.some.inj (otherFound.symm.trans found)
  subst other
  have generated := (PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled).2.2.2.2.2
  have initialInv := inv_initial setup codec context.beaconSeed (context.publicValue setup)
    context.oneTime context.keys.1 context.keys.2 context.published generated
  have finalInv := (PqxdhServerAuthRootProvenance.path_inv setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) final calls path initialInv).1
  have sealEq := congrArg Prod.snd (List.inj_on_of_nodup_map finalInv.sealOnce sealMember
    ((finalInv.frozen snap accepted).2.subset loggedBefore) rfl)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, targetAD⟩ :=
    PqxdhServerAuthRootAcceptance.path_finish setup codec checks context sampled initial final calls path
      raw payload beaconBefore beaconAfter beaconRoots finished snap accepted
  have matchedAD : absBytes nativeCandidate.associated_data = snap.accepted.associatedData :=
    (congrArg RawCtxSourceSend.SealContext.associatedData sealEq).trans
      (congrArg Accepted.associatedData matched)
  have identities := Pqxdh.assocData_inj
    (by simp : (absBytes serverBefore.server.server.identity).length = 32)
    (by simp : (absBytes token.pending.beacon_identity_public_key).length = 32)
    (by simp : (absBytes (binding setup (context.publicValue setup)).identity_public_key).length = 32)
    (setup.joint.publicKeys context.beaconSeed).ed25519.2
    (sourceAD.symm.trans (matchedAD.trans targetAD))
  have identityEq : input.verified.identity = (setup.joint.publicKeys context.beaconSeed).ed25519 := by
    apply List.Vector.toList_injective
    simpa only [PqxdhRootTableInitialization.rootArray_bytes, List.Vector.toList] using
      (congrArg absBytes projected.2.1).symm.trans identities.2
  have acceptMember : acceptCall ∈ calls := by
    rw [split]
    exact List.mem_append_left _ acceptBefore
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
    acceptRaw token receipt input.verified verified.1 verified.2 identityEq keysEq
  have serverFields := currentBinding.symm.trans projected.1
  have serverIdentity := congrArg pqxdh.ServerBinding.identity_public_key serverFields
  have serverIdentifier := congrArg pqxdh.ServerBinding.identity_key_id serverFields
  have acceptedAD : sealContext.associatedData = Pqxdh.assocData
      (context.publicValue setup).identity.ed25519.toList (setup.joint.publicKeys context.beaconSeed).ed25519.toList := by
    simpa only [sealed, binding, PqxdhRootTableInitialization.rootArray_bytes] using
      (congrArg Accepted.associatedData matched).trans targetAD
  refine ⟨token, candidate, kernel, logged, cache, acceptCall, acceptRaw, input, consumed, pending, root, staged,
    found, acceptMember, actualCall, collected, tokenFields, verified.1, projected, ?_, sameRoot,
    installed, serverEq, buildRun, beaconRoot, finishRun, phaseEq, finishOrigin⟩
  dsimp only [binding] at serverIdentity serverIdentifier
  simp only [serverSession, beaconSession, serverIdentity, serverIdentifier, nativeFields.2.1,
    nativeFields.2.2, identityEq, keysEq, sameRoot, acceptedAD,
    PqxdhServerAuthPhase1Identity.contextMaterial, PqxdhServerAuthPhase1Identity.material,
    Phase1Material.keyTuple]

end BeaconcryptCore.Computational.PqxdhServerAuthRootSession

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSession.matching_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSession.matching_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootSession.path_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootSession.path_session
