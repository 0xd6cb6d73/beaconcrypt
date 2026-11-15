import BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields
import BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCache
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconMetadata

/-! Actual accepted fields, generation and initializer occurrences on one original source path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- An active reachable Beacon has no earlier accepted snapshot: that snapshot would retain an earlier Beacon root touch, contrary to the original active-phase invariant. -/
theorem active_empty (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (state : GameState KemSK) (invariant : GameInv Reader Response setup publicValue state)
    (active : InitSent state) : state.ghost.acceptance = none := by
  cases captured : state.ghost.acceptance with
  | none => rfl
  | some snap =>
      obtain ⟨earlier, message, same, _⟩ := invariant.atomic snap captured
      exact (invariant.clean active message ((invariant.frozen snap captured).1.subset
        (by rw [same]; simp))).elim

/-- A successful original finish supplies its actual native root and initialization, exact first acceptance, the target generation's pinned Server and Beacon identity fields, and the transcript hash it read: the retained Init bundle is the target Beacon's written candidate, the decoded Phase 2 gives the response fields, the digest stays at that query in the final cache, and the accepted associated data is context87 followed by that digest. The source path retains both caches and every intervening callback. This replaces `path_finish`, whose identity-layout associated-data conjunct no longer holds. -/
theorem path_finish_transcript (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls final)
    (raw payload : Pqxdh.Bytes) (before after : GameState KemSK)
    (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (finished : (⟨.inr (.finish raw), some payload, before, after, roots⟩ : Call KemSK) ∈ calls)
    (snap : Snapshot) (accepted : final.1.ghost.acceptance = some snap) :
    ∃ control prekey oneTime kem init response digest hashed pending root staged,
      before.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
      before.beacon = context.published.2 ∧
      before.beaconInit = some init ∧
      init = PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup) context.beaconSeed
        context.oneTime context.keys.1 ∧
      responseOf codec raw = some response ∧
      (digest, hashed) ∈ support ((CtxRomAuth.ctxRandomOracle (PqxdhTranscriptAd.query
        (PqxdhTranscriptAd.initOf init) response)).run before.ctx) ∧
      final.1.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) response) = some digest ∧
      control.expected_server_binding = binding setup (context.publicValue setup) ∧
      control.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray
        (setup.joint.publicKeys context.beaconSeed).ed25519 ∧
      some pending ∈ support ((beaconPrefix (PqxdhTranscriptAd.completedOf control digest) setup codec
        context.beaconSeed control before.beacon.beacon.identity oneTime kem raw).run' ()) ∧
      RootAt setup context.seed context.scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) root ∧
      firstBeacon final.1.ghost.touches = some
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) ∧
      (some staged, ((), after.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), hashed)) ∧
      after.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      snap.accepted = Accepted.ofStaged staged ∧
      snap.accepted.associatedData = Pqxdh.SessionTranscript.associatedData digest.toList := by
  obtain ⟨earlier, later, prior, next, split, preceding, reached, suffix⟩ :=
    path_occurrence setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) final calls path _ finished
  have source := callback_source setup codec checks (context.publicValue setup) context.beaconSeed
    context.seed context.scalar _ prior next reached
  obtain ⟨control, prekey, oneTime, kem, init, response, digest, hashed, staged, middle, active, bundle, decoded,
      hashRun, stagedRun, _, _, _, stateEq⟩ :=
    PqxdhServerAuthRootInitialization.finish_receipt_transcript setup codec (context.publicValue setup)
      context.beaconSeed context.seed context.scalar raw payload (before, prior) (after, next) source
  obtain ⟨pending, root, prepared, _, rooted, initialized, stageState⟩ :=
    PqxdhServerAuthRootInitialization.stage_receipt (PqxdhTranscriptAd.completedOf control digest) setup codec
      context.beaconSeed context.seed context.scalar (context.publicValue setup) control before.beacon.beacon.identity
      oneTime kem raw ({ before with ctx := hashed }, prior) staged middle stagedRun
  have initialInv := (PqxdhServerAuthEntryFactor.contextSample_invariant (Reader := Reader) (Response := Response)
    setup codec context sampled).1
  have currentInv := (PqxdhServerAuthRootProvenance.path_inv setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) (before, prior)
    earlier preceding initialInv).1
  have empty := active_empty setup (context.publicValue setup) before currentInv
    ⟨control, prekey, oneTime, kem, active⟩
  have middleEmpty : middle.1.ghost.acceptance = none := by
    rw [stageState]
    exact empty
  have captured : after.ghost.acceptance = some
      ⟨Accepted.ofStaged staged, middle.1.ghost.touches, middle.1.ghost.seals⟩ := by
    change (after, next).1.ghost.acceptance = _
    rw [stateEq]
    simp only [Ghost.accept, middleEmpty]
  have growth := PqxdhServerAuthRootProvenance.path_grows setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (after, next) final later suffix
  have snapshotEq : snap = ⟨Accepted.ofStaged staged, middle.1.ghost.touches, middle.1.ghost.seals⟩ :=
    Option.some.inj (accepted.symm.trans (growth.acceptance _ captured))
  have retained := PqxdhServerAuthRootProvenance.path_active setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) (before, prior)
    earlier preceding ⟨control, prekey, oneTime, kem, active⟩
  change before.beacon = context.published.2 at retained
  have generated := (PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled).2.2.2.2.2
  have controls := PqxdhServerAuthBeaconIdentity.phase1_control setup codec context.beaconSeed
    (context.publicValue setup) context.oneTime context.keys.1 context.keys.2 context.published generated
    control prekey oneTime kem (by rw [← retained]; exact active)
  obtain ⟨bytes, _, publishedEq, _⟩ := PqxdhServerAuthRootSessionFields.path_generation setup codec checks context
    sampled initial (before, prior) earlier preceding ⟨control, prekey, oneTime, kem, active⟩
  have contextInit := PqxdhServerAuthTranscriptCache.context_init setup codec context sampled bytes
    (by rw [publishedEq])
  have initPath := PqxdhServerAuthTranscriptCache.path_beaconInit setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (contextState setup context, initial) (before, prior)
    earlier preceding
  have initEq : init = PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup)
      context.beaconSeed context.oneTime context.keys.1 := by
    have same : some init = some (PqxdhServerAuthNegativeControl.beaconCandidate setup (context.publicValue setup)
        context.beaconSeed context.oneTime context.keys.1) := by
      rw [← contextInit]
      exact bundle.symm.trans initPath
    exact Option.some.inj same
  have nativeAD := PqxdhServerAuthBeaconIdentity.native_ad setup codec pending root
    _ (some staged, ((), middle.1.ctx)) initialized staged rfl
  have metadata := PqxdhPhase2DhMetadata.admitted_fields (completedBinding := PqxdhTranscriptAd.completedOf control digest)
    control pending.collected pending.metadata
    (PqxdhServerAuthBeaconIdentity.prefix_admitted (PqxdhTranscriptAd.completedOf control digest) setup codec
      context.beaconSeed control before.beacon.beacon.identity oneTime kem raw pending prepared)
  have primitiveEq : next = middle.2 := congrArg Prod.snd stateEq
  have cacheEq : after.ctx = middle.1.ctx := congrArg (fun state => state.1.ctx) stateEq
  have hashCached := (PqxdhServerAuthTranscriptCache.query_cached hashRun).2
  have nativeGrown := PqxdhServerAuthTranscriptCache.afterRoot_ctx_grows setup codec _ _ _ initialized
  have retainedRoot := root_mono setup context.seed context.scalar middle.2.cache final.2.cache
    (by rw [← primitiveEq]; exact (path_roots setup codec checks (context.publicValue setup)
      context.beaconSeed context.seed context.scalar (after, next) final later suffix).1) _ root rooted
  have touches : after.ghost.touches = before.ghost.touches ++
      [.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)] := by
    change (after, next).1.ghost.touches = _
    rw [stateEq, Ghost.accept_touches, stageState]
  have firstRoot := firstBeacon_prefix _ _ _
    (show firstBeacon after.ghost.touches = some
      (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) by
      rw [touches]
      exact firstBeacon_after before.ghost.touches [] _
        (currentInv.clean ⟨control, prekey, oneTime, kem, active⟩)) growth.touches
  refine ⟨control, prekey, oneTime, kem, init, response, digest, hashed, pending, root, staged, active, retained,
    bundle, initEq, decoded, hashRun, ?_, controls.1, controls.2, prepared, retainedRoot, firstRoot, ?_, ?_, ?_, ?_⟩
  · apply growth.ctx
    change after.ctx _ = _
    rw [cacheEq]
    exact nativeGrown hashCached
  · simpa only [cacheEq] using initialized
  · change (after, next).1.beacon.beacon.phase = _
    rw [stateEq]
    rfl
  · exact congrArg Snapshot.accepted snapshotEq
  · rw [snapshotEq]
    change absBytes staged.associatedData = _
    rw [nativeAD, metadata.2.2]
    exact PqxdhTranscriptAd.adOf_bytes digest

end BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.active_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.active_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.path_finish_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.path_finish_transcript
