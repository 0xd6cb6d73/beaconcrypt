import BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields

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

/-- A successful original finish supplies its actual native root and initialization, exact first acceptance, and actual target-generation identities in the associated data. The source path retains both caches and every intervening callback. -/
theorem path_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls final)
    (raw payload : Pqxdh.Bytes) (before after : GameState KemSK)
    (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (finished : (⟨.inr (.finish raw), some payload, before, after, roots⟩ : Call KemSK) ∈ calls)
    (snap : Snapshot) (accepted : final.1.ghost.acceptance = some snap) :
    ∃ control prekey oneTime kem pending root staged,
      before.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
      before.beacon = context.published.2 ∧
      control.expected_server_binding = binding setup (context.publicValue setup) ∧
      control.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray
        (setup.joint.publicKeys context.beaconSeed).ed25519 ∧
      some pending ∈ support ((beaconPrefix setup codec context.beaconSeed control before.beacon.beacon.identity
        oneTime kem raw).run' ()) ∧
      RootAt setup context.seed context.scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) root ∧
      firstBeacon final.1.ghost.touches = some
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) ∧
      (some staged, ((), after.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), before.ctx)) ∧
      after.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      snap.accepted = Accepted.ofStaged staged ∧
      snap.accepted.associatedData = Pqxdh.assocData
        (absBytes (binding setup (context.publicValue setup)).identity_public_key)
        (setup.joint.publicKeys context.beaconSeed).ed25519.toList := by
  obtain ⟨earlier, later, prior, next, split, preceding, reached, suffix⟩ :=
    path_occurrence setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) final calls path _ finished
  have source := callback_source setup codec checks (context.publicValue setup) context.beaconSeed
    context.seed context.scalar _ prior next reached
  obtain ⟨control, prekey, oneTime, kem, staged, middle, active, stagedRun, pinned, _, payloadEq, stateEq⟩ :=
    PqxdhServerAuthRootInitialization.finish_receipt setup codec (context.publicValue setup) context.beaconSeed
      context.seed context.scalar raw payload (before, prior) (after, next) source
  obtain ⟨pending, root, prepared, derived, rooted, initialized, stageState⟩ :=
    PqxdhServerAuthRootInitialization.stage_receipt setup codec context.beaconSeed context.seed context.scalar
      (context.publicValue setup) control before.beacon.beacon.identity oneTime kem raw (before, prior)
      staged middle stagedRun
  have generated := (PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled).2.2.2.2.2
  have initialInv := inv_initial setup codec context.beaconSeed (context.publicValue setup)
    context.oneTime context.keys.1 context.keys.2 context.published generated
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
  have controls := PqxdhServerAuthBeaconIdentity.phase1_control setup codec context.beaconSeed
    (context.publicValue setup) context.oneTime context.keys.1 context.keys.2 context.published generated
    control prekey oneTime kem (by rw [← retained]; exact active)
  have nativeAD := PqxdhServerAuthBeaconIdentity.native_ad setup codec pending root
    ((), before.ctx) (some staged, ((), middle.1.ctx)) initialized staged rfl
  have metadata := PqxdhPhase2DhMetadata.admitted_fields control pending.collected pending.metadata
    (PqxdhServerAuthBeaconIdentity.prefix_admitted setup codec context.beaconSeed control
      before.beacon.beacon.identity oneTime kem raw pending prepared)
  have primitiveEq : next = middle.2 := congrArg Prod.snd stateEq
  have cacheEq : after.ctx = middle.1.ctx := congrArg (fun state => state.1.ctx) stateEq
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
  refine ⟨control, prekey, oneTime, kem, pending, root, staged, active, retained, controls.1, controls.2,
    prepared, retainedRoot, firstRoot, ?_, ?_, ?_, ?_⟩
  · simpa only [cacheEq] using initialized
  · change (after, next).1.beacon.beacon.phase = _
    rw [stateEq]
    rfl
  · exact congrArg Snapshot.accepted snapshotEq
  · rw [snapshotEq]
    change absBytes staged.associatedData = _
    rw [nativeAD, metadata.2.2]
    simpa only [PqxdhRootTableInitialization.rootArray_bytes] using
      PqxdhServerAuthBeaconIdentity.control_ad (binding setup (context.publicValue setup))
        (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519) control controls

end BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.active_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.active_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.path_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootAcceptance.path_finish
