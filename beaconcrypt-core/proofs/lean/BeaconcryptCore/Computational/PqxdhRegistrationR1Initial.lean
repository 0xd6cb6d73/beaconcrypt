-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1Audit
import BeaconcryptCore.Computational.PqxdhRegistrationJointBundle

/-! Exact constructor and bundle initialization for the single allocated registration owner. Optional source publication and both primitive caches remain part of the complete continuation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1Initial
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationR1Restriction
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

set_option backward.isDefEq.respectTransparency false in
/-- The same fixed one-time draw feeds the original R1 publication and the literal concrete-owner callback, including optional writer failure after all three signatures. -/
theorem phase1_materialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed identity : IdentitySeed) (selected oneTime : ScalarBytes)
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    Prod.map id (ownerValue identity selected publicKey) <$>
      phase1Run setup codec identity (challenge setup.joint setup.dh serverSeed selected)
        oneTime publicKey secretKey =
      pure (PqxdhRegistrationJointBundle.after setup codec 0
        (ownerValue identity selected publicKey
          (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey))
        (some oneTime) pool).1 := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon,
    simulateQ_bind, simulateQ_spec_query, phase1Impl, pure_bind]
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
    Option.map_some, PqxdhRegistrationJointBundle.after, ownerValue, phaseValue, scalarValue,
    projection, challenge]
  simp only [PqxdhLivePhase1Bundle.signing, PqxdhJointPhase1SourceWriter.signingProgram,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, phase1Impl, pure_bind, Option.map_some,
    PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
    PqxdhBeaconPhase1Publication.prepare, PqxdhJointPhase1SourceWriter.signedCandidate]
  split <;> simp_all only [simulateQ_pure, map_pure, Prod.map, ownerValue, phaseValue,
    scalarValue, PqxdhBeaconPhase1Publication.publish, id_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The logged R1 Phase 1 (`phase1Logged`, which retains the written bundle) has the same concrete owner outcome as the scheduler's bundle step and retains exactly the bundle the scheduler retains (`PqxdhRegistrationJointBundle.afterLog`). -/
theorem phase1Logged_materialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed identity : IdentitySeed) (selected oneTime : ScalarBytes)
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    Prod.map (Prod.map id (ownerValue identity selected publicKey)) id <$>
      phase1Logged setup codec identity (challenge setup.joint setup.dh serverSeed selected)
        oneTime publicKey secretKey =
      pure ((PqxdhRegistrationJointBundle.after setup codec 0
          (ownerValue identity selected publicKey
            (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey))
          (some oneTime) pool).1,
        PqxdhRegistrationJointBundle.afterLog setup codec
          (ownerValue identity selected publicKey
            (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey))
          (some oneTime) none) := by
  simp only [phase1Logged, PqxdhLivePhase1Bundle.bundle, freshBeacon,
    simulateQ_bind, simulateQ_spec_query, phase1LogImpl, phase1Impl, StateT.run_bind, StateT.run_lift, pure_bind]
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
    Option.map_some, PqxdhRegistrationJointBundle.after, PqxdhRegistrationJointBundle.afterLog,
    ownerValue, phaseValue, scalarValue, projection, challenge]
  simp only [PqxdhLivePhase1Bundle.signing, PqxdhJointPhase1SourceWriter.signingProgram,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, phase1LogImpl, phase1Impl, StateT.run_bind,
    StateT.run_lift, StateT.run_pure, pure_bind, Option.map_some,
    PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
    PqxdhBeaconPhase1Publication.prepare, PqxdhJointPhase1SourceWriter.signedCandidate]
  split
  · rename_i written
    obtain ⟨bytes, written⟩ := Option.isSome_iff_exists.mp written
    simp only [StateT.run, written, pure_bind, simulateQ_pure]
    rfl
  · rename_i written
    simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at written
    simp only [StateT.run, written, pure_bind, simulateQ_pure]
    rfl


/-- The actual native R1 initial state retains both empty primitive tables and every original Server field, with the Beacon's retained Phase 1 bundle. -/
def sourceInitial (setup : Setup baseSpec KemSK) (serverSeed : IdentitySeed) (selected : ScalarBytes)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (beaconInit : Option PqxdhEd25519EufCma.Phase1Candidate) : NativeState KemSK :=
  (PqxdhJointDhExtractFamily.empty,
    initialGameState setup (challenge setup.joint setup.dh serverSeed selected) beacon beaconInit)

/-- The actual constructor installs the first public owner at zero, with exactly the concrete representation of the original fresh R1 state. The unused compatibility Beacon remains the constructor's aborted value. -/
theorem install_initial (setup : Setup baseSpec KemSK) (serverSeed : IdentitySeed)
    (origin : PqxdhLiveServerConstruction.Origin) (value : PqxdhRegistrationJointCreation.Material KemSK) :
    PqxdhRegistrationJointCreation.install
      (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys serverSeed).ed25519) setup.serverKeyId
      (PqxdhRegistrationSchedule.initial
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed)) value =
    (0, singleton value.seed value.prekey value.keys.1
      (PqxdhRegistrationSchedule.bookkeeping
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed))
      (sourceInitial setup serverSeed value.prekey
        (freshBeacon setup (challenge setup.joint setup.dh serverSeed value.prekey) value.keys.2) none)) := by
  simp only [PqxdhRegistrationJointCreation.install, PqxdhRegistrationSchedule.initial,
    PqxdhRegistrationR1Restriction.singleton, sourceInitial, initialGameState, Function.update_eq_self]
  rfl


/-- A literal first bundle call samples its one-time scalar at the source position and returns the same complete initialized owner/state as R1, even when the optional writer fails; the scheduler's retained bundle is the R1 logged Phase 1's (`phase1Logged`). -/
theorem bundle_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed identity : IdentitySeed) (selected : ScalarBytes)
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (compatibility : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :
    (PqxdhRegistrationSchedule.bundle setup codec 0).run
      (singleton identity selected publicKey compatibility
        (sourceInitial setup serverSeed selected
          (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey) none)) =
    (fun published => (published.1.1, singleton identity selected publicKey compatibility
      (sourceInitial setup serverSeed selected published.1.2 published.2))) <$>
      (do
        let oneTime ← sampleScalar
        phase1Logged setup codec identity (challenge setup.joint setup.dh serverSeed selected)
          oneTime publicKey secretKey) := by
  rw [PqxdhRegistrationJointBundle.native_source setup codec 0 0 _ _ PqxdhDynamicIdentityPool.initialState rfl]
  simp only [PqxdhRegistrationJointBundle.traceLog, sourceInitial, initialGameState,
    ownerValue, freshBeacon, phaseValue, map_bind]
  rw [Functor.map_map, map_eq_bind_pure_comp]
  apply bind_congr
  intro oneTime
  simpa only [Functor.map_map, map_pure, Prod.map, Function.comp_def, id_eq,
    PqxdhRegistrationR1Restriction.singleton, withBeacon, sourceInitial, initialGameState, List.set_cons_zero, List.set_nil,
    ownerValue, freshBeacon, phaseValue, Function.update_idem, Function.update_self] using
    congrArg (fun program => (fun (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
        Option PqxdhEd25519EufCma.Phase1Candidate) =>
      (result.1.1, (⟨withBeacon compatibility (sourceInitial setup serverSeed selected
          (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey) result.2),
        [result.1.2], Function.update (fun _ => none) 0 result.2⟩ : PqxdhRegistrationSchedule.State KemSK))) <$> program)
      (phase1Logged_materialized setup codec serverSeed identity selected oneTime publicKey secretKey
        PqxdhDynamicIdentityPool.initialState).symm


/-- The literal first bundle followed by any adaptive restricted public continuation is the same fully audited R1 run after operational projection. Its initial invariant and private-handle shape follow from the actual optional Phase1 execution. -/
theorem bundle_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed identity : IdentitySeed) (selected : ScalarBytes)
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (secretKey : KemSK)
    (compatibility : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    Prod.map id eraseShared <$> (do
      let published ← (PqxdhRegistrationSchedule.bundle setup codec 0).run
        (singleton identity selected publicKey compatibility
          (sourceInitial setup serverSeed selected
            (freshBeacon setup (challenge setup.joint setup.dh serverSeed selected) secretKey) none))
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed)
        (simulateQ route (work published.1))).run published.2) =
    (do
      let oneTime ← sampleScalar
      let published ← phase1Logged setup codec identity (challenge setup.joint setup.dh serverSeed selected)
        oneTime publicKey secretKey
      Prod.map id (singleton identity selected publicKey compatibility ∘ eraseObservers) <$>
        (simulateQ (nativeHandler setup codec checks serverSeed selected identity) (work published.1.1)).run
          (sourceInitial setup serverSeed selected published.1.2 published.2)) := by
  rw [map_bind, bundle_initial setup codec serverSeed identity selected publicKey secretKey compatibility,
    bind_map_left, bind_assoc]
  refine bind_congr fun oneTime => ?_
  apply OracleComp.bind_congr_of_forall_mem_support
  intro published supported
  exact PqxdhRegistrationR1Audit.singleton_program setup codec checks serverSeed identity selected publicKey
    compatibility (work published.1.1) (sourceInitial setup serverSeed selected published.1.2 published.2)
    (inv_initial setup codec identity (challenge setup.joint setup.dh serverSeed selected)
      oneTime publicKey secretKey published supported)
    (phase1_handles setup codec identity (challenge setup.joint setup.dh serverSeed selected)
      oneTime publicKey secretKey published.1
      (phase1Logged_support setup codec identity (challenge setup.joint setup.dh serverSeed selected)
        oneTime publicKey secretKey published supported))


/-- The admitted typed constructor, its actual first bundle and complete adaptive suffix retain precisely the production seed/prekey/KEM/one-time draw order. The right side keeps the full original R1 audit until the final operational projection. -/
theorem typed_program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    Prod.map id eraseShared <$> (do
      let created ← (PqxdhRegistrationSchedule.create setup
        (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys serverSeed).ed25519)
        setup.serverKeyId).run (PqxdhRegistrationSchedule.initial
          (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed))
      let published ← (PqxdhRegistrationSchedule.bundle setup codec 0).run created.2
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed)
        (simulateQ route (work published.1))).run published.2) =
    (do
      let value ← PqxdhRegistrationJointCreation.material setup
      let oneTime ← sampleScalar
      let published ← phase1Logged setup codec value.seed
        (challenge setup.joint setup.dh serverSeed value.prekey) oneTime value.keys.1 value.keys.2
      Prod.map id (singleton value.seed value.prekey value.keys.1
        (PqxdhRegistrationSchedule.bookkeeping
          (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed)) ∘
        eraseObservers) <$>
        (simulateQ (nativeHandler setup codec checks serverSeed value.prekey value.seed) (work published.1.1)).run
          (sourceInitial setup serverSeed value.prekey published.1.2 published.2)) := by
  rw [map_bind, PqxdhRegistrationJointCreation.native_source, bind_map_left]
  refine bind_congr fun value => ?_
  rw [install_initial, bundle_program]


/-- Private same-execution audit of the actual source draws and original R1 continuation. None of these fields is supplied to the public client. -/
structure Audit (KemSK Result : Type) where
  material : PqxdhRegistrationJointCreation.Material KemSK
  oneTime : ScalarBytes
  published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK
  /-- The Phase 1 bundle the Beacon retained (`phase1Logged`). -/
  beaconInit : Option PqxdhEd25519EufCma.Phase1Candidate
  result : Result × NativeState KemSK

/-- The original audited continuation samples only the four actual Beacon values, in their production order. -/
noncomputable def audited (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    ProbComp (Audit KemSK Result) := do
  let value ← PqxdhRegistrationJointCreation.material setup
  let oneTime ← sampleScalar
  let logged ← phase1Logged setup codec value.seed
    (challenge setup.joint setup.dh serverSeed value.prekey) oneTime value.keys.1 value.keys.2
  let result ← (simulateQ (nativeHandler setup codec checks serverSeed value.prekey value.seed)
    (work logged.1.1)).run (sourceInitial setup serverSeed value.prekey logged.1.2 logged.2)
  pure ⟨value, oneTime, logged.1, logged.2, result⟩

/-- Erase only proof histories when observing a native audit as the actual singleton protocol state. -/
def observe (compatibility : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (audit : Audit KemSK Result) : Result × PqxdhRegistrationSchedule.State KemSK :=
  (audit.result.1, singleton audit.material.seed audit.material.prekey audit.material.keys.1
    compatibility (eraseObservers audit.result.2))

/-- The complete typed source prefix has the exact operational distribution of the same audited original execution. All original private histories remain in the audit before this projection. -/
theorem typed_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (origin : PqxdhLiveServerConstruction.Origin)
    (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    Prod.map id eraseShared <$> (do
      let created ← (PqxdhRegistrationSchedule.create setup
        (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys serverSeed).ed25519)
        setup.serverKeyId).run (PqxdhRegistrationSchedule.initial
          (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed))
      let published ← (PqxdhRegistrationSchedule.bundle setup codec 0).run created.2
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks serverSeed)
        (simulateQ route (work published.1))).run published.2) =
    observe (PqxdhRegistrationSchedule.bookkeeping
      (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin serverSeed)) <$>
      audited setup codec checks serverSeed work := by
  rw [typed_program]
  simp only [audited, observe, map_bind, bind_pure_comp, Functor.map_map, Function.comp_def]
  rfl

end BeaconcryptCore.Computational.PqxdhRegistrationR1Initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.phase1_materialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.phase1_materialized
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.phase1Logged_materialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.phase1Logged_materialized
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.install_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.install_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.bundle_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.bundle_initial
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.bundle_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.bundle_program
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.typed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.typed_program
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.typed_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Initial.typed_audit
