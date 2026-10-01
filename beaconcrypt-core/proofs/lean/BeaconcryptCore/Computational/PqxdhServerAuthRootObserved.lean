import BeaconcryptCore.Computational.PqxdhServerAuthRootJournal
import BeaconcryptCore.Computational.PqxdhServerAuthObservedGame

/-! Exact original public-journal and field-substitution projections of the private source occurrence game. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootObserved
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhServerAuthRootExecution PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The complete family interpreter preserves the exact joint public-journal projection of the original callback audit. -/
theorem execution_public {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (work : OracleComp ServerAuthSpec Result) :
    (fun result => (((result.1.1, result.1.2.2.map publicCall), result.1.2.1), result.2)) <$>
      execution setup codec checks context work =
      (simulateQ (family setup context.seed context.scalar)
        ((simulateQ (authHandler setup codec checks (context.publicValue setup) context.beaconSeed)
          (PqxdhServerAuthApiJournal.record work)).run (contextState setup context))).run
            PqxdhJointDhExtractFamily.empty := by
  have same := congrArg (fun program =>
    (simulateQ (family setup context.seed context.scalar) program).run PqxdhJointDhExtractFamily.empty)
    (program_public setup codec checks (context.publicValue setup) context.beaconSeed work
      (contextState setup context, []))
  simpa only [execution, simulateQ_map, StateT.run_map, List.map_nil, List.nil_append, Prod.eta, id_map'] using same

/-- The original local samples followed by the actual original API journal and complete source/family state. -/
noncomputable def sampledPublic (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp (PqxdhServerAuthObservedGame.Result KemSK) := do
  let context ← contextSample setup codec
  let result ← (simulateQ (family setup context.seed context.scalar)
    ((simulateQ (authHandler setup codec checks (context.publicValue setup) context.beaconSeed)
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        (contextState setup context))).run PqxdhJointDhExtractFamily.empty
  pure (context.seed, context.scalar, (result.1.1.2, result.1.2), result.2)

/-- Flattening the actual samplers recovers the existing original observed game, jointly with the chronological public journal. -/
theorem sampled_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    sampledPublic setup codec checks revealSeed adversary =
      PqxdhServerAuthObservedGame.game setup codec checks revealSeed adversary := by
  simp only [sampledPublic, contextSample, PqxdhServerAuthObservedGame.game, PqxdhServerAuthObservedGame.body,
    simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind,
    family_coins (rom_coinForward setup.hmac setup.joint setup.dh _ _), bind_map_left]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  rfl

/-- Project only the private annotation and extra local samples, retaining the exact public journal jointly with all original state. -/
def observed (result : Outcome KemSK) : PqxdhServerAuthObservedGame.Result KemSK :=
  (result.context.seed, result.context.scalar, (result.state.2.map publicCall, result.state.1), result.primitive)

/-- The original observed source game is the exact public/full-state projection of the same sampled occurrence game. -/
theorem game_observed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    observed <$> game setup codec checks revealSeed adversary =
      PqxdhServerAuthObservedGame.game setup codec checks revealSeed adversary := by
  rw [← sampled_public]
  simp only [PqxdhServerAuthRootExecution.game, PqxdhServerAuthPhase1Generation.sample, sampledPublic, map_bind, bind_map_left, map_pure]
  refine bind_congr fun context => ?_
  have same := congrArg (fun program => program >>= fun result =>
    pure (context.seed, context.scalar, (result.1.1.2, result.1.2), result.2))
    (execution_public setup codec checks context (adversary (contextInput setup revealSeed context)))
  simpa only [bind_map_left, observed] using same

/-- The original native all-attempt EUF capture is exactly the material/public-journal projection of this same annotated execution. The source invariant is obtained from the actual context sampler. -/
theorem execution_capture (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (context : Context KemSK)
    (sampled : context ∈ support (contextSample setup codec)) :
    (fun result => (⟨PqxdhServerAuthJointIdentityEuf.material setup context.scalar context.oneTime context.keys.1,
      result.1.2.2.map publicCall⟩ : PqxdhServerAuthJointIdentityEuf.Captured)) <$>
      execution setup codec checks context (adversary (contextInput setup false context)) =
        PqxdhServerAuthJointIdentityEuf.nativeCapture setup codec checks adversary context := by
  rw [PqxdhServerAuthJointIdentityEuf.nativeCapture,
    ← PqxdhServerAuthNative.program_native setup codec checks context.seed context.scalar context.beaconSeed
      _ (PqxdhJointDhExtractFamily.empty, contextState setup context)
      (contextSample_invariant setup codec context sampled).1]
  have same := congrArg (Functor.map (fun result =>
    (⟨PqxdhServerAuthJointIdentityEuf.material setup context.scalar context.oneTime context.keys.1,
      result.1.1.2⟩ : PqxdhServerAuthJointIdentityEuf.Captured)))
    (execution_public setup codec checks context (adversary (contextInput setup false context)))
  simpa only [PqxdhServerAuthNative.evaluate, Functor.map_map, family, Context.publicValue] using same

/-- The existing all-attempt signed-field substitution event on this exact private source outcome. Only its original public accept journal is scanned. -/
noncomputable def changed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (result : Outcome KemSK) : Bool :=
  PqxdhServerAuthJointIdentityEuf.changed setup.joint (setup.joint.publicKeys result.context.beaconSeed)
    (PqxdhServerAuthPhase1Identity.contextMaterial setup result.context)
    (PqxdhServerAuthJointIdentityEuf.candidates codec (result.state.2.map publicCall))

/-- The same original context order and literal native all-attempt capture, before the existing full-continuation production-order swap. -/
noncomputable def sampledBad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) : ProbComp Bool := do
  let context ← contextSample setup codec
  let result ← PqxdhServerAuthJointIdentityEuf.nativeCapture setup codec checks adversary context
  pure (PqxdhServerAuthJointIdentityEuf.changed setup.joint (setup.joint.publicKeys context.beaconSeed)
    result.honest (PqxdhServerAuthJointIdentityEuf.candidates codec result.journal))

/-- The complete annotated source and original native capture give the identical all-attempt substitution event. -/
theorem game_changed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) :
    changed setup codec <$> game setup codec checks false adversary = sampledBad setup codec checks adversary := by
  simp only [PqxdhServerAuthRootExecution.game, PqxdhServerAuthPhase1Generation.sample,
    sampledBad, map_bind, bind_map_left, map_pure]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro context sampled
  have same := congrArg (fun program => program >>= fun result => pure
    (PqxdhServerAuthJointIdentityEuf.changed setup.joint (setup.joint.publicKeys context.beaconSeed)
      result.honest (PqxdhServerAuthJointIdentityEuf.candidates codec result.journal)))
    (execution_capture setup codec checks adversary context sampled)
  simpa only [bind_map_left, changed, PqxdhServerAuthJointIdentityEuf.material,
    PqxdhServerAuthPhase1Identity.contextMaterial, PqxdhServerAuthPhase1Identity.material,
    Context.publicValue, challenge] using same

/-- The exact same audited signed-field event has the published production-order native source distribution. The existing constructor swap retains the entire evaluated continuation. -/
theorem source_bad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) :
    𝒟[changed setup codec <$> game setup codec checks false adversary] =
      𝒟[PqxdhServerAuthJointIdentityEuf.sourceBad setup codec checks adversary] := by
  rw [game_changed]
  simp only [sampledBad, contextSample, PqxdhServerAuthJointIdentityEuf.sourceBad, bind_assoc, pure_bind]
  exact PqxdhServerAuthNative.constructor_order setup fun seed scalar beaconSeed oneTime keys => do
    let published ← phase1Run setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
      oneTime keys.1 keys.2
    let result ← PqxdhServerAuthJointIdentityEuf.nativeCapture setup codec checks adversary
      ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩
    pure (PqxdhServerAuthJointIdentityEuf.changed setup.joint (setup.joint.publicKeys beaconSeed)
      result.honest (PqxdhServerAuthJointIdentityEuf.candidates codec result.journal))

/-- The same complete annotated source execution in production constructor order. The audit remains private and each actual callback is still executed once. -/
noncomputable def orderedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp (Outcome KemSK) := do
  let seed ← sampleSeed
  let beaconSeed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let published ← phase1Run setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
    oneTime keys.1 keys.2
  let context : Context KemSK := ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩
  let result ← execution setup codec checks context (adversary (contextInput setup revealSeed context))
  pure ⟨context, .targetPhase1, result.1.2, result.2⟩

/-- Any final observation of the entire same-run audit has the identical production-order distribution. The swap includes all source callbacks, private states, journals and event witnesses in its continuation. -/
theorem observation_order {Result : Type} [MeasurableSpace Result]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (observe : Outcome KemSK → Result) :
    𝒟[observe <$> game setup codec checks revealSeed adversary] =
      𝒟[observe <$> orderedGame setup codec checks revealSeed adversary] := by
  simp only [PqxdhServerAuthRootExecution.game, PqxdhServerAuthPhase1Generation.sample, contextSample,
    orderedGame, map_bind, map_pure, bind_assoc, pure_bind]
  exact PqxdhServerAuthNative.constructor_order setup fun seed scalar beaconSeed oneTime keys => do
    let published ← phase1Run setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
      oneTime keys.1 keys.2
    let context : Context KemSK := ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩
    let result ← execution setup codec checks context (adversary (contextInput setup revealSeed context))
    pure (observe ⟨context, .targetPhase1, result.1.2, result.2⟩)

end BeaconcryptCore.Computational.PqxdhServerAuthRootObserved

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.execution_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.execution_public

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.sampled_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.sampled_public

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.game_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.game_observed

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.execution_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.execution_capture

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.game_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.game_changed

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.source_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.source_bad

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.observation_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootObserved.observation_order
