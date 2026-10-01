import BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance

/-! Exact full source sampling and private occurrence audit, with unchanged original execution. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootExecution
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Run the original complete adaptive source with private callback/root occurrences. The adversary receives precisely the original public replies. -/
noncomputable def execution {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (work : OracleComp ServerAuthSpec Result) :
    ProbComp ((Result × Audit KemSK) × PqxdhJointDhExtractFamily.State) :=
  (simulateQ (family setup context.seed context.scalar)
    ((simulateQ (handler setup codec checks (context.publicValue setup) context.beaconSeed) work).run
      (contextState setup context, []))).run PqxdhJointDhExtractFamily.empty

/-- Private occurrence annotations erase from the entire interpreted adaptive continuation, retaining complete original protocol and primitive state. -/
theorem execution_erase {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (work : OracleComp ServerAuthSpec Result) :
    (fun result => ((result.1.1, result.1.2.1), result.2)) <$> execution setup codec checks context work =
      (simulateQ (family setup context.seed context.scalar)
        ((simulateQ (authHandler setup codec checks (context.publicValue setup) context.beaconSeed) work).run
          (contextState setup context))).run PqxdhJointDhExtractFamily.empty := by
  have erased := congrArg (fun program =>
    (simulateQ (family setup context.seed context.scalar) program).run PqxdhJointDhExtractFamily.empty)
    (program_erase setup codec checks (context.publicValue setup) context.beaconSeed work
      (contextState setup context, []))
  simpa only [execution, simulateQ_map, StateT.run_map] using erased

/-- The original context sampler followed by the unchanged interpreted source body. -/
noncomputable def sampledSource (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let context ← contextSample setup codec
  let result ← (simulateQ (family setup context.seed context.scalar)
    ((simulateQ (authHandler setup codec checks (context.publicValue setup) context.beaconSeed)
      (adversary (contextInput setup revealSeed context))).run (contextState setup context))).run
      PqxdhJointDhExtractFamily.empty
  pure (context.seed, context.scalar, result.1.2, result.2)

/-- Flattening the actual local samplers preserves the full original game, including all source fields, both caches and primitive histories. -/
theorem sampled_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    sampledSource setup codec checks revealSeed adversary = gameState setup codec checks revealSeed adversary := by
  simp only [sampledSource, contextSample, gameState, body, simulateQ_bind, StateT.run_bind,
    bind_assoc, pure_bind, family_coins (rom_coinForward setup.hmac setup.joint setup.dh _ _), bind_map_left]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  rfl

/-- Full private source outcome: original local samples and protocol state, the literal R1 generation coordinate, complete callback audit and full family state. -/
structure Outcome (KemSK : Type) where
  context : Context KemSK
  position : PqxdhServerAuthPhase1Generation.Position
  state : Audit KemSK
  primitive : PqxdhJointDhExtractFamily.State

/-- The literal complete R1 game with only private source-occurrence annotations added. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp (Outcome KemSK) := do
  let generated ← PqxdhServerAuthPhase1Generation.sample setup codec
  let result ← execution setup codec checks generated.1
    (adversary (contextInput setup revealSeed generated.1))
  pure ⟨generated.1, generated.2, result.1.2, result.2⟩

/-- Forget only the extra private generation coordinate, retained local samples and callback audit. -/
def erase (result : Outcome KemSK) :
    IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State :=
  (result.context.seed, result.context.scalar, result.state.1, result.primitive)

/-- The complete source game with annotations erases exactly to the approved original R1 game; there is no probability or resource loss. -/
theorem game_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    erase <$> game setup codec checks revealSeed adversary = gameState setup codec checks revealSeed adversary := by
  rw [← sampled_source]
  simp only [game, PqxdhServerAuthPhase1Generation.sample, sampledSource, map_bind, bind_map_left, map_pure]
  refine bind_congr fun context => ?_
  have same := congrArg (fun program => program >>= fun result =>
    pure (context.seed, context.scalar, result.1.2, result.2))
    (execution_erase setup codec checks context (adversary (contextInput setup revealSeed context)))
  simpa only [bind_map_left, erase] using same

/-- Each supported annotated run supplies the literal sampled context and a linked complete callback path from the original empty state. -/
theorem game_path (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks revealSeed adversary)) :
    result.context ∈ support (contextSample setup codec) ∧
    result.position = .targetPhase1 ∧
    Path setup codec checks (result.context.publicValue setup) result.context.beaconSeed
      result.context.seed result.context.scalar
      (contextState setup result.context, PqxdhJointDhExtractFamily.empty) result.state.2
      (result.state.1, result.primitive) := by
  simp only [game, PqxdhServerAuthPhase1Generation.sample, bind_map_left, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨context, sampled, actual, reached, rfl⟩ := supported
  obtain ⟨calls, recorded, path⟩ := program_path setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar (adversary (contextInput setup revealSeed context))
    (contextState setup context, []) PqxdhJointDhExtractFamily.empty actual reached
  simp only [List.nil_append] at recorded
  exact ⟨sampled, rfl, recorded ▸ path⟩

/-- The public query/reply projection of an actual private callback receipt. No root, kernel or private state is exposed. -/
def publicCall (call : Call KemSK) : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query :=
  ⟨call.query, call.reply⟩

/-- Projecting the callback audit gives exactly the original public API journal, jointly with the original result and complete protocol state. -/
theorem program_public {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (work : OracleComp ServerAuthSpec Result) (before : Audit KemSK) :
    (fun result => ((result.1, result.2.2.map publicCall), result.2.1)) <$>
      (simulateQ (handler setup codec checks publicValue beaconSeed) work).run before =
      (fun result => ((result.1.1, before.2.map publicCall ++ result.1.2), result.2)) <$>
        (simulateQ (authHandler setup codec checks publicValue beaconSeed)
          (PqxdhServerAuthApiJournal.record work)).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp [PqxdhServerAuthApiJournal.record]
  | query_bind query next ih =>
      unfold PqxdhServerAuthApiJournal.record
      rw [run_simulateQ_loggingOracle_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
        simulateQ_map, StateT.run_map, Functor.map_map]
      simp_rw [ih]
      simp only [handler, StateT.run, bind_map_left, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, publicCall]
      have same := congrArg (fun step : OracleComp PqxdhJointDhExtractRoot.RootSpec
          (ServerAuthSpec.Range query × GameState KemSK) => step >>= fun actual =>
        (fun result => ((result.1.1, before.2.map publicCall ++ ⟨query, actual.1⟩ :: result.1.2), result.2)) <$>
          (simulateQ (authHandler setup codec checks publicValue beaconSeed)
            (PqxdhServerAuthApiJournal.record (next actual.1))).run actual.2)
        (callback_erase setup codec checks publicValue beaconSeed query before.1)
      simpa only [bind_map_left, StateT.run, PqxdhServerAuthApiJournal.record] using same

end BeaconcryptCore.Computational.PqxdhServerAuthRootExecution

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.execution_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.execution_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.sampled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.sampled_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.game_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.game_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.game_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.game_path

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.program_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootExecution.program_public
