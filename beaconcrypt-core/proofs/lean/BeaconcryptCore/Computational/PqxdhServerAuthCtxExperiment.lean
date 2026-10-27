import BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve

/-! The original uniform-entry experiment is compiled to an ordinary one-key CTX client with its exact context, residual sampler and full adaptive decision. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The executable terminal decision inspects only retained source annotations and the original event. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (result : Option Result × (Local KemSK × Option Nat)) : Bool :=
  PqxdhServerAuthCtxStop.stoppedDecision setup context Q j result

/-- Reinstalling the component-owned cache cannot change the actual original decision. -/
theorem decision_project (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (result : Option Result × PqxdhServerAuthCtxReserve.Monitored KemSK) :
    PqxdhServerAuthCtxStop.stoppedDecision setup context Q j
      (Prod.map id PqxdhServerAuthCtxReserve.project result) =
      decision setup context Q j (result.1, result.2.1) := by
  rcases result with ⟨_ | answer, after⟩ <;> rfl

/-- The actual adaptive stopped execution retains its entire local poststate; no selected-key argument is available to its code. -/
noncomputable def execution (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :=
  ((simulateQ (PqxdhServerAuthCtxReserve.stopped
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
    (adversary (contextInput setup false context))).run).run (PqxdhServerAuthCtxReserve.initial setup context).1

/-- The original source decision is executable using only the complete retained local state. -/
noncomputable def continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  decision setup context Q j <$> execution setup codec checks adversary Q j context rest

/-- The executable original-event continuation is exactly the full stopped source game under the actual component interpreter. -/
theorem continuation_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) :
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (continuation setup codec checks adversary Q j context rest)).run
      AdaptiveCtxDynamicKnownKeys.initialSource =
    PqxdhServerAuthCtxStop.stoppedEntryDistinguisher setup codec checks adversary false Q j context
      (PqxdhServerAuthCtxMaterial.output key rest) := by
  have same := PqxdhServerAuthCtxReserve.entry_source setup codec checks context rest Q j key adversary
  simp only [continuation, simulateQ_map, StateT.run_map, Functor.map_map]
  simpa only [decision_project, PqxdhServerAuthCtxNative.evaluate,
    PqxdhSelectedStateInterpreter.evaluate, execution, StateT.run, Functor.map_map,
    PqxdhSelectedStateInterpreter.pair, Prod.mk.eta, PqxdhServerAuthCtxReserve.initial] using same

/-- Forwarding a complete source sampler retains the entire component state and every actual uniform draw. -/
theorem sample_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sample : ProbComp Result) (state : Component) :
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (simulateQ PqxdhServerAuthCtxAmbient.coin sample)).run state =
      (fun value => (value, state)) <$> sample := by
  have same := congrArg (fun work => (fun result => (result.1, result.2.2)) <$> work)
    (PqxdhServerAuthCtxAmbient.coin_program source key read sample ((), state))
  simpa only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, Functor.map_map,
    Prod.mk.eta, id_map'] using same

/-- The concrete component client draws the complete production context and residual factor itself, then runs the original adaptive adversary. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ PqxdhServerAuthCtxCalls.Residual)
  continuation setup codec checks adversary Q j context rest

/-- Actual context and residual sampling are preserved with their complete continuation and unchanged component state. -/
theorem client_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (key : RootOutput) :
    Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (client setup codec checks adversary Q j)).run AdaptiveCtxDynamicKnownKeys.initialSource =
    (do let context ← contextSample setup codec
        let rest ← $ᵗ PqxdhServerAuthCtxCalls.Residual
        PqxdhServerAuthCtxStop.stoppedEntryDistinguisher setup codec checks adversary false Q j context
          (PqxdhServerAuthCtxMaterial.output key rest)) := by
  simp only [client, simulateQ_bind, StateT.run_bind, map_bind, sample_source, bind_map_left]
  simp only [continuation_source]

/-- The exact stopped joint-factor experiment is the ordinary one-key component experiment with this constructed client. Generator interchange preserves the complete evaluated continuation. -/
theorem stopped_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    𝒟[PqxdhServerAuthCtxStop.stoppedEntryGame setup codec checks adversary false Q j] =
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (client setup codec checks adversary Q j)] := by
  apply EvalDistEq.evalDist_eq
  have exactSampler := PqxdhServerAuthCtxMaterial.key_first_context (contextSample setup codec)
    (fun context value => PqxdhServerAuthCtxStop.stoppedEntryDistinguisher setup codec checks adversary false Q j context value)
  simpa only [PqxdhServerAuthCtxStop.stoppedEntryGame, AdaptiveCtxDynamicKnownKeys.sourceGame,
    map_bind, client_source] using exactSampler

/-- The unchanged uniform-entry authentication decision is the decision of this concrete ordinary selected-key client, with zero extra loss. -/
theorem uniform_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    𝒟[uniformEntryGame setup codec checks adversary false Q j] =
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (client setup codec checks adversary Q j)] := by
  exact (PqxdhServerAuthCtxStop.uniform_entry_event setup codec checks adversary false Q j).trans
    (stopped_game setup codec checks adversary Q j)

/-- Computing the original terminal decision preserves the actual complete execution's selected seal and raw caps. -/
theorem continuation_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    (continuation setup codec checks adversary Q j context rest).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (continuation setup codec checks adversary Q j context rest).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  simpa only [continuation, isQueryBoundP_map_iff, execution, PqxdhServerAuthCtxReserve.initial,
    PqxdhServerAuthCtxReserve.stopped] using
    PqxdhServerAuthCtxHandlerBounds.initial_record_bills setup codec checks context rest Q j adversary

/-- Both actual executable samplers add zero selected record calls, so the complete ordinary client retains the one-seal and one-raw caps. -/
theorem client_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (client setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (client setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  constructor
  · simpa only [client, Nat.zero_add] using isQueryBoundP_bind
      (PqxdhServerAuthCtxAmbient.coin_other (contextSample setup codec)).2.1
      (fun context _ => isQueryBoundP_bind
        (PqxdhServerAuthCtxAmbient.coin_other ($ᵗ PqxdhServerAuthCtxCalls.Residual)).2.1
        (fun rest _ => (continuation_bills setup codec checks adversary Q j context rest).1))
  · simpa only [client, Nat.zero_add] using isQueryBoundP_bind
      (PqxdhServerAuthCtxAmbient.coin_other (contextSample setup codec)).2.2
      (fun context _ => isQueryBoundP_bind
        (PqxdhServerAuthCtxAmbient.coin_other ($ᵗ PqxdhServerAuthCtxCalls.Residual)).2.2
        (fun rest _ => (continuation_bills setup codec checks adversary Q j context rest).2))

end BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.decision_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.decision_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.continuation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.sample_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.stopped_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.stopped_game

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.uniform_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.uniform_game

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.continuation_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.continuation_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.client_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment.client_record_bills
