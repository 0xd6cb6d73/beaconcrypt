import BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability

/-! Exact marked-run projections for public owner observations, retaining the existing complete sampler and journal. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedEntry
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The supplied observation receives the existing root-erased ghost and chronological public API journal. It receives no additional private sampled state. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (Q : Nat) (j : Fin (Q + 1))
    (observe : Observer) (result : PqxdhServerAuthPublicationJournalClient.Answer KemSK) : Bool :=
  match result.2.2 with
  | none => false
  | some (reply, state) => PqxdhServerAuthPublicationObservedCompiler.decision setup result.1 Q j
      observe (some reply, state)

/-- A terminal public observation commutes with erasure of private publication markers, over the complete original sampled source client. -/
theorem full_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observe : Observer) :
    simulateQ PqxdhServerAuthPublicationPrefixStop.erase
      (decision setup Q j observe <$> PqxdhServerAuthPublicationJournalClient.full setup codec checks adversary Q j) =
      PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observe := by
  rw [simulateQ_map, PqxdhServerAuthPublicationJournalClient.full_erase, Functor.map_map,
    ← PqxdhServerAuthPublicationObservedCompiler.full_client]
  apply congrArg (fun f => f <$> PqxdhServerAuthPublicationObservedCompiler.full setup codec checks adversary Q j)
  funext result
  rcases result with ⟨context, rest, reply, state⟩
  cases reply <;> rfl

/-- The marked execution projects jointly to the arbitrary public decision, original ordinary history and complete component poststate. -/
theorem observed_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observe : Observer)
    (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (key : CtxRomAuth.CtxKey)
    (state : PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (decision setup Q j observe result.1, (result.2.1.observer, result.2.2))) <$>
      (simulateQ (PqxdhServerAuthPublicationMarkedHistory.observed real decode setup.source.crypto key)
        (PqxdhServerAuthPublicationJournalClient.full setup codec checks adversary Q j)).run state =
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key)
      (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observe)).run
        (state.1.observer, state.2) := by
  have same := congrArg (fun work =>
    (simulateQ (RawCtxSelectedAuthenticationObserver.observed real decode setup.source.crypto key) work).run
      (state.1.observer, state.2)) (full_decision setup codec checks adversary Q j observe)
  simp only [simulateQ_map, StateT.run_map] at same
  rw [← PqxdhServerAuthPublicationMarkedHistory.observer_erase] at same
  simpa only [Functor.map_map] using same

/-- Erasing only analysis histories recovers the original source decision under the same complete key/context/material draw. -/
theorem source_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observe : Observer) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observe) =
      (fun result => decision setup Q j observe result.1) <$>
        PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, PqxdhServerAuthPublicationProbability.game,
    PqxdhServerAuthPublicationMarkedHistory.sourceGame, map_bind]
  refine bind_congr fun key => ?_
  rw [← PqxdhFirstBeaconRecordCanonical.observed_fst _ _ key _
    (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)]
  simpa only [Functor.map_map, Function.comp_def, PqxdhServerAuthPublicationMarkedHistory.initialState] using
    (congrArg (fun work => Prod.fst <$> work)
      (observed_decision setup codec checks adversary Q j observe
        true (RawCtxUniversalDecoder.decoder codec.frameRead) key
        (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource))).symm

/-- The existing key-schedule uniform endpoint is the decision on the very same complete marked experiment, for every allowed public observer. No security inclusion is assumed. -/
theorem uniform_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observe : Observer) :
    𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j observe] =
      𝒟[(fun result => decision setup Q j observe result.1) <$>
        PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j] := by
  rw [PqxdhServerAuthPublicationObservedCompiler.uniform_game, source_decision]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.full_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.full_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.observed_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.observed_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.source_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.source_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.uniform_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection.uniform_decision
