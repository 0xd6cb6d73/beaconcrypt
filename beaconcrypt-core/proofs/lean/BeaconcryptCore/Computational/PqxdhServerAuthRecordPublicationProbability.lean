import BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationJoin
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationObserverProjection

/-! The decoded-record public event is bounded in the same complete source experiment and with its own public observation. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt CtxRomAuth
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The stronger public decision is charged to the same ordinary authentication or unpublished matched attempt in the actual complete key/context/material execution. -/
theorem full_winning (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (key : CtxKey) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : PqxdhServerAuthPublicationJournalClient.Answer KemSK ×
      (PqxdhServerAuthPublicationMarkedHistory.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthPublicationMarkedHistory.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key) (PqxdhServerAuthPublicationJournalClient.full setup codec checks adversary Q j)).run
      (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (winning : PqxdhServerAuthPublicationObserverProjection.decision setup Q j
      (PqxdhServerAuthRecordPublicationEvent.observer codec j.val) result.1 = true) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1 := by
  simp only [PqxdhServerAuthPublicationJournalClient.full, simulateQ_bind, StateT.run_bind,
    PqxdhServerAuthPublicationJournalClient.observed_coins, bind_map_left,
    bind_pure_comp, simulateQ_map, StateT.run_map, mem_support_bind_iff, support_map, Set.mem_image] at supported
  obtain ⟨context, _, rest, _, outcome, reached, rfl⟩ := supported
  cases normal : outcome.1 with
  | none => simp only [PqxdhServerAuthPublicationObserverProjection.decision, normal, Bool.false_eq_true] at winning
  | some reply =>
    rcases reply with ⟨⟨answer, journal⟩, after⟩
    cases answer
    simp only [PqxdhServerAuthPublicationObserverProjection.decision, normal,
      PqxdhServerAuthPublicationObservedCompiler.decision,
      PqxdhServerAuthPublicationObservedCompiler.observe, Bool.and_eq_true] at winning
    have event := (@of_decide_eq_true _ (Classical.propDecidable _) winning.2)
    obtain ⟨snap, accepted⟩ := event.1.1
    have supportedNormal : (some (((), journal), after), outcome.2) ∈ support ((simulateQ
        (PqxdhServerAuthPublicationMarkedHistory.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (PqxdhServerAuthPublicationPrefixSource.program setup codec checks context rest Q j
          (PqxdhServerAuthApiJournal.record (adversary (contextInput setup false context)))
          (PqxdhServerAuthCtxReserve.initial setup context).1)).run
        (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)) := by
      simpa only [← normal, Prod.mk.eta] using reached
    exact PqxdhServerAuthRecordPublicationJoin.accepted_clean setup codec checks adversary context rest key Q j
      writable responseBack frameBack journal after outcome.2 supportedNormal snap accepted event.1.2.2.2
      (by simpa only [Bool.not_eq_true'] using winning.1) event.1.2.2.1
      ((PqxdhServerAuthRecordPublicationEvent.observer_true codec j.val _ journal).mp event.2)

set_option linter.deprecated false in
/-- The actual stronger public observation splits in the same experiment into the two previously bounded events, charging ordinary authentication only once. -/
theorem winning_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) :
    Pr[fun result => PqxdhServerAuthPublicationObserverProjection.decision setup Q j
      (PqxdhServerAuthRecordPublicationEvent.observer codec j.val) result.1 = true |
      PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j] ≤
    Pr[fun result => RawCtxSelectedAuthenticationObserver.won
      (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true |
      PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j] +
    Pr[fun result => PqxdhServerAuthPublicationMarkedHistory.Matched
      (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1 |
      PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j] := by
  refine (probEvent_mono (mx := PqxdhServerAuthPublicationProbability.game setup codec checks adversary Q j)
    (q := fun result => RawCtxSelectedAuthenticationObserver.won
      (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true ∨
      PqxdhServerAuthPublicationMarkedHistory.Matched
        (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1)
    ?_).trans (probEvent_or_le _ _ _)
  intro result supported winning
  simp only [PqxdhServerAuthPublicationProbability.game,
    PqxdhServerAuthPublicationMarkedHistory.sourceGame, mem_support_bind_iff] at supported
  exact supported.elim fun key reached => full_winning setup codec checks adversary key Q j
    writable responseBack frameBack result reached.2 winning

/-- The actual uniform decoded-record observation has only the existing constructed record reductions and explicit statistical terms; its stronger source inclusion is proved on the complete joint experiment. -/
theorem uniform_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (j : Fin (Q + 1)) (fallback : ModifiedNonceAeadForgery)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) :
    (𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j
      (PqxdhServerAuthRecordPublicationEvent.observer codec j.val)] {true}).toReal ≤
    PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have split := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (winning_split setup codec checks adversary Q j writable responseBack frameBack)
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at split
  simp only [PqxdhServerAuthPublicationObserverProjection.uniform_decision,
    evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def,
    PqxdhServerAuthPublicationLoss.recordLoss]
  exact split.trans (add_le_add
    (PqxdhServerAuthPublicationProbability.ordinary_bound setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins j fallback)
    (PqxdhServerAuthPublicationProbability.matched_bound setup codec checks caps bounded adversary
      qCoin Q qH qHash budget coins j))

end BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.full_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.full_winning
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.winning_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.winning_split
/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationProbability.uniform_bound
