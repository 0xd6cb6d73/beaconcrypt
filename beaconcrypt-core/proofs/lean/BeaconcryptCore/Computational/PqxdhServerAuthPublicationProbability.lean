import BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationComposition
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationLoss
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationResources

/-! Numerical owner-publication comparison in the same complete source-key experiment. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt CtxRomAuth
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The original selected-key sampler and complete marked source client share all observer histories and component state. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :=
  PqxdhServerAuthPublicationMarkedHistory.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto (PqxdhServerAuthPublicationJournalClient.full setup codec checks adversary Q j)

/-- Erasing only the analysis history recovers exactly the original uniform owner's public observation, including its complete context and key samplers. -/
theorem source_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j
        (PqxdhServerAuthPublicationOccurrence.observer j.val)) =
      (fun result => PqxdhServerAuthPublicationJournalClient.decision setup Q j result.1) <$>
        game setup codec checks adversary Q j := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, game, PqxdhServerAuthPublicationMarkedHistory.sourceGame, map_bind]
  refine bind_congr fun key => ?_
  rw [← PqxdhFirstBeaconRecordCanonical.observed_fst _ _ key _
    (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)]
  simpa only [Functor.map_map, Function.comp_def, PqxdhServerAuthPublicationMarkedHistory.initialState] using
    (congrArg (fun work => Prod.fst <$> work)
      (PqxdhServerAuthPublicationJournalClient.observed_decision setup codec checks adversary Q j
        true (RawCtxUniversalDecoder.decoder codec.frameRead) key
        (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource))).symm

/-- The ordinary authentication monitor is a projection of the same marked run; the publication decision changes no oracle response. -/
theorem ordinary_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j
          (PqxdhServerAuthPublicationOccurrence.observer j.val))) =
      (fun result => RawCtxSelectedAuthenticationObserver.won
        (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer) <$>
        game setup codec checks adversary Q j := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, game,
    PqxdhServerAuthPublicationMarkedHistory.sourceGame, map_bind,
    RawCtxSelectedAuthenticationObserver.decision_interpreted]
  refine bind_congr fun key => ?_
  simpa only [Functor.map_map, Function.comp_def, PqxdhServerAuthPublicationMarkedHistory.initialState] using
    (congrArg (fun work => (fun result => RawCtxSelectedAuthenticationObserver.won
      (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1) <$> work)
      (PqxdhServerAuthPublicationJournalClient.observed_decision setup codec checks adversary Q j
        true (RawCtxUniversalDecoder.decoder codec.frameRead) key
        (PqxdhServerAuthPublicationMarkedHistory.initialState, AdaptiveCtxDynamicKnownKeys.initialSource))).symm

/-- Every actual winning publication observation is charged on the same sampled run to ordinary authentication or to an unpublished matched raw attempt. -/
theorem winning_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead) :
    Pr{let result ← game setup codec checks adversary Q j}[PqxdhServerAuthPublicationJournalClient.decision setup Q j result.1 = true] ≤
    Pr{let result ← game setup codec checks adversary Q j}[RawCtxSelectedAuthenticationObserver.won
      (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true] +
    Pr{let result ← game setup codec checks adversary Q j}[PqxdhServerAuthPublicationMarkedHistory.Matched
      (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1] := by
  refine (prEvent_mono_of_support (game setup codec checks adversary Q j) _ (fun result => RawCtxSelectedAuthenticationObserver.won
    (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true ∨
    PqxdhServerAuthPublicationMarkedHistory.Matched
      (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1)
    ?_).trans (prEvent_or_le _ _ _)
  intro result supported winning
  simp only [game, PqxdhServerAuthPublicationMarkedHistory.sourceGame, mem_support_bind_iff] at supported
  exact supported.elim fun key reached =>
    PqxdhServerAuthPublicationJournalClient.full_winning setup codec checks adversary key Q j writable result reached.2 winning

/-- The unpublished matched-history event consumes the already constructed validation and private-view reductions, on the actual selected-key draw. -/
theorem matched_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin) (j : Fin (Q + 1)) :
    (Pr{let result ← game setup codec checks adversary Q j}[PqxdhServerAuthPublicationMarkedHistory.Matched
      (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead)) result.2.1]).toReal ≤
    PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j
      (RawCtxUniversalDecoder.decoder codec.frameRead) (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have records := PqxdhServerAuthPublicationJournalClient.full_record_bills setup codec checks adversary Q j
  have compared := PqxdhServerAuthPublicationMarkedHistory.source_killed_bound true
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhServerAuthPublicationRandom.decodedTag (RawCtxUniversalDecoder.decoder codec.frameRead))
    (PqxdhServerAuthPublicationJournalClient.full setup codec checks adversary Q j) records.1 records.2
  rw [← PqxdhServerAuthPublicationPrefixStop.source_clean _ _ _ _ _ _
      (by simp [PqxdhServerAuthPublicationGuess.Hit]),
    PqxdhServerAuthPublicationJournalClient.full_capture] at compared
  exact (ENNReal.toReal_mono (prEvent_ne_top _) compared).trans
    (PqxdhServerAuthPublicationPrefixSource.clean_bound setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j (RawCtxUniversalDecoder.decoder codec.frameRead))

/-- The ordinary branch uses the exact old authentication reductions, with the original complete source budget. -/
theorem ordinary_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (j : Fin (Q + 1)) (fallback : ModifiedNonceAeadForgery) :
    (Pr{let result ← game setup codec checks adversary Q j}[RawCtxSelectedAuthenticationObserver.won
      (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1.observer = true]).toReal ≤
    PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j fallback
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have bound := PqxdhServerAuthPublicationComposition.observer_bound setup codec checks adversary Q j
    (PqxdhServerAuthPublicationOccurrence.observer j.val) fallback _
    (PqxdhServerAuthCtxResources.client_hash setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom j)
  simpa only [ordinary_decision, ← prEvent_eq_evalDist_singleton _ true, prEvent_map] using bound

/-- The actual uniform owner experiment has only constructed primitive advantages and explicit statistical losses; no event-inclusion or publication premise is assumed. -/
theorem uniform_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (j : Fin (Q + 1)) (fallback : ModifiedNonceAeadForgery)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead) :
    (𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j
      (PqxdhServerAuthPublicationOccurrence.observer j.val)] {true}).toReal ≤
    PqxdhServerAuthPublicationLoss.recordLoss setup codec checks adversary Q j fallback
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have split := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩)
    (winning_split setup codec checks adversary Q j writable)
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at split
  simp only [PqxdhServerAuthPublicationObservedCompiler.uniform_game, source_decision,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, PqxdhServerAuthPublicationLoss.recordLoss]
  exact split.trans (add_le_add
    (ordinary_bound setup codec checks caps bounded adversary qCoin Q qH qHash budget coins j fallback)
    (matched_bound setup codec checks caps bounded adversary qCoin Q qH qHash budget coins j))

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.source_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.source_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.ordinary_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.ordinary_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.winning_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.winning_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.matched_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.matched_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.ordinary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.ordinary_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationProbability.uniform_bound

