import BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceCover
import BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthDesignation

/-! The original authentication decision implies the ordinary all-attempt CTX observer event in the same complete source execution. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxStop
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A normal stopped client output is an output of the original complete source client with the same reply and full protocol state. Refused checkpoints never provide a fictitious continuation. -/
theorem source_normal_support {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (client : OracleComp ServerAuthSpec α)
    (state : HiddenState KemSK) (first : Option Nat)
    (result : Option α × (HiddenState KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ
      (sourceStopped setup codec checks context Q j tails) client).run.run (state, first)))
    (answer : α) (continues : result.1 = some answer) :
    (answer, result.2.1) ∈ support ((simulateQ
      (hiddenHandler setup codec checks context Q j (tableServices setup context tails)) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state first with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    have same := Option.some.inj continues
    subst answer
    simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    change middle ∈ support ((sourceStopped setup codec checks context Q j tails query).run (state, first)) at reached
    rw [sourceStopped_step, support_map] at reached
    obtain ⟨inner, reached, rfl⟩ := reached
    cases reply : (checkpoint query state.1.1.sessions inner.2.1.2.1 first inner.1).1 with
    | none =>
      simp only [reply, Option.elim_none, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases continues
    | some value =>
      have same := checkpoint_reply query state.1.1.sessions inner.2.1.2.1 first inner.1 value reply
      subst value
      simp only [reply, Option.elim_some] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨inner, reached, ih inner.1 inner.2 _ supported⟩

/-- The observed executable's actual normal result has exactly the original source-run support after restoring only the component-owned shared cache. -/
theorem execution_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (continues : result.1.1 = some ()) :
    PqxdhServerAuthCtxState.project (result.1.2.1, result.2.2) ∈ support
      (hiddenRun setup codec checks adversary false context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))) := by
  have erased := PqxdhFirstBeaconRecordCanonical.observed_component _ _ _ _ _ result supported
  have projected : (result.1.1,
      (PqxdhServerAuthCtxState.project (result.1.2.1, result.2.2), result.1.2.2)) ∈ support
      (Prod.map id PqxdhServerAuthCtxReserve.project <$>
        (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
          (simulateQ (PqxdhServerAuthCtxReserve.stopped
            (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
            (adversary (contextInput setup false context))).run).run
          (PqxdhServerAuthCtxReserve.initial setup context)) := by
    change _ ∈ support (Prod.map id PqxdhServerAuthCtxReserve.project <$>
      PqxdhSelectedStateInterpreter.pair <$> _)
    rw [Functor.map_map, support_map]
    exact ⟨(result.1, result.2.2), erased, rfl⟩
  rw [PqxdhServerAuthCtxReserve.initial_source] at projected
  have original := source_normal_support setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
    (adversary (contextInput setup false context)) _ none _ projected () continues
  simp only [hiddenRun, support_map, Set.mem_image]
  exact ⟨_, original, rfl⟩

/-- Every true original authentication decision in the complete observed executable is an ordinary all-attempt CTX observer win. The actual full source run supplies selected-input existence and equality; no target honesty, tuple freshness or origin premise is assumed. -/
theorem execution_won (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.execution setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (winning : PqxdhServerAuthCtxExperiment.decision setup context Q j result.1 = true) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true := by
  classical
  have normal : result.1.1 = some () := by
    cases reply : result.1.1 with
    | none => simp only [PqxdhServerAuthCtxExperiment.decision, stoppedDecision, reply, Bool.false_eq_true] at winning
    | some value => cases value; rfl
  have invariant := PqxdhServerAuthCtxObserverHistory.run_invariant setup codec checks context rest key Q j
    adversary result supported normal
  have covered := PqxdhServerAuthCtxAcceptanceCover.run_cover setup codec checks context rest key Q j
    adversary writable result supported normal
  have source := execution_source setup codec checks adversary context rest key Q j result supported normal
  have decision : hiddenDecision setup context Q j
      (PqxdhServerAuthCtxState.project (result.1.2.1, result.2.2)) = true := by
    have projected := (PqxdhServerAuthCtxExperiment.decision_project setup context Q j
      (result.1.1, (result.1.2, result.2.2))).trans winning
    simpa only [Prod.map, id_eq, PqxdhServerAuthCtxReserve.project, stoppedDecision, normal] using projected
  obtain ⟨bytes, selected, input⟩ := PqxdhServerAuthDesignation.decision_input setup codec checks adversary context
    (PqxdhServerAuthCtxMaterial.output key rest) Q j _ source decision
  have event : (PqxdhServerAuthCtxState.project (result.1.2.1, result.2.2)).1.2.2.bad = false ∧
      EntryEvent setup context.seed context.scalar Q j result.1.2.1.1.1.ghost := of_decide_eq_true decision
  exact PqxdhServerAuthCtxAcceptanceCover.covered_won setup codec context result.1.2.1 result.2.1
    covered invariant.2.clean bytes selected input event.2.1

/-- Computing the original terminal bit preserves the same successful ordinary observer attribution. -/
theorem continuation_won (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (context : Context KemSK)
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Bool × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.continuation setup codec checks adversary Q j context rest)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (winning : result.1 = true) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true := by
  simp only [PqxdhServerAuthCtxExperiment.continuation, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at supported
  obtain ⟨execution, reached, rfl⟩ := supported
  exact execution_won setup codec checks adversary context rest key Q j writable execution reached winning

/-- The actual context/residual samplers preserve the complete initial observer state, so the original full component client's true decision is an ordinary forgery-observer win for every challenger key. -/
theorem client_won (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (result : Bool × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (winning : result.1 = true) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1 = true := by
  simp only [PqxdhServerAuthCtxExperiment.client, simulateQ_bind, StateT.run_bind,
    PqxdhServerAuthCtxAcceptanceCover.observed_coins, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨context, _, rest, _, reached⟩ := supported
  exact continuation_won setup codec checks adversary context rest key Q j writable result reached winning

/-- The same uniform challenger key and actual complete client, with deterministic ordinary instrumentation retained only for analysis. -/
noncomputable def observedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    ProbComp (Bool × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)) := do
  let key ← $ᵗ RootOutput
  (simulateQ (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto key) (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).run
    (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)

/-- Erasing observer instrumentation retains the full original component decision distribution. -/
theorem observed_original (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) =
      Prod.fst <$> observedGame setup codec checks adversary Q j := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, observedGame, map_bind,
    PqxdhFirstBeaconRecordCanonical.observed_fst]

/-- The ordinary executable forgery monitor is the deterministic winning predicate of this same fully observed game. -/
theorem observed_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)) =
      (fun result => RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) result.2.1) <$>
        observedGame setup codec checks adversary Q j := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, observedGame, map_bind,
    RawCtxSelectedAuthenticationObserver.decision_interpreted]

/-- The original uniform-entry authentication probability is bounded by the constructed ordinary all-attempt forgery observer with coefficient one and no extra record/session selection factor. -/
theorem uniform_observer (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead) :
    𝒟[uniformEntryGame setup codec checks adversary false Q j] {true} ≤
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
          (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j))] {true} := by
  rw [PqxdhServerAuthCtxExperiment.uniform_game, observed_original, observed_decision]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result supported winning
  simp only [observedGame, mem_support_bind_iff] at supported
  obtain ⟨key, _, reached⟩ := supported
  exact client_won setup codec checks adversary key Q j writable result reached winning

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The concrete ordinary modified-AEAD validation reduction for the full source client's deterministic all-attempt observer. -/
noncomputable def validation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (qHash : Nat) :=
  AdaptiveCtxPrefixValidation.validationReduction (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (AdaptiveCtxDynamicKnownKeys.decisionClient setup.source.crypto
      (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j))) qHash

/-- The actual selected raw interface makes at most one attempt, so its constructed ordinary integrity reduction uses index zero without an additional target guess. -/
noncomputable def integrity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) :=
  AdaptiveRawNonceAead.indexedReduction (AdaptiveCtxReceive.baseDecoder (RawCtxUniversalDecoder.decoder codec.frameRead)) fallback
    (AdaptiveCtxReceive.wrapped (RawCtxUniversalDecoder.decoder codec.frameRead)
      (AdaptiveCtxDynamicKnownKeys.decisionClient setup.source.crypto
        (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
          (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)))) 0

/-- Exact ordinary CTX loss, retaining the two constructed primitive reductions and both explicit statistical terms. -/
noncomputable def ctxLossENN (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage setup.source.crypto
    (validation setup codec checks adversary Q j qHash)) +
  (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
  2 * modifiedNonceAeadINTCTXTAdvantage setup.source.crypto
    (integrity setup codec checks adversary Q j fallback) +
  (1 : ℝ≥0∞) / (2 ^ 512 : Nat)

/-- The transparent ordinary loss as a real total for the enclosing finite hybrid sum. -/
noncomputable def ctxLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat) : ℝ :=
  (ctxLossENN setup codec checks adversary Q j fallback qHash).toReal

/-- The exact original uniform-entry event consumes the constructed ordinary validation and integrity reductions, with one selected seal and one raw attempt proved by the executable source control. -/
theorem authentication_bound_ennreal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat)
    (hashBound : (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute qHash) :
    𝒟[uniformEntryGame setup codec checks adversary false Q j] {true} ≤
      ctxLossENN setup codec checks adversary Q j fallback qHash := by
  have records := PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j
  have ordinary := RawCtxSelectedAuthenticationObserver.authentication_bound
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) qHash 1 1
    hashBound records.1 records.2 (by norm_num)
  simpa only [Finset.sum_range_one, Nat.cast_one, ctxLossENN, validation, integrity] using
    (uniform_observer setup codec checks adversary Q j writable).trans ordinary

/-- Both primitive advantages and the explicit finite statistical terms make the exact ordinary loss finite; conversion to a real number loses no infinite mass. -/
theorem ctxLoss_finite (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat) :
    ctxLossENN setup codec checks adversary Q j fallback qHash ≠ ⊤ := by
  have primitive : modifiedNonceAeadINTCTXTAdvantage setup.source.crypto
      (integrity setup codec checks adversary Q j fallback) ≠ ⊤ := prEvent_ne_top _
  simp only [ctxLossENN, ENNReal.add_ne_top]
  constructor
  · constructor
    · constructor
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.mul_ne_top (by simp) (by norm_num)
    · exact ENNReal.mul_ne_top (by norm_num) primitive
  · exact ENNReal.div_ne_top (by norm_num)
      (Nat.cast_ne_zero.mpr (pow_ne_zero 512 (by decide : (2 : Nat) ≠ 0)))

/-- Real-valued complete uniform-entry authentication endpoint for the enclosing source/hybrid theorem. The hash budget is an operational bound on this exact client, not a new security assumption. -/
theorem authentication_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat)
    (hashBound : (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute qHash) :
    (𝒟[uniformEntryGame setup codec checks adversary false Q j] {true}).toReal ≤
      ctxLoss setup codec checks adversary Q j fallback qHash := by
  exact ENNReal.toReal_mono (ctxLoss_finite setup codec checks adversary Q j fallback qHash)
    (authentication_bound_ennreal setup codec checks adversary Q j writable fallback qHash hashBound)

/-- The real loss used by the enclosing hybrid sum is nonnegative. -/
theorem ctxLoss_nonneg (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (fallback : ModifiedNonceAeadForgery) (qHash : Nat) :
    0 ≤ ctxLoss setup codec checks adversary Q j fallback qHash := ENNReal.toReal_nonneg

end BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.source_normal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.source_normal_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.execution_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.execution_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.execution_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.execution_won

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.continuation_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.continuation_won

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.client_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.client_won

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.observed_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.observed_original

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.observed_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.observed_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.uniform_observer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.uniform_observer

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.authentication_bound_ennreal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.authentication_bound_ennreal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.ctxLoss_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.ctxLoss_finite

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.authentication_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.ctxLoss_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverEvent.ctxLoss_nonneg
