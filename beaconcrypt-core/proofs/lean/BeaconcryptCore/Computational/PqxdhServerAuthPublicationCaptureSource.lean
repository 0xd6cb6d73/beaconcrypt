import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy

/-! Ordered selected-record capture commutes with the actual dynamic known-key lowering. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource
open CtxRomAuth AdaptiveCtxReceive PqxdhServerAuthPublicationGuess
variable {Result PrefixResult : Type}

/-- A prefix with no selected seal or raw request is forwarded completely before capture continues, preserving every actual intermediate query reply. -/
theorem capture_prefix (initial : OracleComp ReceiveSpec PrefixResult)
    (noSeal : initial.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : initial.IsQueryBoundP IsRawQuery 0)
    (next : PrefixResult → OracleComp ReceiveSpec Result) (saved : Option CtxRomRecord) :
    capture (initial >>= next) saved = (do
      let reply ← initial
      capture (next reply) saved) := by
  induction initial using OracleComp.inductionOn with
  | pure value => simp only [pure_bind]
  | query_bind query continuation ih =>
    simp only [isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal noRaw
    rcases query with ((coin | (input | request)) | bytes)
    · change (do let reply ← ReceiveSpec.query (.inl (.inl coin));
                  capture (continuation reply >>= next) saved : OracleComp ReceiveSpec Candidate) =
        (do let reply ← ReceiveSpec.query (.inl (.inl coin));
            let value ← continuation reply; capture (next value) saved)
      exact bind_congr fun reply => ih reply (noSeal.2 reply) (noRaw.2 reply)
    · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input)));
                  capture (continuation reply >>= next) saved : OracleComp ReceiveSpec Candidate) =
        (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input)));
            let value ← continuation reply; capture (next value) saved)
      exact bind_congr fun reply => ih reply (noSeal.2 reply) (noRaw.2 reply)
    · exact False.elim (noSeal.1 trivial)
    · exact False.elim (noRaw.1 trivial)

/-- Capture the actual selected record and first selected raw request at the dynamic interface. Known-key calls remain unchanged, even when their bytes equal the selected key. -/
noncomputable def dynamic (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    Option CtxRomRecord → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Candidate :=
  OracleComp.recOn work
    (fun _ _ => pure none)
    (fun query _ recurse saved => match query with
      | .inl (.inr raw) => pure (saved.map fun record => (record, raw))
      | .inl (.inl (.inr (.inr input))) => do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr input))))
          recurse reply reply
      | query => do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query query
          recurse reply saved)

/-- The dynamic and ordinary captures identify the same ordered selected occurrence and raw candidate through the actual known-key lowering. All underlying queries and replies are preserved; only the final local known-key bookkeeping is projected. -/
theorem lower (crypto : Pqxdh.Crypto) (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : AdaptiveCtxDynamicKnownKeys.ReductionState) (saved : Option CtxRomRecord) :
    capture (AdaptiveCtxDynamicKnownKeys.wrapped crypto work state) saved =
      Prod.fst <$> AdaptiveCtxDynamicKnownKeys.wrapped crypto (dynamic work saved) state := by
  induction work using OracleComp.inductionOn generalizing state saved with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl selected =>
      rcases selected with ((coin | (input | request)) | raw)
      all_goals simp only [AdaptiveCtxDynamicKnownKeys.wrapped, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind]
      all_goals simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run,
        bind_pure_comp, bind_map_left]
      · change (do let reply ← ReceiveSpec.query (.inl (.inl coin));
                    capture (AdaptiveCtxDynamicKnownKeys.wrapped crypto (next reply) state) saved : OracleComp ReceiveSpec Candidate) =
          Prod.fst <$> (do let reply ← ReceiveSpec.query (.inl (.inl coin)); AdaptiveCtxDynamicKnownKeys.wrapped crypto (dynamic (next reply) saved) state)
        rw [map_bind]
        exact bind_congr fun reply => ih reply state saved
      · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input)));
                    capture (AdaptiveCtxDynamicKnownKeys.wrapped crypto (next reply)
                      { state with selectedPublic := input.2 :: state.selectedPublic }) saved : OracleComp ReceiveSpec Candidate) =
          Prod.fst <$> (do let reply ← ReceiveSpec.query (.inl (.inr (.inl input))); AdaptiveCtxDynamicKnownKeys.wrapped crypto (dynamic (next reply) saved) { state with selectedPublic := input.2 :: state.selectedPublic })
        rw [map_bind]
        exact bind_congr fun reply => ih reply _ saved
      · change (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request)));
                    capture (AdaptiveCtxDynamicKnownKeys.wrapped crypto (next reply) state) reply : OracleComp ReceiveSpec Candidate) =
          Prod.fst <$> (do let reply ← ReceiveSpec.query (.inl (.inr (.inr request))); AdaptiveCtxDynamicKnownKeys.wrapped crypto (dynamic (next reply) reply) state)
        rw [map_bind]
        exact bind_congr fun reply => ih reply state reply
      · rfl
    | inr known =>
      change capture (AdaptiveCtxDynamicKnownKeys.wrapped crypto
        (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inr known); next reply) state) saved =
        Prod.fst <$> AdaptiveCtxDynamicKnownKeys.wrapped crypto
          (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inr known); dynamic (next reply) saved) state
      simp only [AdaptiveCtxDynamicKnownKeys.wrapped, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind]
      rw [capture_prefix]
      · rw [map_bind]
        exact bind_congr fun result => ih result.1 result.2 saved
      · exact AdaptiveCtxDynamicKnownBounds.target_step crypto _
          AdaptiveCtxSharedTarget.forward_seal_class (.inr known) state
      · exact AdaptiveCtxDynamicKnownBounds.target_step crypto _
          AdaptiveCtxSharedTarget.forward_raw_class (.inr known) state

/-- The dynamic decision tests only the actual captured tag against the first raw candidate; no selected opening is forwarded. -/
noncomputable def decision (decode : RawDecoder) (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := by
  classical
  exact (fun candidate => decide (Hit (PqxdhServerAuthPublicationRandom.decodedTag decode) candidate)) <$>
    dynamic work none

/-- Ordinary-interface form of the same private tag decision. -/
noncomputable def ordinary (decode : RawDecoder) (work : OracleComp ReceiveSpec Result) :
    OracleComp ReceiveSpec Bool := by
  classical
  exact (fun candidate => decide (Hit (PqxdhServerAuthPublicationRandom.decodedTag decode) candidate)) <$>
    capture work none

/-- The ordinary decision produced by the maintained dynamic compiler is exactly the ordered capture used in the checked privacy endpoint. -/
theorem decision_lower (crypto : Pqxdh.Crypto) (decode : RawDecoder)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    AdaptiveCtxDynamicKnownKeys.decisionClient crypto (decision decode work) =
      ordinary decode (AdaptiveCtxDynamicKnownKeys.wrapped crypto work AdaptiveCtxDynamicKnownKeys.initialReduction) := by
  classical
  rw [ordinary, lower]
  simp only [AdaptiveCtxDynamicKnownKeys.decisionClient, decision,
    AdaptiveCtxDynamicKnownKeys.wrapped, simulateQ_map, StateT.run_map, Functor.map_map]

open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- Concrete dynamic capture of the complete sampled reference lowers to the exact ordinary Boolean distinguisher, with no selected-occurrence identification from equal bytes. -/
theorem reference_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (decode : RawDecoder) :
    AdaptiveCtxDynamicKnownKeys.decisionClient setup.source.crypto
      (decision decode (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j)) =
      PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode := by
  rw [decision_lower]
  rfl

/-- The selected-key source game of the actual dynamic reference capture is the canonical ordinary endpoint. The key sampler and both complete source samplers remain unchanged. -/
theorem reference_view (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (decode : RawDecoder) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
      (decision decode (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j)) =
      AdaptiveCtxPrivacyGuard.canonicalView decode setup.source.crypto
        (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode) := by
  rw [AdaptiveCtxDynamicKnownKeys.source_view, AdaptiveCtxSharedModes.real_view_eq, reference_decision]

/-- Interpreting the dynamic Boolean observer is exactly the event on its actual captured record/raw pair, with the complete source component state retained. -/
theorem capture_probability (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    Pr{let result ← AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto (decision decode work)}[result.1 = true] =
      Pr{let result ← AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto (dynamic work none)}[Hit (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1] := by
  classical
  simp only [decision, AdaptiveCtxDynamicKnownKeys.sourceGame, simulateQ_map, StateT.run_map,
    OracleComp.prEvent_bind_eq_tsum, prEvent_map, decide_eq_true_eq]

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh

/-- The actual dynamic source game for the concrete reference capture consumes the exact ordinary privacy bound and original source budgets. No occurrence, failure or tag law is supplied by the caller. -/
theorem reference_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    (Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
        (dynamic (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j) none))}[Hit (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1]).toReal ≤
      PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j decode
        (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  rw [← capture_probability]
  have bound := PqxdhServerAuthPublicationPrivacy.source_bound setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j decode
  rw [← reference_view] at bound
  simpa only [prEvent_map, Function.comp_def] using bound

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.capture_prefix' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.capture_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.lower
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.decision_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.decision_lower
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_view
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.capture_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.capture_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource.reference_bound
