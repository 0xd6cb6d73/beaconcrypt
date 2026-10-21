import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost

/-! The actual selected-publication stop is a structural truncation of the unconditional mixed reference, so its first-raw capture inherits the existing reference bound. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxCalls PqxdhServerAuthPublicationPruning
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- The entire reference-side killed continuation is a truncation of the unconditional reference. Only the latter's final analysis ghost is projected; each continuing original callback remains complete. -/
theorem reference_prunes (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    Prunes ((simulateQ (PqxdhServerAuthPublicationFilter.filtered false setup codec checks context rest Q j) work).run state).run
      (Prod.map id PqxdhServerAuthPublicationGhost.tracked <$>
        (simulateQ (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j) work).run.run state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => exact .stop (some (value, state)) _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OptionT.run_bind, Option.elimM, map_bind]
      rw [← PqxdhServerAuthPublicationFailure.stopped_reference setup codec checks context rest Q j query state]
      simp only [PqxdhServerAuthPublicationFilter.filtered, StateT.run, OptionT.run_mk, bind_map_left]
      refine bind_same _ _ _ fun result _ => ?_
      simp only [PqxdhServerAuthPublicationFilter.gate, Bool.false_eq_true, ite_false]
      split_ifs
      · exact .stop none _
      · cases reply : result.2.1 with
        | none => exact .stop none _
        | some value =>
            have tail := ih value (PqxdhServerAuthPublicationGhost.tracked result.2.2)
            rw [← PqxdhServerAuthPublicationReferenceGhost.program_project setup codec checks context rest Q j
              (next value) result.2.2] at tail
            simpa only [Option.map_some, Option.elim_some, StateT.run] using tail

/-- The comparison retains the original context and residual samplers and adaptive source input. Its terminal value is unused by the before-raw observer. -/
noncomputable def comparisonClient (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Unit := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ Residual)
  let _ ← ((simulateQ (PqxdhServerAuthPublicationFilter.filtered false setup codec checks context rest Q j)
    (adversary (contextInput setup false context))).run (PqxdhServerAuthCtxReserve.initial setup context).1).run
  pure ()

/-- The fully sampled adaptive comparison is a truncation of the exact unconditional reference used by the privacy reduction. Terminal observations do not alter the original query tree. -/
theorem client_prunes (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    Prunes (comparisonClient setup codec checks adversary Q j)
      ((fun _ => ()) <$> PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j) := by
  simp only [comparisonClient, PqxdhServerAuthPublicationReference.client, map_bind]
  refine bind_same _ _ _ fun context _ => ?_
  refine bind_same _ _ _ fun rest _ => ?_
  simpa only [map_pure, bind_pure_comp, Functor.map_map, PqxdhServerAuthPublicationReference.execution] using
    map_both _ _ (reference_prunes setup codec checks context rest Q j
      (adversary (contextInput setup false context)) (PqxdhServerAuthCtxReserve.initial setup context).1)
      (fun _ => ()) (fun _ => ())

/-- The actual fully sampled killed reference capture is bounded by the unchanged unconditional reference capture, with its original selected-key draw and shared state. -/
theorem client_capture (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : AdaptiveCtxReceive.RawDecoder) :
    Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic (comparisonClient setup codec checks adversary Q j) none))}[PqxdhServerAuthPublicationGuess.Hit
      (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1] ≤
      Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
          (PqxdhServerAuthPublicationCaptureSource.dynamic
            (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j) none))}[PqxdhServerAuthPublicationGuess.Hit
        (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1] := by
  simpa only [dynamic_map] using source_mono true decode setup.source.crypto _ _
    (client_prunes setup codec checks adversary Q j) none
    (PqxdhServerAuthPublicationGuess.Hit (PqxdhServerAuthPublicationRandom.decodedTag decode))
    (by simp [PqxdhServerAuthPublicationGuess.Hit])

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh

/-- The concrete stopped comparison consumes the existing ordinary reference reductions with the original source budgets. No failure-conditioned tag law or caller event inclusion is assumed. -/
theorem comparison_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : AdaptiveCtxReceive.RawDecoder) :
    (Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic (comparisonClient setup codec checks adversary Q j) none))}[PqxdhServerAuthPublicationGuess.Hit
      (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1]).toReal ≤
      PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j decode
        (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  exact (ENNReal.toReal_mono (prEvent_ne_top _) (client_capture setup codec checks adversary Q j decode)).trans
    (PqxdhServerAuthPublicationCaptureSource.reference_bound setup codec checks caps bounded adversary
      qCoin Q qHash qH coins accepts hashes rom j decode)

/-- Every generalized all-replies certificate of the complete reference also bounds the stopped comparison. This covers weighted bytes as well as primitive-interface classes. -/
theorem client_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (budget : Budget)
    (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget)
    (bounded : (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j).IsQueryBound budget canQuery cost) :
    (comparisonClient setup codec checks adversary Q j).IsQueryBound budget canQuery cost := by
  exact query_bound _ _ (client_prunes setup codec checks adversary Q j) budget canQuery cost
    (by simpa only [isQueryBound_map_iff] using bounded)

/-- The actual source continuation is stopped only after a successful selected outer publication. It retains the complete original ghost between callbacks and preserves the original sampler order. -/
noncomputable def actualClient (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Unit := do
  let context ← simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec)
  let rest ← simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ Residual)
  let _ ← ((simulateQ (PqxdhServerAuthPublicationFilter.sourceFiltered setup codec checks context rest Q j)
    (adversary (contextInput setup false context))).run (PqxdhServerAuthCtxReserve.initial setup context).1).run
  pure ()

/-- Full adaptive source execution and its filtered comparison have the identical query program after discarding only their terminal result. The actual source preserves its private ghost until that terminal point. -/
theorem actual_comparison (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    actualClient setup codec checks adversary Q j = comparisonClient setup codec checks adversary Q j := by
  simp only [actualClient, comparisonClient]
  refine bind_congr fun context => ?_
  refine bind_congr fun rest => ?_
  have same := congrArg (fun program => (fun _ => ()) <$> program)
    (PqxdhServerAuthPublicationFilter.source_program setup codec checks context rest Q j
      (adversary (contextInput setup false context)) (PqxdhServerAuthCtxReserve.initial setup context).1)
  have initial : PqxdhServerAuthPublicationGhost.tracked (PqxdhServerAuthCtxReserve.initial setup context).1 =
      (PqxdhServerAuthCtxReserve.initial setup context).1 := rfl
  simpa only [bind_pure_comp, Functor.map_map, initial] using same

/-- The fully sampled actual stopped source obeys the ordinary unconditional-reference capture bound. Every original public callback runs before the publication stop; no conditioned primitive law is introduced. -/
theorem actual_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : AdaptiveCtxReceive.RawDecoder) :
    (Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic (actualClient setup codec checks adversary Q j) none))}[PqxdhServerAuthPublicationGuess.Hit
      (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1]).toReal ≤
      PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j decode
        (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  rw [actual_comparison]
  exact comparison_bound setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j decode

/-- Every reference all-replies certificate bounds the actual stopped source, retaining weighted and mixed cost ledgers. -/
theorem actual_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (budget : Budget)
    (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget)
    (bounded : (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j).IsQueryBound budget canQuery cost) :
    (actualClient setup codec checks adversary Q j).IsQueryBound budget canQuery cost := by
  rw [actual_comparison]
  exact client_budget setup codec checks adversary Q j budget canQuery cost bounded

/-- The actual stopped source retains the complete source context, residual76, callback and KEM/base allowance. This is a dynamic-interface request count, not a zero-runtime claim. -/
theorem actual_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (actualClient setup codec checks adversary Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  exact actual_budget setup codec checks adversary Q j _ _ _
    (PqxdhServerAuthPublicationReferenceResources.client_total setup codec checks caps bounded adversary
      qCoin Q qHash qH coins accepts hashes rom j)

/-- The actual stopped client keeps the sharp one-seal/one-raw certificates and the checked source plaintext allowance. All possible component replies are included. -/
theorem actual_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (actualClient setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (actualClient setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
    AdaptiveCtxDynamicKnownBounds.PlaintextBound (actualClient setup codec checks adversary Q j)
      Aeneas.Std.Usize.max := by
  have original := PqxdhServerAuthPublicationReferenceResources.client_record_bills setup codec checks adversary Q j
  exact ⟨actual_budget setup codec checks adversary Q j _ _ _ original.1,
    actual_budget setup codec checks adversary Q j _ _ _ original.2,
    actual_budget setup codec checks adversary Q j _ _ _
      (PqxdhServerAuthPublicationReferenceBytes.client_plaintext setup codec checks adversary Q j)⟩

/-- Uniform and hash routes retain the explicit original source allowance independently of their distinct primitive reduction overheads. -/
theorem actual_routes (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (actualClient setup codec checks adversary Q j).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
    (actualClient setup codec checks adversary Q j).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have total := actual_total setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.reference_prunes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.reference_prunes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_prunes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_prunes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_capture
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.comparison_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.comparison_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.client_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_comparison
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_routes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationDominance.actual_routes
