import BeaconcryptCore.Computational.PqxdhServerAuthEntryAccept
import BeaconcryptCore.Computational.PqxdhServerAuthEntryFinish
import BeaconcryptCore.Computational.PqxdhServerAuthEntryServices

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every original adversary operation has a checked complete-state coupling; there is no interface callback premise. -/
theorem hidden_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (query : ServerAuthSpec.Domain) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk query).run left)
      ((hiddenHandler setup codec checks context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk)) query).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  cases query with
  | inl coin => exact coin_step_coupling setup codec checks context Q j prk _ coin left right related
  | inr query =>
      cases query with
      | accept raw => exact accept_step_coupling setup codec checks context Q j prk raw left right related
      | build session payload => exact build_step_coupling setup codec checks context Q j prk session payload left right related
      | finish raw => exact finish_step_coupling setup codec checks context Q j prk raw left right related
      | hmac key message => exact hmac_step_coupling setup codec checks context Q j prk _ rfl key message left right related
      | hash bytes => exact hash_step_coupling setup codec checks context Q j prk _ bytes left right related
      | reveal keyId => exact reveal_step_coupling setup codec checks context Q j prk _ keyId left right related

/-- The complete unchanged adaptive client preserves all source state until the refusal already excluded by the original event. Both runs continue with their exact own replies after refusal; no scheduling restriction is introduced. -/
theorem hidden_client_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    {Result : Type} (client : OracleComp ServerAuthSpec Result)
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((simulateQ (prefetchedHandler setup codec checks context Q j prk) client).run left)
      ((simulateQ (hiddenHandler setup codec checks context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))) client).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  exact relTriple_until_bad _ _ _ _ _
    (prefetchedStep_bad setup codec checks context Q j prk)
    (hiddenHandler_bad setup codec checks context Q j _)
    (hidden_step_coupling setup codec checks context Q j prk) client left right (Or.inl related)

/-- Complete final source and omitted-entry states are coupled from the literal context sampler, with no honest-target, cache-miss or successful-opening premise. -/
theorem hidden_run_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (supported : context ∈ support (contextSample setup codec)) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) :
    RelTriple (prefetchedRun setup codec checks adversary revealSeed context Q j prk)
      (hiddenRun setup codec checks adversary revealSeed context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk)))
      (fun left right => EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right ∨
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j left ∧ right.1.2.2.bad = true)) := by
  simp only [prefetchedRun, hiddenRun]
  apply relTriple_map
  apply relTriple_post_mono (hidden_client_coupling setup codec checks context Q j prk _ _ _
    (EntryRel.initial setup codec context supported Q j prk))
  intro left right post
  exact post.elim (fun good => Or.inl good.2) Or.inr

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The original per-entry decision on the complete prefetched source execution. -/
noncomputable def prefetchedDecision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (prk : HmacBlock) : ProbComp Bool := by
  classical
  exact (fun state => decide (EntryEvent setup context.seed context.scalar Q j state.1.1.ghost)) <$>
    prefetchedRun setup codec checks adversary revealSeed context Q j prk

/-- The actual source event implies the nonrefused factored event under the complete-run coupling. Refused source executions cannot win the original event, so this adds no error term. -/
theorem hidden_decision_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (supported : context ∈ support (contextSample setup codec)) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) :
    RelTriple (prefetchedDecision setup codec checks adversary revealSeed Q j context prk)
      (sourceHiddenDecision setup codec checks adversary revealSeed Q j context prk)
      (fun left right => left = true → right = true) := by
  classical
  simp only [prefetchedDecision, sourceHiddenDecision]
  apply relTriple_map
  apply relTriple_post_mono (hidden_run_coupling setup codec checks adversary revealSeed context supported Q j prk)
  intro left right post event
  have won : EntryEvent setup context.seed context.scalar Q j left.1.1.ghost := of_decide_eq_true event
  rcases post with related | bad
  · exact decide_eq_true ⟨related.good, (ProtocolRel.entry setup context.seed context.scalar Q j _ _ _ _ related.protocol).mp won⟩
  · exact (entry_not_selectedBad setup context.seed context.scalar (context.publicValue setup) Q j left.1.1
      bad.1.1.1 won bad.1.2).elim

/-- A Boolean event implication under a complete coupling bounds its true probability with coefficient one. -/
theorem bool_probability_le {left right : ProbComp Bool}
    (coupled : RelTriple left right (fun a b => a = true → b = true)) :
    𝒟[left] {true} ≤ 𝒟[right] {true} := by
  have bound := probEvent_le_of_relTriple coupled (p := fun bit => bit = true) (q := fun bit => bit = true)
    (fun _ _ implication => implication)
  simpa only [← evalDist_apply_setOf, Set.ofPred_eq_eq_singleton] using bound

/-- Source and factored per-context success probabilities are related without a statistical or guessing loss. -/
theorem prefetched_decision_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (supported : context ∈ support (contextSample setup codec)) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) :
    𝒟[prefetchedDecision setup codec checks adversary revealSeed Q j context prk] {true} ≤
      𝒟[sourceHiddenDecision setup codec checks adversary revealSeed Q j context prk] {true} :=
  bool_probability_le (hidden_decision_coupling setup codec checks adversary revealSeed context supported Q j prk)

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The complete prefetched source decision, with the real context sampled before its one designated block. -/
noncomputable def prefetchedEntryDecisionGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ProbComp Bool := do
  let context ← contextSample setup codec
  let prk ← $ᵗ HmacBlock
  prefetchedDecision setup codec checks adversary revealSeed Q j context prk

/-- Full sampled source-to-factor coupling. The context and all challenge-independent source randomness retain their original order. -/
theorem sampled_decision_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    RelTriple (prefetchedEntryDecisionGame setup codec checks adversary revealSeed Q j)
      (realEntryGame setup codec checks adversary revealSeed Q j)
      (fun left right => left = true → right = true) := by
  unfold prefetchedEntryDecisionGame realEntryGame
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support (contextSample setup codec))
    (relTriple_refl_of_mem_support (contextSample setup codec) fun value member => ⟨rfl, member⟩) ?_
  rintro context _ ⟨rfl, supported⟩
  refine relTriple_bind (R := Eq) (relTriple_refl ($ᵗ HmacBlock)) ?_
  rintro prk _ rfl
  exact hidden_decision_coupling setup codec checks adversary revealSeed context supported Q j prk


/-- The unchanged authentication event at the original source endpoint. -/
noncomputable def actualEntryGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ProbComp Bool := by
  classical
  exact (fun result => decide (EntryEvent setup result.1 result.2.1 Q j result.2.2.1.ghost)) <$>
    gameState setup codec checks revealSeed adversary

/-- The complete prefetched Boolean game is exactly the original entry predicate mapped over its retained state game. -/
theorem prefetched_decision_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    prefetchedEntryDecisionGame setup codec checks adversary revealSeed Q j =
      (fun result => @decide (EntryEvent setup result.1.seed result.1.scalar Q j result.2.1.1.ghost)
        (Classical.propDecidable _)) <$> prefetchedGame setup codec checks adversary revealSeed Q j := by
  simp only [prefetchedEntryDecisionGame, prefetchedDecision, prefetchedGame, map_bind,
    bind_pure_comp, Functor.map_map]


/-- Eager sampling dominates the original source event without selecting an honest target or conditioning on successful derivation. -/
theorem actual_le_prefetched_decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    𝒟[actualEntryGame setup codec checks adversary revealSeed Q j] {true} ≤
      𝒟[prefetchedEntryDecisionGame setup codec checks adversary revealSeed Q j] {true} := by
  classical
  rw [prefetched_decision_map]
  simpa only [actualEntryGame, evalDist_apply_singleton, probOutput_map, decide_eq_true_eq] using
    entry_le_prefetched setup codec checks adversary revealSeed Q j


/-- The original source event is bounded by the concrete real key-schedule game with coefficient one, for every adaptive adversary and every selected operation. -/
theorem actual_le_real_entry (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    𝒟[actualEntryGame setup codec checks adversary revealSeed Q j] {true} ≤
      𝒟[realEntryGame setup codec checks adversary revealSeed Q j] {true} :=
  le_trans (actual_le_prefetched_decision setup codec checks adversary revealSeed Q j)
    (bool_probability_le (sampled_decision_coupling setup codec checks adversary revealSeed Q j))

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The explicit ordinary key-schedule distinguisher: sample the actual source context, then run its complete adaptive protocol interpreter with the supplied joint output. -/
noncomputable def entryReduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    PqxdhServerAuthKeySchedule.Distinguisher :=
  PqxdhServerAuthKeySchedule.withContext (contextSample setup codec)
    (entryDistinguisher setup codec checks adversary revealSeed Q j)

/-- The five constructed component advantages for this actual entry reduction. The Extract endpoints use the established uniform 32-byte sampler, while the three PRF endpoints expose one, one and two challenge queries. -/
noncomputable def entryScheduleLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) : ℝ :=
  let D := entryReduction setup codec checks adversary revealSeed Q j
  let R := PqxdhServerAuthKeySchedule.rootExpandReduction setup.source D
  let I := PqxdhServerAuthKeySchedule.initExtractReduction setup.source setup.hmac D
  let E := PqxdhServerAuthKeySchedule.initExpandReduction setup.source D
  let S := PqxdhServerAuthKeySchedule.stepExtractReduction setup.hmac D
  let T := PqxdhServerAuthKeySchedule.stepExpandReduction D
  (hmacPrfRealGame setup.hmac R).boolDistAdvantage (hmacPrfRandomGame R) +
    (extractRealGame setup.hmac PqxdhServerAuthKeySchedule.uniform32 I).boolDistAdvantage
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32 I) +
    (hmacPrfRealGame setup.hmac E).boolDistAdvantage (hmacPrfRandomGame E) +
    (extractRealGame setup.hmac PqxdhServerAuthKeySchedule.uniform32 S).boolDistAdvantage
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32 S) +
    (hmacPrfRealGame setup.hmac T).boolDistAdvantage (hmacPrfRandomGame T)

/-- The actual full-run key-schedule transition uses the five B8a reductions, with no protocol security hypothesis or honest-target premise. SourceFullCorrect is the permanent functional Extract/Expand wiring contract. -/
theorem real_uniform_entry_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (realEntryGame setup codec checks adversary revealSeed Q j).boolDistAdvantage
      (uniformEntryGame setup codec checks adversary revealSeed Q j) ≤
        entryScheduleLoss setup codec checks adversary revealSeed Q j := by
  simpa only [realEntryGame, uniformEntryGame, source_hidden_factor, entryScheduleLoss, entryReduction] using
    PqxdhServerAuthKeySchedule.keySchedule_bound_context setup.source setup.hmac correct
      (contextSample setup codec) (entryDistinguisher setup codec checks adversary revealSeed Q j)


/-- Per-entry authentication after replacing the complete correlated selected key schedule. All five advantages belong to explicit reductions built from the same original adaptive adversary. This statement adds no selection factor; summing over entries is a separate enclosing step. -/
theorem entry_le_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[actualEntryGame setup codec checks adversary revealSeed Q j] {true}).toReal ≤
      (𝒟[uniformEntryGame setup codec checks adversary revealSeed Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary revealSeed Q j := by
  have original := ENNReal.toReal_mono
    (MeasureTheory.measure_ne_top (𝒟[realEntryGame setup codec checks adversary revealSeed Q j]) {true})
    (actual_le_real_entry setup codec checks adversary revealSeed Q j)
  have bound := real_uniform_entry_bound setup codec checks adversary revealSeed Q j correct
  have gap := (abs_le.mp bound).2
  linarith


/-- Exact challenge-interface caps of the three constructed PRF reductions. These counts exclude ordinary source coins and primitive work, which have separate concrete bills. -/
theorem entry_prf_query_bounds (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    let D := entryReduction setup codec checks adversary revealSeed Q j
    (PqxdhServerAuthKeySchedule.rootExpandReduction setup.source D).IsQueryBoundP IsHmacChallengeQuery 1 ∧
    (PqxdhServerAuthKeySchedule.initExpandReduction setup.source D).IsQueryBoundP IsHmacChallengeQuery 1 ∧
    (PqxdhServerAuthKeySchedule.stepExpandReduction D).IsQueryBoundP IsHmacChallengeQuery 2 :=
  ⟨PqxdhServerAuthKeySchedule.rootExpandReduction_query_bound setup.source _,
    PqxdhServerAuthKeySchedule.initExpandReduction_query_bound setup.source _,
    PqxdhServerAuthKeySchedule.stepExpandReduction_query_bound _⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_client_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_client_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_run_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_run_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_decision_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_decision_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.bool_probability_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.bool_probability_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetched_decision_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetched_decision_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.sampled_decision_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.sampled_decision_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetched_decision_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetched_decision_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_le_prefetched_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_le_prefetched_decision
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_le_real_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.actual_le_real_entry
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.real_uniform_entry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.real_uniform_entry_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_le_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_le_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_prf_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_prf_query_bounds
