import BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry
import BeaconcryptCore.Computational.PqxdhServerAuthEntryReductionResources

/-! Five explicit schedule reductions for an accepted root-erased API observation. These are new distinguishers when the observation changes; the old seal-origin advantages are not reused under another name. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedEntry
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The original flattened source context and real services, with the unchanged public adversary and the new final observation. -/
noncomputable def actualGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ProbComp Bool := do
  let context ← contextSample setup codec
  source setup codec checks adversary revealSeed Q j observer context

/-- The same source context precedes the one selected PRK; public HKDF evaluations stay real. -/
noncomputable def realGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ProbComp Bool := do
  let context ← contextSample setup codec
  let prk ← $ᵗ HmacBlock
  sourceHidden setup codec checks adversary revealSeed Q j observer context prk

/-- One correlated uniform selected schedule is passed to the same complete adaptive observer. -/
noncomputable def uniformGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ProbComp Bool := do
  let context ← contextSample setup codec
  let value ← $ᵗ PqxdhServerAuthKeySchedule.Output
  distinguisher setup codec checks adversary revealSeed Q j observer context value

/-- Source eager sampling and the full journal coupling compose in the actual sampled context. Accepted observations cannot enter either already-excluded refusal branch. -/
theorem source_real_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) :
    RelTriple (actualGame setup codec checks adversary revealSeed Q j observer)
      (realGame setup codec checks adversary revealSeed Q j observer)
      (fun left right => left = true → right = true) := by
  unfold actualGame realGame
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support (contextSample setup codec))
    (relTriple_refl_of_mem_support (contextSample setup codec) fun value member => ⟨rfl, member⟩) ?_
  rintro context _ ⟨rfl, supported⟩
  apply relTriple_of_evalDistEq_left
    (source_prefetched setup codec checks adversary revealSeed Q j observer context)
  refine relTriple_bind (R := Eq) (relTriple_refl ($ᵗ HmacBlock)) ?_
  rintro prk _ rfl
  exact source_hidden_coupling setup codec checks adversary revealSeed Q j observer context supported prk

/-- Explicit ordinary reduction, including the entire real source-context sampler. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : PqxdhServerAuthKeySchedule.Distinguisher :=
  PqxdhServerAuthKeySchedule.withContext (contextSample setup codec)
    (distinguisher setup codec checks adversary revealSeed Q j observer)

/-- The five ordinary component advantages belong to the new constructed observation reduction. Extract uses the actual proved uniform32 samplers; HMAC uses one, one and two challenge calls. -/
noncomputable def scheduleLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ℝ :=
  let D := reduction setup codec checks adversary revealSeed Q j observer
  let R := PqxdhServerAuthKeySchedule.rootExpandReduction setup.source D
  let I := PqxdhServerAuthKeySchedule.initExtractReduction setup.source setup.hmac D
  let E := PqxdhServerAuthKeySchedule.initExpandReduction setup.source D
  let S := PqxdhServerAuthKeySchedule.stepExtractReduction setup.hmac D
  let T := PqxdhServerAuthKeySchedule.stepExpandReduction D
  (hmacPrfRealGame setup.hmac R).boolDistance (hmacPrfRandomGame R) +
    (extractRealGame setup.hmac PqxdhServerAuthKeySchedule.uniform32 I).boolDistance
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32 I) +
    (hmacPrfRealGame setup.hmac E).boolDistance (hmacPrfRandomGame E) +
    (extractRealGame setup.hmac PqxdhServerAuthKeySchedule.uniform32 S).boolDistance
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32 S) +
    (hmacPrfRealGame setup.hmac T).boolDistance (hmacPrfRandomGame T)

/-- Adjacent schedule hybrids use the same complete public journal and correlated callbacks. The sole functional premise is the existing full Extract/Expand source-wiring contract. -/
theorem real_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (correct : SourceFullCorrect setup.source setup.hmac) :
    (realGame setup codec checks adversary revealSeed Q j observer).boolDistance
      (uniformGame setup codec checks adversary revealSeed Q j observer) ≤
        scheduleLoss setup codec checks adversary revealSeed Q j observer := by
  simpa only [realGame, uniformGame, source_factor, scheduleLoss, reduction] using
    PqxdhServerAuthKeySchedule.keySchedule_bound_context setup.source setup.hmac correct
      (contextSample setup codec) (distinguisher setup codec checks adversary revealSeed Q j observer)

/-- Accepted source observations have the same selected-coordinate loss, with no additional raw-attempt or session guessing factor. The enclosing owner partition is separate. -/
theorem source_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[actualGame setup codec checks adversary revealSeed Q j observer] {true}).toReal ≤
      (𝒟[uniformGame setup codec checks adversary revealSeed Q j observer] {true}).toReal +
        scheduleLoss setup codec checks adversary revealSeed Q j observer := by
  have original := ENNReal.toReal_mono
    (MeasureTheory.measure_ne_top (𝒟[realGame setup codec checks adversary revealSeed Q j observer]) {true})
    (bool_probability_le (source_real_coupling setup codec checks adversary revealSeed Q j observer))
  have gap := (abs_le.mp (real_uniform setup codec checks adversary revealSeed Q j observer correct)).2
  linarith

open PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts

/-- The actual journal observer pays every original adaptive callback and interpreter bill. The four caps are those of the original adversary, including rejected queries. -/
theorem observer_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (observer : Observer) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (distinguisher setup codec checks adversary revealSeed Q j observer context value).IsTotalQueryBound
      (entryRunBudget caps qCoin Q qHash qH) := by
  simp only [distinguisher, PqxdhServerAuthObservedEntry.hidden, IsTotalQueryBound, isQueryBound_map_iff]
  apply (hidden_client_uniform setup codec checks context Q j _ caps
    (hidden_handler_uniform setup codec checks context Q j _
      (factor_services_uniform setup codec checks context value) caps bounded)
    _ ![qCoin, Q, qHash, qH] ?_ _ ?_).mono
      (entry_initial_potential setup context caps qCoin Q qHash qH)
  · intro i
    apply (PqxdhServerAuthApiJournal.query_bound _ _ _).mpr
    fin_cases i
    · exact coins _
    · exact accepts _
    · exact hashes _
    · exact rom _
  · intro index token found
    cases found

/-- The constructed reduction includes the actual context generation and complete base/KEM bill. There is no opaque observer-cost premise. -/
theorem reduction_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (observer : Observer) (value : PqxdhServerAuthKeySchedule.Output) :
    (reduction setup codec checks adversary revealSeed Q j observer value).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH) := by
  unfold reduction PqxdhServerAuthKeySchedule.withContext entryReductionBudget
  exact isTotalQueryBound_bind (context_uniform setup codec caps bounded)
    (fun context => observer_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j observer context value)

/-- All five newly constructed component games have explicit challenge, reduction-uniform and challenger-uniform bills derived from the original source caps. -/
theorem component_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (observer : Observer) :
    EntryComponentBills setup.source setup.hmac
      (reduction setup codec checks adversary revealSeed Q j observer)
      (entryReductionBudget caps qCoin Q qHash qH) :=
  entry_component_bills setup.source setup.hmac _ _
    (reduction_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j observer)

end BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.source_real_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.source_real_coupling

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.real_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.real_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.source_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.observer_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.reduction_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.component_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule.component_bills
