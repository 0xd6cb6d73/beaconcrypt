import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceHandlers
import BeaconcryptCore.Computational.PqxdhServerAuthEntryBound

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual selected-output observer pays the complete adaptive source bill, with original capability caps and concrete callbacks; neither success nor a good-state event is assumed. -/
theorem entry_distinguisher_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (entryDistinguisher setup codec checks adversary revealSeed Q j context value).IsTotalQueryBound
      (entryRunBudget caps qCoin Q qHash qH) := by
  simp only [entryDistinguisher, hiddenRun, IsTotalQueryBound, isQueryBound_map_iff]
  apply (hidden_client_uniform setup codec checks context Q j _ caps
    (hidden_handler_uniform setup codec checks context Q j _
      (factor_services_uniform setup codec checks context value) caps bounded)
    _ ![qCoin, Q, qHash, qH] ?_ _ ?_).mono
      (entry_initial_potential setup context caps qCoin Q qHash qH)
  · intro i
    fin_cases i
    · exact coins _
    · exact accepts _
    · exact hashes _
    · exact rom _
  · intro index token found
    cases found

/-- Complete uniform bill for the executable entry reduction, including its real source context and every adaptive callback. Primitive challenger sampling is separate. -/
def entryReductionBudget (caps : KemCaps) (qCoin Q qHash qH : Nat) : Nat :=
  128 + caps.keygenCost + entryRunBudget caps qCoin Q qHash qH

/-- The five concrete key-schedule reductions share this fully discharged observer cap; no opaque source-work premise remains. -/
theorem entry_reduction_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (value : PqxdhServerAuthKeySchedule.Output) :
    (entryReduction setup codec checks adversary revealSeed Q j value).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH) := by
  unfold entryReduction PqxdhServerAuthKeySchedule.withContext entryReductionBudget
  exact isTotalQueryBound_bind (context_uniform setup codec caps bounded)
    (fun context => entry_distinguisher_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom revealSeed j context value)

/-- The complete reduction bill exposes all source sampler, KEM and interpreted base terms. These are uniform oracle counts, not a runtime bound on deterministic public primitives. -/
theorem entry_reduction_budget_expanded (caps : KemCaps) (qCoin Q qHash qH : Nat) :
    entryReductionBudget caps qCoin Q qHash qH =
      256 + qCoin + 160 * Q + 64 * (qHash + qH) +
      caps.keygenUniform + Q * caps.encapsUniform + caps.decapsUniform +
      caps.baseUniform * (caps.keygenBase + Q * caps.encapsBase + caps.decapsBase) :=
  entry_budget_expanded caps qCoin Q qHash qH

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_distinguisher_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_distinguisher_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_reduction_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_reduction_budget_expanded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_reduction_budget_expanded
