import BeaconcryptCore.Computational.PqxdhServerAuthStopBudget

section SourceResourcesSection

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The stopped actual source retains the complete original uniform bill, including the full second accept before refusal. All original adversary classes and concrete KEM/base costs remain explicit. -/
theorem stopped_source_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (value : PqxdhServerAuthKeySchedule.Output) {Result : Type} (client : OracleComp ServerAuthSpec Result)
    (budget : Fin 4 → Nat) (queries : ∀ i, client.IsQueryBoundP (entryClasses i) (budget i))
    (state : HiddenState KemSK × Option Nat) (valid : ResourceValid state.1.1.1) :
    (((simulateQ (sourceStopped setup codec checks context Q j (factorServices setup codec checks context value)) client).run).run state).IsTotalQueryBound
      (entryPotential caps budget state.1.1.1) := by
  rw [← isQueryBoundP_true_iff]
  apply optional_potential_invariant _ (fun state => ResourceValid state.1.1.1) entryClasses (fun _ => True)
    (fun budget state => entryPotential caps budget state.1.1.1) ?_ client budget queries state valid
  intro query before available invariant positive
  rcases before with ⟨before, first⟩
  refine ⟨entryBill caps query before.1.1, ?_, entryBill_le caps query before.1.1 invariant available positive, ?_⟩
  · rw [sourceStopped_step]
    have services : tableServices setup context (factorServices setup codec checks context value) =
        factorServices setup codec checks context value := rfl
    simp only [isQueryBoundP_map_iff, services]
    exact (hidden_handler_uniform setup codec checks context Q j _
      (factor_services_uniform setup codec checks context value) caps bounded query before).isQueryBoundP
  · intro result supported answer continues
    rw [sourceStopped_step] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨original, originalSupported, rfl⟩ := supported
    have footprint := hiddenHandler_resources setup codec checks context Q j _ query before original originalSupported
    exact ⟨ResourceStep.valid query before.1.1 original.2.1.1 invariant footprint,
      entry_potential_step caps query before.1.1 original.2.1.1 invariant footprint available positive⟩

/-- The literal stopped entry observer retains B8b's fully discharged source bill on every path, with no ambient-work or good-event premise. -/
theorem stopped_distinguisher_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (stoppedEntryDistinguisher setup codec checks adversary revealSeed Q j context value).IsTotalQueryBound
      (entryRunBudget caps qCoin Q qHash qH) := by
  simp only [stoppedEntryDistinguisher, IsTotalQueryBound, isQueryBound_map_iff]
  apply (stopped_source_uniform setup codec checks caps bounded context Q j value
    (adversary (contextInput setup revealSeed context)) ![qCoin, Q, qHash, qH] ?_
    (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none) ?_).mono
      (entry_initial_potential setup context caps qCoin Q qHash qH)
  · intro i
    fin_cases i
    · exact coins _
    · exact accepts _
    · exact hashes _
    · exact rom _
  · intro index token found
    cases found

set_option maxRecDepth 10000 in
/-- The complete joint output sampler costs 108 byte draws; its correlated projections are never sampled independently here. -/
theorem factor_uniform : ($ᵗ PqxdhServerAuthKeySchedule.Output : ProbComp PqxdhServerAuthKeySchedule.Output).IsTotalQueryBound 108 := by
  simp only [← PqxdhFullSecretInputKdf.pairSample]
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
    (fun step => isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun other => show (pure (step, other) : ProbComp PqxdhServerAuthKeySchedule.Output).IsTotalQueryBound 0 from by trivial))

/-- The complete stopped uniform entry game pays the actual context, every source callback and the full joint108 challenge. The selected-key-first compiler later separates32 challenger bytes and76 residual bytes without changing this total. -/
theorem stopped_entry_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (revealSeed : Bool) (j : Fin (Q + 1)) :
    (stoppedEntryGame setup codec checks adversary revealSeed Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 108) := by
  unfold stoppedEntryGame
  have combined := isTotalQueryBound_bind (context_uniform setup codec caps bounded)
    (fun context => isTotalQueryBound_bind factor_uniform
      (fun value => stopped_distinguisher_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
        coins accepts hashes rom revealSeed j context value))
  exact combined.mono (by unfold entryReductionBudget; omega)

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end SourceResourcesSection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_source_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_distinguisher_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_distinguisher_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.factor_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.factor_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_entry_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_entry_uniform
