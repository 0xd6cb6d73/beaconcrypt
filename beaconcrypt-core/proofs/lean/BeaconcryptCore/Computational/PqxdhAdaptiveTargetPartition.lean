import BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost
import BeaconcryptCore.Computational.RawCtxSelectiveTargets

/-!
A final optional target partitions one common source execution. The identity is exact and charges no oracle call. It does not assert that separately randomized target experiments are one globally randomized experiment.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition
open PqxdhAdaptiveTargetPost
variable {Choice : Type} [Fintype Choice] [DecidableEq Choice]

def wins (result : Decision Choice) : Bool := result.1.isSome && result.2

/-- The adaptive success event is the disjoint union of its actual final target choices. -/
theorem partition (game : ProbComp (Decision Choice)) :
    Pr[= true | wins <$> game] = ∑ selected, Pr[= true | choose selected <$> game] := by
  have identity := RawCtxSelectiveTargets.event_partition game Prod.fst (fun _ result => result.2 = true)
  have any : ∀ result : Decision Choice, wins result = true ↔
      RawCtxSelectiveTargets.anyEvent Prod.fst (fun _ result => result.2 = true) result := by
    intro result
    cases chosen : result.1 <;> simp [wins, RawCtxSelectiveTargets.anyEvent, RawCtxSelectiveTargets.selectedEvent, chosen]
  have predicate : (fun result : Decision Choice => wins result = true) =
      RawCtxSelectiveTargets.anyEvent Prod.fst (fun _ result => result.2 = true) := funext fun result => propext (any result)
  simp only [← probEvent_eq_eq_probOutput, probEvent_map, choose, Bool.and_eq_true, decide_eq_true_eq, Function.comp_def]
  rw [predicate, identity]
  rfl

/-- Real-valued success probabilities inherit the same exact finite partition. -/
theorem partition_real (game : ProbComp (Decision Choice)) :
    Pr[= true | wins <$> game].toReal = ∑ selected, Pr[= true | choose selected <$> game].toReal := by
  rw [partition, ENNReal.toReal_sum]
  intro selected _
  exact probOutput_ne_top

end BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition.partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition.partition
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition.partition_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition.partition_real
