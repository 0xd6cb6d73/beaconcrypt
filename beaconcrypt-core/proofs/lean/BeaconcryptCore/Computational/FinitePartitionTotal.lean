import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-! Selective bounds for a complete finite request partition imply an explicit total request count. This accounting theorem retains every possible oracle reply. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.FinitePartitionTotal

/-- Summing the selective request bounds charges every original request once. -/
theorem bound {ι Kind Value : Type} {spec : OracleSpec ι} [Fintype Kind] [DecidableEq Kind]
    (classify : spec.Domain → Kind) (client : OracleComp spec Value) (budget : Kind → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    client.IsTotalQueryBound (FinitePartitionQueryBounds.bill (fun _ => 1) budget) := by
  refine IsQueryBound.proj (FinitePartitionQueryBounds.bill (fun _ => 1)) ?_ ?_
    (FinitePartitionQueryBounds.structural classify client budget bounded)
  all_goals intro query current positive
  all_goals have exactBill := FinitePartitionQueryBounds.bill_step (fun _ => 1) current (classify query) positive
  all_goals omega

end BeaconcryptCore.Computational.FinitePartitionTotal

/-- info: 'BeaconcryptCore.Computational.FinitePartitionTotal.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.FinitePartitionTotal.bound
