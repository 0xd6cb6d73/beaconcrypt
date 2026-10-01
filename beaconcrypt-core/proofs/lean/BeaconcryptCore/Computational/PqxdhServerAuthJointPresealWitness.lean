import BeaconcryptCore.Computational.PqxdhServerAuthJointWitness
import BeaconcryptCore.Computational.PqxdhServerAuthPresealControl

/-! The separate actual pre-seal reveal control succeeds on the same explicitly insecure functional witness used by the class/spread, seed-reveal and honest-relay controls. No production primitive security claim is made. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness
open PqxdhServerAuthJointWitness PqxdhServerAuthExperiment
open PqxdhServerAuthNegativeControl

/-- The actual control's functional and abstract message laws hold on the existing joint witness, with the concrete public size limit one hundred. -/
theorem actual_control_laws : ControlLaws setup codec 100 := control_laws 100

/-- The concrete attack first requests payload one, then uses the separately revealed actual old chain to reseal payload two. -/
noncomputable def client : Adversary := PqxdhServerAuthPresealControl.adversary setup codec [1] [2]

/-- The separate control uses the original authentication decision on its actual source execution, with accepting allocation checks. -/
noncomputable def game : ProbComp Bool := PqxdhServerAuthPresealControl.presealGame setup codec acceptAll client

/-- The concrete separate pre-seal control succeeds with probability at least one on the same witness; all liveness and functional premises are discharged. -/
theorem success_lower : 1 ≤ (𝒟[game] {true}).toReal := by
  have lower := PqxdhServerAuthPresealControl.preseal_reveal_control setup codec 100 actual_control_laws
    PqxdhHypothesisWitness.toyFunctional [1] [2] (by decide) (by decide) (by decide)
    (by simp; scalar_tac) (by decide) (by decide) (by decide)
  simpa only [kem_error, sub_zero, game, client, evalDist_apply_singleton] using lower

/-- The separate original authentication decision succeeds with probability exactly one on the joint witness. -/
theorem success : (𝒟[game] {true}).toReal = 1 := by
  have upper : 𝒟[game] {true} ≤ 1 := by
    rw [evalDist_apply_singleton]
    exact probOutput_le_one
  exact le_antisymm (by simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_mono ENNReal.one_ne_top upper)) success_lower

/-- The same concrete source execution is observed at its original wrong-payload authentication event. -/
noncomputable def wrongPayloadGame : ProbComp Bool := by
  classical
  exact (fun result => decide (W2 setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    PqxdhServerAuthPresealControl.controlState setup codec acceptAll client

/-- The attack specifically reaches the original wrong-payload event with probability one; it does not merely win an unspecified authentication disjunct. -/
theorem wrong_payload : (𝒟[wrongPayloadGame] {true}).toReal = 1 := by
  classical
  have lower := PqxdhServerAuthPresealControl.preseal_control setup codec 100 actual_control_laws
    PqxdhHypothesisWitness.toyFunctional [1] [2] (by decide) (by decide) (by decide)
    (by simp; scalar_tac) (by decide) (by decide) (by decide)
  have actual : 1 ≤ (𝒟[wrongPayloadGame] {true}).toReal := by
    simpa only [wrongPayloadGame, client, evalDist_apply_singleton, probOutput_map,
      decide_eq_true_eq, kem_error, sub_zero] using lower
  have upper : 𝒟[wrongPayloadGame] {true} ≤ 1 := by
    rw [evalDist_apply_singleton]
    exact probOutput_le_one
  exact le_antisymm (by simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_mono ENNReal.one_ne_top upper)) actual

/-- The concrete same-witness attack uses at most one accept and commitment-hash request and no public HMAC query on every adversary input. -/
theorem query_budget : AuthBudget client 1 0 1 :=
  PqxdhServerAuthPresealControl.adversary_budget setup codec [1] [2]

/-- All adaptive reply paths retain the separate API ledger: one accept, build, altered reveal, public commitment hash and finish, with zero explicit coins or public HMAC calls. -/
theorem query_classes (input : AuthInput) (category : PqxdhServerAuthPresealControl.ApiClass) :
    (client input).IsQueryBoundP (PqxdhServerAuthPresealControl.HasClass category)
      (match category with | .coin | .hmac => 0 | _ => 1) :=
  PqxdhServerAuthPresealControl.adversary_classes setup codec [1] [2] input category

/-- The complete concrete adversary makes at most five public API calls, including every optional rejection branch. This does not count source or challenger work as free. -/
theorem query_total (input : AuthInput) : (client input).IsTotalQueryBound 5 :=
  PqxdhServerAuthPresealControl.adversary_total setup codec [1] [2] input

end BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.actual_control_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.actual_control_laws

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.success_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.success_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.success

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.wrong_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.wrong_payload

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_classes

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointPresealWitness.query_total

