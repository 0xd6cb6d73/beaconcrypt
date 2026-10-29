-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBound

/-! The final observer may evaluate symbolic descriptors using the candidate after the candidate-free client has finished. The joint candidate/value law therefore retains the same key-query guessing bound; candidate blindness is required only of the executing oracle client, not of the final analysis predicate. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation
open RegistrationNativeSecretWord (Spec IsKey symbolic actual)
open RegistrationNativeSecretWordTrace (values run fixed_distance guess_bound)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {Value Observation : Type}
attribute [local irreducible] uniformSample

noncomputable def symbolicView (observe : MlKemSharedSecret → Value → Observation) (work : OracleComp Spec Value) : ProbComp Observation := do
  let candidate ← $ᵗ MlKemSharedSecret
  observe candidate <$> values symbolic work

noncomputable def bytesView (observe : MlKemSharedSecret → Value → Observation) (work : OracleComp Spec Value) : ProbComp Observation := do
  let candidate ← $ᵗ MlKemSharedSecret
  observe candidate <$> (simulateQ (RegistrationNativeSecretWordSource.byteSource candidate) work).run' ∅

/-- Every common final observer, including the full candidate/value pair, has the same coefficient-one literal collision bound. -/
theorem observed_close (observe : MlKemSharedSecret → Value → Observation) (work : OracleComp Spec Value)
    (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    ENNReal.ofReal (discreteDistance (symbolicView observe work) (bytesView observe work)) ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have averaged := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ MlKemSharedSecret)
    (fun candidate => observe candidate <$> values symbolic work)
    (fun candidate => observe candidate <$> values (actual candidate) work)
    (fun _ => run work) (fun candidate result => candidate ∈ result.2.2)
    (fun candidate _ => (discreteDistance_map_le (observe candidate) _ _).trans (fixed_distance candidate work))
  have source : (do let candidate ← $ᵗ MlKemSharedSecret; observe candidate <$> values (actual candidate) work) = bytesView observe work := by
    apply bind_congr
    intro candidate
    rw [values, RegistrationNativeSecretWordSource.values_source]
  rw [source] at averaged
  exact (ENNReal.ofReal_le_ofReal averaged).trans
    ((ENNReal.ofReal_toReal (prEvent_ne_top _)).le.trans (guess_bound work cap bounded))

/-- Candidate-dependent final events retain the same bound without an extra hidden-suffix assumption. -/
theorem event_bound (observe : MlKemSharedSecret → Value → Observation) (work : OracleComp Spec Value)
    (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) (event : Observation → Prop) :
    Pr{let result ← bytesView observe work}[event result] ≤
      Pr{let result ← symbolicView observe work}[event result] + cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have compared := prEvent_le_prEvent_add_ofReal_discreteDistance (bytesView observe work) (symbolicView observe work) event
  rw [discreteDistance_comm] at compared
  exact compared.trans (add_le_add le_rfl (observed_close observe work cap bounded))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation.observed_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation.observed_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation.event_bound
