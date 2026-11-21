-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSource

/-! An arbitrary candidate-free symbolic client and the actual192-byte lazy table differ by at most one uniform32-byte literal-guessing term per original key query. Later adaptive literals are included because the entire symbolic execution, including all its random replies, is independent of the candidate. Applying this theorem to a concrete native frontend still requires a proved candidate-free language translation. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBound
open RegistrationNativeSecretWord (Spec IsKey symbolic actual)
open RegistrationNativeSecretWordTrace (values run fixed_distance guess_bound)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {Value : Type}
attribute [local irreducible] uniformSample

noncomputable def normalized (work : OracleComp Spec Value) : ProbComp Value := do
  let candidate ← $ᵗ MlKemSharedSecret
  values (actual candidate) work

noncomputable def bytes (work : OracleComp Spec Value) : ProbComp Value := do
  let candidate ← $ᵗ MlKemSharedSecret
  (simulateQ (RegistrationNativeSecretWordSource.byteSource candidate) work).run' ∅

/-- The exact actual192-byte service is the normalized symbolic service, including arbitrary repeated atom and literal keys. -/
theorem bytes_source (work : OracleComp Spec Value) : bytes work = normalized work := by
  unfold bytes normalized
  apply bind_congr
  intro candidate
  exact (RegistrationNativeSecretWordSource.values_source candidate work).symm

/-- The complete returned-value laws differ by at most the actual syntactic key allowance over the uniform32-byte space. -/
theorem normalized_close (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    ENNReal.ofReal (discreteDistance (values symbolic work) (normalized work)) ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace Value := ⊤
  have averaged := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ MlKemSharedSecret)
    (fun _ => values symbolic work) (fun candidate => values (actual candidate) work)
    (fun _ => run work) (fun candidate result => candidate ∈ result.2.2)
    (fun candidate _ => fixed_distance candidate work)
  have dropped : ($ᵗ MlKemSharedSecret >>= fun _ => values symbolic work) =ᵈ values symbolic work :=
    EvalDistEq.of_evalDist_eq ((LazyOracleDiscard.lawEq_drop ($ᵗ MlKemSharedSecret) (values symbolic work)).evalDist_eq)
  have distance := discreteDistance_congr dropped (EvalDistEq.refl (normalized work))
  change discreteDistance ($ᵗ MlKemSharedSecret >>= fun _ => values symbolic work) (normalized work) ≤ _ at averaged
  rw [distance] at averaged
  exact (ENNReal.ofReal_le_ofReal averaged).trans
    ((ENNReal.ofReal_toReal (prEvent_ne_top _)).le.trans (guess_bound work cap bounded))

/-- The same bound applies directly to the real byte-indexed lazy table, with no assumed alias or simulation event. -/
theorem bytes_close (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    ENNReal.ofReal (discreteDistance (values symbolic work) (bytes work)) ≤ cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  rw [bytes_source]
  exact normalized_close work cap bounded

/-- Every event of the actual returned value is transported with the same coefficient-one literal-guessing loss. -/
theorem event_bound (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap)
    (event : Value → Prop) :
    Pr{let result ← bytes work}[event result] ≤
      Pr{let result ← values symbolic work}[event result] + cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have eventClose := prEvent_le_prEvent_add_ofReal_discreteDistance (bytes work) (values symbolic work) event
  rw [discreteDistance_comm] at eventClose
  exact eventClose.trans (add_le_add le_rfl (bytes_close work cap bounded))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.bytes_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.bytes_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.normalized_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.normalized_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.bytes_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.bytes_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBound.event_bound
