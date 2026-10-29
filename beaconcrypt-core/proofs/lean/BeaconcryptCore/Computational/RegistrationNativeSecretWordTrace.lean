-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWord

/-! The literal-suffix trace is sampled by the candidate-free symbolic table client. Its syntactic key cap controls every reached list, including retries and aliases. Only the later deferred comparison reads the uniform candidate. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace
open RegistrationNativeSecretWord (Spec Cache IsKey literals symbolic actual)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {Value : Type}

noncomputable def run (work : OracleComp Spec Value) : ProbComp (Value × (Cache × List MlKemSharedSecret)) :=
  (simulateQ (RawCtxSelectedQueryTrace.recorded symbolic literals) work).run (∅, [])

noncomputable def values (implementation : QueryImpl Spec (StateT Cache ProbComp))
    (work : OracleComp Spec Value) : ProbComp Value := (simulateQ implementation work).run' ∅

private theorem literal_length (query : Spec.Domain) : (literals query).length ≤ if IsKey query then 1 else 0 := by
  cases query with
  | inl coin => simp [literals, IsKey]
  | inr key => rcases key with ⟨head, word⟩; cases word <;> simp [literals, IsKey]

/-- Every supported original symbolic execution records at most its syntactic key allowance, regardless of adaptive replies. -/
theorem length_bound (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap)
    (result : Value × (Cache × List MlKemSharedSecret)) (supported : result ∈ support (run work)) :
    result.2.2.length ≤ cap := by
  simpa only [List.length_nil, Nat.zero_add] using RawCtxSelectedQueryTrace.length_bound symbolic literals IsKey
    literal_length work cap bounded (∅, []) result supported

private theorem trace_values (implementation : QueryImpl Spec (StateT Cache ProbComp))
    (work : OracleComp Spec Value) :
    Prod.fst <$> (simulateQ (RawCtxSelectedQueryTrace.recorded implementation literals) work).run (∅, []) =
      values implementation work := by
  have erased := congrArg (Functor.map Prod.fst)
    (RawCtxSelectedQueryTrace.complete implementation literals work (∅, []))
  simpa only [values, StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq] using erased

/-- The normalized actual table and the symbolic table differ only by a candidate literal in this same execution's full trace. -/
theorem fixed_distance (candidate : MlKemSharedSecret) (work : OracleComp Spec Value) :
    discreteDistance (values symbolic work) (values (actual candidate) work) ≤
      (Pr{let result ← run work}[candidate ∈ result.2.2]).toReal := by
  have compared := RawCtxSelectedAliasCoupling.recorded_distance symbolic (actual candidate) literals candidate work (∅ : Cache)
  rw [RegistrationNativeSecretWord.actual_routed] at compared
  have mapped := (discreteDistance_map_le Prod.fst _ _).trans compared
  simpa only [trace_values, run] using mapped

private theorem uniform_point (secret : MlKemSharedSecret) :
    Pr{let sampled ← $ᵗ MlKemSharedSecret}[sampled = secret] = (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, PqxdhExtractRomHiddenSuffix.secret_card]
  norm_num

/-- A fixed literal list catches only its length's share of the complete uniform32-byte space. -/
theorem list_guess (list : List MlKemSharedSecret) :
    Pr{let candidate ← $ᵗ MlKemSharedSecret}[candidate ∈ list] ≤ list.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  induction list with
  | nil =>
      rw [prEvent_eq_zero_of_forall_not _ _ (fun _ member => List.not_mem_nil member)]
      exact zero_le
  | cons value rest ih =>
      rw [prEvent_congr ($ᵗ MlKemSharedSecret) _ (fun candidate => candidate = value ∨ candidate ∈ rest)
        (fun candidate => List.mem_cons)]
      refine (prEvent_or_le ($ᵗ MlKemSharedSecret) (fun candidate => candidate = value) (fun candidate => candidate ∈ rest)).trans ?_
      rw [uniform_point]
      calc (256 ^ 32 : ℝ≥0∞)⁻¹ + Pr{let candidate ← $ᵗ MlKemSharedSecret}[candidate ∈ rest]
          ≤ (256 ^ 32 : ℝ≥0∞)⁻¹ + rest.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := add_le_add le_rfl ih
        _ = (rest.length + 1 : Nat) * (256 ^ 32 : ℝ≥0∞)⁻¹ := by simp [Nat.cast_add, add_mul, add_comm]

attribute [local irreducible] uniformSample

/-- The whole adaptive literal list is independent of the candidate, so all earlier and later literal queries share one derived key-query cap. -/
theorem guess_bound (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    Pr{let pair ← (do let candidate ← $ᵗ MlKemSharedSecret; let result ← run work; pure (candidate, result))}[pair.1 ∈ pair.2.2.2] ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  rw [OracleComp.prEvent_bind_map_swap]
  have after : ∀ result ∈ support (run work),
      Pr{let candidate ← $ᵗ MlKemSharedSecret}[candidate ∈ result.2.2] ≤ cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
    intro result reached
    refine (list_guess result.2.2).trans ?_
    gcongr
    exact_mod_cast length_bound work cap bounded result reached
  have averaged := prEvent_bind_le_of_forall_le_of_support (run work)
    (fun result => (fun candidate : MlKemSharedSecret => candidate ∈ result.2.2) <$> ($ᵗ MlKemSharedSecret : ProbComp _))
    (fun proposition : Prop => proposition)
    (fun result reached => by simpa only [prEvent_map] using after result reached)
  simpa only [map_bind, Functor.map_map, Function.comp_def, id_eq] using averaged

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.length_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.length_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.fixed_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.fixed_distance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.list_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.list_guess
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace.guess_bound
