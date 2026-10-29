-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache

/-! Actual Family cache coverage has a finite size derived from actual derive-query budgets. Each fresh checker adds one possible literal input, including when previous candidates were chosen adaptively. Coin and fixed public-HMAC calls do not grow this address list. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacSha512)
open RegistrationNativeRelatedFamily (Spec State input)
open RegistrationNativeKnownInputBatchCache (addresses append_derive)
variable {Value : Type}

def IsDerive : Spec.Domain → Prop
  | .inr (.derive _) => True
  | _ => False

instance : DecidablePred IsDerive := fun query => by
  rcases query with coin | (message | key | message) <;> simp only [IsDerive] <;> infer_instance

/-- Every actual ideal query adds at most its own one derive address to the literal history list. -/
theorem query_count (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain) (before : State)
    (result : Spec.Range query × State)
    (supported : result ∈ support ((RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar query).run before)) :
    (addresses joint dh seed scalar result.2.history).length ≤
      (addresses joint dh seed scalar before.history).length + (if IsDerive query then 1 else 0) := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨value, _sampled, returned⟩ := supported
      cases returned
      simp only [IsDerive, ite_false, Nat.add_zero, le_refl]
  | inr query => cases query with
    | sign message | publicHmac key message =>
        simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run,
          support_pure, Set.mem_singleton_iff] at supported
        cases supported
        simp only [addresses, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil,
          IsDerive, ite_false, Nat.add_zero, le_refl]
    | derive message =>
        simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run] at supported
        cases realized : input joint dh seed scalar message with
        | none =>
            rw [realized] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rw [append_derive, realized]
            simp only [Option.toList_none, List.append_nil, IsDerive, ite_true]
            omega
        | some bytes =>
            rw [realized] at supported
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
            obtain ⟨derived, _reached, returned⟩ := supported
            cases returned
            rw [append_derive, realized]
            simp only [Option.toList_some, List.length_append, List.length_singleton, IsDerive, ite_true, le_refl]

/-- The original actual derive-query cap bounds every reached cache-address list. -/
theorem program_count (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec Value) (budget : Nat)
    (bounded : work.IsQueryBoundP IsDerive budget) (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) work).run before)) :
    (addresses joint dh seed scalar result.2.history).length ≤ (addresses joint dh seed scalar before.history).length + budget := by
  induction work using OracleComp.inductionOn generalizing before budget with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      dsimp only
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have head := query_count hmac joint dh seed scalar query before middle reached
      have tail := ih middle.1 _ (bounded.2 middle.1) middle.2 continued
      by_cases counted : IsDerive query
      · have positive := bounded.1.resolve_left (not_not.mpr counted)
        simp only [counted, ite_true] at head tail
        omega
      · simp only [counted, ite_false] at head tail
        omega

/-- Actual local probability draws add no Family derive address. -/
theorem coins_zero (work : ProbComp Value) :
    (simulateQ RegistrationNativeKnownInputCheck.coins work).IsQueryBoundP IsDerive 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro coin _unselected
  simp only [RegistrationNativeKnownInputCheck.coins, isQueryBoundP_query_iff, IsDerive]
  intro impossible
  exact impossible.elim

/-- The fixed-suffix candidate checker contains exactly one possibly cache-growing derive query. -/
theorem checkAt_cap (first suffix : DhOutput) :
    (RegistrationNativeKnownInputCheck.checkAt first suffix).IsQueryBoundP IsDerive 1 := by
  simp only [RegistrationNativeKnownInputCheck.checkAt, isQueryBoundP_query_bind_iff,
    IsDerive, Nat.lt_one_iff, Nat.sub_self, isQueryBoundP_pure]
  simp

/-- A complete actual fresh candidate test adds at most one literal input to the earlier-address list. -/
theorem check_cap (first : DhOutput) :
    (RegistrationNativeKnownInputCheck.check first).IsQueryBoundP IsDerive 1 := by
  unfold RegistrationNativeKnownInputCheck.check
  exact isQueryBoundP_bind (coins_zero ($ᵗ DhOutput)) (fun suffix _ => checkAt_cap first suffix)

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.query_count' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.query_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.program_count' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.program_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.coins_zero' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.coins_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.checkAt_cap' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.checkAt_cap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.check_cap' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting.check_cap
