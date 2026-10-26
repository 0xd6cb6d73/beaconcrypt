-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedUniform

/-! The literal encapsulation scan inherits the original source bounds, and every reached pending callback inherits the same all-reply residual bounds. This supplies finite adversary contexts without adding a runtime support test. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds
open PqxdhRegistrationJointKemEncapsulation PqxdhRegistrationJointKemCut PqxdhRegistrationJointKemExposedCounts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result Next : Type}

def Count (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) : (Spec KemSK).Domain → Prop
  | .inl query => predicate query
  | .inr _ => False
instance (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (Count (KemSK := KemSK) predicate) := fun query => by
  cases query
  · exact inferInstanceAs (Decidable (predicate _))
  · exact inferInstanceAs (Decidable False)

/-- A complete computation's selective bound also bounds its original prefix; continuation work cannot erase preceding requests. -/
theorem bind_prefix {κ : Type} {target : OracleSpec κ} (work : OracleComp target Result)
    (next : Result → OracleComp target Next) (predicate : target.Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (bounded : (work >>= next).IsQueryBoundP predicate cap) :
    work.IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure result => trivial
  | query_bind query continuation ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at bounded
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Real interpretation charges every old query and every reached actual encapsulation's declared primitive bill. -/
theorem actual_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (work : OracleComp (Spec KemSK) Result)
    (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (qOld qEncap cost : Nat)
    (old : work.IsQueryBoundP (Count (KemSK := KemSK) predicate) qOld)
    (encap : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) qEncap)
    (primitive : ∀ request, (actual setup (.inr request)).IsQueryBoundP predicate cost) :
    (simulateQ (actual setup) work).IsQueryBoundP predicate (qOld + cost * qEncap) := by
  induction work using OracleComp.inductionOn generalizing qOld qEncap with
  | pure result => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at old encap
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query, actual, isQueryBoundP_query_bind_iff]
      simp only [Count] at old
      refine ⟨old.1.imp_right (fun positive => by omega), ?_⟩
      · intro answer
        have tail := ih answer _ _ (old.2 answer) (encap.2 answer)
        apply tail.mono
        simp only [IsEncapsulation, ite_false]
        split_ifs with counted
        · have positive := old.1.resolve_left (not_not.mpr counted)
          omega
        · omega
    | inr request =>
      have positive : 0 < qEncap := by simpa only [IsEncapsulation, not_true_eq_false, false_or] using encap.1
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      simp only [simulateQ_bind, simulateQ_spec_query]
      have result := isQueryBoundP_bind (primitive request) (fun answer _ =>
        ih answer qOld remaining (by simpa only [Count, ite_false] using old.2 answer)
          (by simpa only [IsEncapsulation, ite_true, Nat.add_one_sub_one] using encap.2 answer))
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- The executable prechallenge scan has no more queried work than completing the original source callback with its real encapsulator. -/
theorem scan_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (qOld qEncap cost : Nat)
    (old : work.IsQueryBoundP (Count (KemSK := KemSK) predicate) qOld)
    (encap : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) qEncap)
    (primitive : ∀ request, (actual setup (.inr request)).IsQueryBoundP predicate cost) :
    (scan setup work index).IsQueryBoundP predicate (qOld + cost * qEncap) := by
  apply bind_prefix _ (finish setup)
  rw [scan_finish]
  exact actual_bound setup work predicate qOld qEncap cost old encap primitive

/-- A pending source cut carries a bound for every possible encapsulation reply, including failure. -/
def Residual (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) : Cut KemSK Result → Prop
  | .complete _ => True
  | .pending _ next => ∀ reply, (next reply).IsQueryBoundP predicate cap

/-- Every actually reached cut inherits the original source's all-reply continuation bound. The scan support is structural over arbitrary private-service replies, not only a real-key distribution. -/
theorem residual (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (work : OracleComp (Spec KemSK) Result) (index : Nat)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (bounded : work.IsQueryBoundP predicate cap)
    (cut : Cut KemSK Result) (reached : cut ∈ support (scan setup work index)) :
    Residual predicate cap cut := by
  induction work using OracleComp.inductionOn generalizing index cut with
  | pure result =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    have tail (answer) : (next answer).IsQueryBoundP predicate cap :=
      (bounded.2 answer).mono (by split_ifs <;> omega)
    cases query with
    | inl query =>
      rw [scan_other, mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      exact ih answer index (tail answer) cut reached
    | inr request =>
      cases index with
      | zero =>
        rw [scan_target] at reached
        obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
        exact tail
      | succ index =>
        rw [scan_prior, mem_support_bind_iff] at reached
        obtain ⟨answer, _, reached⟩ := reached
        exact ih answer index (tail answer) cut reached

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.bind_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.bind_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.actual_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.scan_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.scan_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutBounds.residual
