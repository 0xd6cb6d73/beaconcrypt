-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlySource
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! The early first-getter substitution forwards every indexed creation and reveal exactly as in the original AST. Its complete source therefore inherits the actual original create/no-reveal bills; no extra resource premise is needed for its challenge transformation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemEarlyGame (intercept)
open PqxdhKemIndCca
variable {κ KemSK : Type} {ambient : OracleSpec κ}

private def call (query : (Spec ambient KemSK).Domain) : OracleComp (Spec ambient KemSK) ((Spec ambient KemSK).Range query) :=
  (Spec ambient KemSK).query query

private theorem pure_intercept (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (value : Bool) :
    intercept (ambient := ambient) (KemSK := KemSK) key challenge candidate (pure value) = pure value := by
  have exposed : RegistrationNativeKemGame.expose (pure value : OracleComp (Spec ambient KemSK) Bool) 0 =
      pure (.complete value) := rfl
  simp only [intercept, exposed, pure_bind, RegistrationNativeKemTotalGame.continuation]

private theorem other_intercept (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : ambient.Domain)
    (next : ambient.Range query → OracleComp (Spec ambient KemSK) Bool) :
    intercept key challenge candidate (call (.inl query) >>= next) =
      call (.inl query) >>= fun reply => intercept key challenge candidate (next reply) := by
  simp only [call, intercept, RegistrationNativeKemGame.expose, RegistrationNativeKemCut.scan_other, bind_assoc]

private theorem pool_intercept (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : PqxdhLiveKemBirth.Query)
    (next : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → OracleComp (Spec ambient KemSK) Bool) :
    intercept key challenge candidate (call (.inr (.inl query)) >>= next) =
      call (.inr (.inl query)) >>= fun reply => intercept key challenge candidate (next reply) := by
  simp only [call, intercept, RegistrationNativeKemGame.expose, RegistrationNativeKemCut.scan_pool, bind_assoc]

private theorem getter_intercept (key publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Bool) :
    intercept publicKey challenge candidate (call (.inr (.inr key)) >>= next) =
      if key = publicKey then next (challenge, candidate) else call (.inr (.inr key)) >>= next := by
  simp only [call, intercept, RegistrationNativeKemGame.expose, RegistrationNativeKemCut.scan_target,
    pure_bind, RegistrationNativeKemTotalGame.continuation]

/-- Replacing the first getter preserves every original predicated query bill whose predicate excludes encapsulation getters. -/
theorem intercept_bound (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (predicate : (Spec ambient KemSK).Domain → Prop) [DecidablePred predicate]
    (getterFree : ∀ publicKey, ¬predicate (.inr (.inr publicKey)))
    (work : OracleComp (Spec ambient KemSK) Bool) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    (intercept key challenge candidate work).IsQueryBoundP predicate cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => simp only [pure_intercept, isQueryBoundP_pure]
  | query_bind query next ih =>
      rcases query with query | (query | publicKey)
      · change (intercept key challenge candidate (call (.inl query) >>= next)).IsQueryBoundP predicate cap
        rw [other_intercept, call, isQueryBoundP_query_bind_iff]
        rw [isQueryBoundP_query_bind_iff] at bounded
        exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      · change (intercept key challenge candidate (call (.inr (.inl query)) >>= next)).IsQueryBoundP predicate cap
        rw [pool_intercept, call, isQueryBoundP_query_bind_iff]
        rw [isQueryBoundP_query_bind_iff] at bounded
        exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      · change (intercept key challenge candidate (call (.inr (.inr publicKey)) >>= next)).IsQueryBoundP predicate cap
        rw [getter_intercept]
        by_cases matching : publicKey = key
        · rw [ite_eq_left matching]
          rw [isQueryBoundP_query_bind_iff] at bounded
          simpa only [ite_eq_right (getterFree publicKey)] using bounded.2 (challenge, candidate)
        · rw [ite_eq_right matching]
          simpa only [call] using bounded

/-- Actual opaque key creation retains its original complete-program allowance under the early challenge. -/
theorem create_bound (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Bool) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) cap) :
    (intercept key challenge candidate work).IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) cap :=
  intercept_bound key challenge candidate _ (fun _ => not_false) work cap bounded

/-- The original absence of indexed reveals is retained for every early-branch callback and failure path. -/
theorem reveal_bound (key : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Bool) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) cap) :
    (intercept key challenge candidate work).IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) cap :=
  intercept_bound key challenge candidate _ (fun _ => not_false) work cap bounded

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.intercept_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.intercept_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.create_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.create_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.reveal_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyBudget.reveal_bound
