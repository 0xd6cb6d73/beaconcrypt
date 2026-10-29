-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! The cut suspends the literal native encapsulation getter before any KEM reply. It retains the exact remaining arbitrary native program and all earlier interpretation effects. It has no legacy source14 command, typed accept surrogate or selected secret field. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCut
open RegistrationNativeKemInterface (Spec)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
variable {κ KemSK Result : Type} {ambient : OracleSpec κ}
variable {m : Type → Type} [Monad m]

inductive Cut (ambient : OracleSpec κ) (KemSK Result : Type) where
  | complete (result : Result)
  | pending (key : MlKem768PublicKey)
      (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Result)

noncomputable def scan (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Result) : Nat → m (Cut ambient KemSK Result) :=
  OracleComp.recOn work
    (fun result _ => pure (.complete result))
    (fun query next recurse index => match query with
      | .inl request => do
          let reply ← implementation (.inl request)
          recurse reply index
      | .inr (.inl request) => do
          let reply ← implementation (.inr (.inl request))
          recurse reply index
      | .inr (.inr key) => match index with
          | 0 => pure (.pending key next)
          | index + 1 => do
              let reply ← implementation (.inr (.inr key))
              recurse reply index)

noncomputable def finish (implementation : QueryImpl (Spec ambient KemSK) m) : Cut ambient KemSK Result → m Result
  | .complete result => pure result
  | .pending key next => do
      let reply ← implementation (.inr (.inr key))
      simulateQ implementation (next reply)

/-- The selected getter is suspended before its ciphertext and secret are sampled. -/
theorem scan_target (implementation : QueryImpl (Spec ambient KemSK) m) (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Result) :
    scan implementation ((Spec ambient KemSK).query (.inr (.inr key)) >>= next) 0 = pure (.pending key next) := rfl

/-- Every earlier encapsulation preserves its literal native callback and continuation. -/
theorem scan_prior (implementation : QueryImpl (Spec ambient KemSK) m) (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Result) (index : Nat) :
    scan implementation ((Spec ambient KemSK).query (.inr (.inr key)) >>= next) (index + 1) =
      (implementation (.inr (.inr key)) >>= fun answer => scan implementation (next answer) index) := rfl

/-- Non-KEM primitive callbacks retain the exact effects of the chosen actual interpreter. -/
theorem scan_other (implementation : QueryImpl (Spec ambient KemSK) m) (query : ambient.Domain)
    (next : ambient.Range query → OracleComp (Spec ambient KemSK) Result) (index : Nat) :
    scan implementation ((Spec ambient KemSK).query (.inl query) >>= next) index =
      (implementation (.inl query) >>= fun answer => scan implementation (next answer) index) := rfl

/-- Generated-key creation, private indexed decapsulation and ordinary reveals keep their full reply and history positions. -/
theorem scan_pool (implementation : QueryImpl (Spec ambient KemSK) m) (query : PqxdhLiveKemBirth.Query)
    (next : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → OracleComp (Spec ambient KemSK) Result) (index : Nat) :
    scan implementation ((Spec ambient KemSK).query (.inr (.inl query)) >>= next) index =
      (implementation (.inr (.inl query)) >>= fun answer => scan implementation (next answer) index) := rfl

/-- Running the cut and original callback continuation gives the entire original native program under any actual stateful interpreter. -/
theorem scan_finish [LawfulMonad m] (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Result) (index : Nat) :
    (scan implementation work index >>= finish implementation) = simulateQ implementation work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result =>
      change (pure (Cut.complete result) >>= finish implementation) = pure result
      rw [pure_bind]
      rfl
  | query_bind query next ih =>
    rcases query with query | (query | key)
    · simp only [scan_other, bind_assoc, ih, simulateQ_bind, simulateQ_spec_query]
    · simp only [scan_pool, bind_assoc, ih, simulateQ_bind, simulateQ_spec_query]
    · cases index with
      | zero => simp only [scan_target, pure_bind, finish, simulateQ_bind, simulateQ_spec_query]
      | succ index => simp only [scan_prior, bind_assoc, ih, simulateQ_bind, simulateQ_spec_query]

end BeaconcryptCore.Computational.RegistrationNativeKemCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_target' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_prior' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_prior

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_other' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_pool' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_pool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCut.scan_finish
