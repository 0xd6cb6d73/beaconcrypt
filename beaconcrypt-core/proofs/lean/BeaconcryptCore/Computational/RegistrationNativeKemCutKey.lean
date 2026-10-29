-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCutStop

/-! The first native getter retains its literal key through arbitrary preceding stateful effects. A completed prefix is composed with its exact continuation; a suspended prefix retains that continuation without evaluating it. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCutKey
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut scan)
open PqxdhKemIndCca (MlKem768PublicKey)
variable {κ KemSK Value Result : Type} {ambient : OracleSpec κ}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def hasKey (key : MlKem768PublicKey) : (Spec ambient KemSK).Domain → Prop
  | .inr (.inr actual) => actual = key
  | _ => True

/-- A literal query restriction is retained through an actual compiler whose admitted callbacks satisfy that restriction. -/
theorem simulate_allowed {σ : Type} {input : OracleSpec σ}
    (implementation : QueryImpl input (OracleComp (Spec ambient KemSK)))
    (predicate : input.Domain → Prop) (key : MlKem768PublicKey)
    (callbacks : ∀ query, predicate query → (implementation query).AllQueriesSatisfy
      (hasKey (ambient := ambient) (KemSK := KemSK) key))
    (work : OracleComp input Value) (allowed : work.AllQueriesSatisfy predicate) :
    (simulateQ implementation work).AllQueriesSatisfy (hasKey (ambient := ambient) (KemSK := KemSK) key) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (callbacks query allowed.1) (fun reply => ih reply (allowed.2 reply))

/-- Suspending the first getter commutes with composing the exact native continuation. -/
theorem scan_bind (implementation : QueryImpl (Spec ambient KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Value)
    (next : Value → OracleComp (Spec ambient KemSK) Result) :
    scan implementation (work >>= next) 0 =
      (scan implementation work 0 >>= fun cut => match cut with
        | .complete value => scan implementation (next value) 0
        | .pending key resume => pure (.pending key (fun reply => resume reply >>= next))) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      change scan implementation (pure value >>= next) 0 = (pure (Cut.complete value) >>= _)
      rw [pure_bind, pure_bind]
  | query_bind query resume ih =>
      rcases query with query | (query | key)
      · simp only [bind_assoc, RegistrationNativeKemCut.scan_other, ih]
      · simp only [bind_assoc, RegistrationNativeKemCut.scan_pool, ih]
      · simp only [bind_assoc, RegistrationNativeKemCut.scan_target, pure_bind]
        rfl

/-- Every supported first-getter suspension has the key required by the actual program's query syntax. -/
theorem pending_key {S : Type}
    (implementation : QueryImpl (Spec ambient KemSK) (StateT S ProbComp))
    (work : OracleComp (Spec ambient KemSK) Value) (key : MlKem768PublicKey)
    (allowed : work.AllQueriesSatisfy (hasKey (ambient := ambient) (KemSK := KemSK) key))
    (actual : MlKem768PublicKey)
    (next : (PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) →
      OracleComp (Spec ambient KemSK) Value) (before after : S)
    (supported : (.pending actual next, after) ∈ support ((scan implementation work 0).run before)) :
    actual = key := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
      change (Cut.pending actual next, after) ∈
        support (pure (Cut.complete value, before) : ProbComp (Cut ambient KemSK Value × S)) at supported
      simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | query_bind query resume ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rcases query with query | (query | requested)
      · rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨reply, reached⟩, _prefix, tail⟩ := supported
        exact ih reply (allowed.2 reply) reached after tail
      · rw [RegistrationNativeKemCut.scan_pool, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨reply, reached⟩, _prefix, tail⟩ := supported
        exact ih reply (allowed.2 reply) reached after tail
      · simp only [RegistrationNativeKemCut.scan_target, StateT.run_pure,
          mem_support_pure_iff, Prod.mk.injEq, Cut.pending.injEq] at supported
        exact supported.1.1.trans allowed.1

end BeaconcryptCore.Computational.RegistrationNativeKemCutKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutKey.simulate_allowed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutKey.simulate_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutKey.scan_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutKey.scan_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCutKey.pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCutKey.pending_key
