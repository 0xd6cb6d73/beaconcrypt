-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyLayer

/-! The original hidden-bit and fresh-message controllers commute with native transport. Their actual source frame permits only coins and sends, so the native legacy embedding and transport compose to the identity on every reached query. Transcript metadata cannot affect the original same-session decision. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy
open RegistrationNativeEntropyCore (compiler)
open PqxdhDeploymentSecrecy (Ledger coinOrSend)
variable {Value Reader Response : Type}

private theorem framed_identity (work : OracleComp PqxdhDeploymentInterface.Spec Value)
    (bounded : work.IsQueryBoundP (fun query => coinOrSend query = false) 0) :
    simulateQ compiler (simulateQ RegistrationNativeLedger.legacyLift work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have allowed : coinOrSend query = true := by
        by_contra denied
        have bad : coinOrSend query = false := Bool.eq_false_iff.mpr denied
        have impossible := bounded.1.resolve_left (not_not.mpr bad)
        omega
      have one : (compiler ∘ₛ RegistrationNativeLedger.legacyLift) query =
          (PqxdhDeploymentInterface.Spec.query query : OracleComp PqxdhDeploymentInterface.Spec _) := by
        cases query with
        | inl coin => rfl
        | inr command =>
            cases command <;> simp only [coinOrSend, Bool.false_eq_true] at allowed
            all_goals rfl
      simp only [simulateQ_bind, simulateQ_spec_query, one]
      apply congrArg (fun continuation => (PqxdhDeploymentInterface.Spec.query query :
        OracleComp PqxdhDeploymentInterface.Spec _) >>= continuation)
      funext reply
      exact ih reply (by simpa only [Nat.zero_sub, ite_self] using bounded.2 reply)

/-- The literal original secrecy source issues only coin/send queries, on which the complete native transport is the identity. -/
theorem legacy_secrecy (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : Ledger) :
    simulateQ compiler (simulateQ RegistrationNativeLedger.legacyLift
        ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before)) =
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before) :=
  framed_identity _ (PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy before)

/-- Restoring a secrecy append retains every raw plaintext and exact original private test/fresh poststate. -/
theorem restore_secrecy (before : Ledger) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (reply : Option RawCtxSourceSend.Encrypted) (test : Option PqxdhDeploymentSecrecy.TestState)
    (fresh : List PqxdhDeploymentSecrecy.FreshEntry) :
    RegistrationNativeEntropyRestore.ledger
        { before.record (.inr secrecy) reply with test := test, fresh := fresh } =
      ⟨{ (RegistrationNativeEntropyRestore.ledger before).ledger.record (.inr secrecy) reply with
          test := test, fresh := fresh },
        (RegistrationNativeEntropyRestore.ledger before).transcript ++ [⟨.inr secrecy, reply⟩]⟩ := by
  have appended := RegistrationNativeEntropyLayer.restore_append before ⟨.inr secrecy, reply⟩
  have same := congrArg (fun state : RegistrationNativeLedger.State =>
    { state with ledger := { state.ledger with test := test, fresh := fresh } }) appended
  exact same

end BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy.legacy_secrecy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy.legacy_secrecy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy.restore_secrecy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy.restore_secrecy
