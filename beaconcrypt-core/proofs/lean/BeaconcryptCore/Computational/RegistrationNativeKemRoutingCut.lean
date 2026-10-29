-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemRouting

/-! Ordinary native accept programs execute before the selected cut without consuming its ordinal. The entire arbitrary continuation, generated-key service state and ordinary encapsulation callbacks remain in their original order. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemRoutingCut
open RegistrationNativeKemInterface (Spec EncapsulationSpec)
open RegistrationNativeKemRouting (route)
open RegistrationNativeKemCut (scan)
variable {κ KemSK Value Result : Type} {ambient : OracleSpec κ}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- All nonselected native work is executed at the unchanged selected-getter cut, including its actual public encapsulations. -/
theorem ordinary_prefix
    (implementation : QueryImpl (Spec (ambient + EncapsulationSpec) KemSK) m)
    (work : OracleComp (Spec ambient KemSK) Value)
    (next : Value → OracleComp (Spec (ambient + EncapsulationSpec) KemSK) Result) (index : Nat) :
    scan implementation (simulateQ (route false) work >>= next) index =
      (simulateQ (implementation ∘ₛ route false) work >>= fun value => scan implementation (next value) index) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_bind]
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
      rcases query with query | (query | key)
      · simp only [route, RegistrationNativeKemCut.scan_other, QueryImpl.apply_compose,
          simulateQ_spec_query]
        congr 1
        funext reply
        exact ih reply
      · simp only [route, RegistrationNativeKemCut.scan_pool, QueryImpl.apply_compose,
          simulateQ_spec_query]
        congr 1
        funext reply
        exact ih reply
      · simp only [route, Bool.false_eq_true, ite_false,
          QueryImpl.apply_compose, simulateQ_spec_query]
        rw [RegistrationNativeKemCut.scan_other (ambient := ambient + EncapsulationSpec)
          implementation (.inr key)]
        congr 1
        funext reply
        exact ih reply

end BeaconcryptCore.Computational.RegistrationNativeKemRoutingCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRoutingCut.ordinary_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRoutingCut.ordinary_prefix
