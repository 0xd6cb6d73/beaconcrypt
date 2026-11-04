-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! A successful value returned by an arbitrary typed free program interpreted in source RustT belongs to that same original free program. Capture, Native and external poststates remain explicit, and failed or divergent leaf replies cannot enter a successful continuation. -/
namespace BeaconcryptCore.Refinement.AdapterPublicSuccessfulOracleSupport
open AdapterPublicWrapperRustT (RustT)
variable {I S T P Value : Type} {spec : OracleSpec I}

theorem successful (implementation : QueryImpl spec (StateT S (RustT (StateT T (StateT P ProbComp)))))
    (work : OracleComp spec Value) (value : Value)
    (beforeCapture afterCapture : S) (beforeNative afterNative : T) (previous next : P)
    (supported : ((.ok (value, afterCapture), afterNative), next) ∈ support
      (((((simulateQ implementation work).run beforeCapture).run).run beforeNative).run previous)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing beforeCapture afterCapture beforeNative afterNative previous next with
  | pure result =>
    simp only [simulateQ_pure, StateT.run_pure, RustT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq] at supported
    cases supported.1.1.1
    simp only [support_pure, Set.mem_singleton_iff]
  | query_bind query rest ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, RustT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨answer, middleNative⟩, between⟩, _called, continued⟩ := supported
    cases answer with
    | fail error | div =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at continued
    | ok pair =>
      rcases pair with ⟨reply, middleCapture⟩
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply,
        ih reply middleCapture afterCapture middleNative afterNative between next continued⟩

end BeaconcryptCore.Refinement.AdapterPublicSuccessfulOracleSupport

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicSuccessfulOracleSupport.successful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicSuccessfulOracleSupport.successful
