-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix
open RegistrationAgreementExecutor RegistrationAgreementQueryTrace

theorem trace_prefix {Value : Type} (work : OracleComp Spec Value) (initial journal : Trace) :
    trace work (initial ++ journal) = Prod.map id (initial ++ ·) <$> trace work journal := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => simp only [trace_pure, map_pure]; rfl
  | query_bind request next ih =>
    simp only [trace_query_bind, map_bind, List.append_assoc, ih]

theorem query_bind_empty {Value : Type} (request : Request) (next : Spec.Range request → OracleComp Spec Value) :
    trace (Spec.query request >>= next) [] = (do
      let reply ← Spec.query request
      (fun result => (result.1, ⟨request, reply⟩ :: result.2)) <$> trace (next reply) []) := by
  rw [trace_query_bind]
  apply bind_congr
  intro reply
  calc
    _ = Prod.map id ([⟨request, reply⟩] ++ ·) <$> trace (next reply) [] := by
      simpa only [List.nil_append, List.append_nil] using trace_prefix (next reply) [⟨request, reply⟩] []
    _ = _ := by
      congr 1
end BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix.trace_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix.trace_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix.query_bind_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix.query_bind_empty
