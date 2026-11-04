-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage
import BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! A private complete query/reply trace is returned by the same original adaptive request tree. It includes root callbacks and is independent of any selected security event. Erasure recovers the original tree exactly. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
open RegistrationAgreementExecutor
abbrev Entry := (request : Request) × Spec.Range request
abbrev Trace := List Entry

def trace {Value : Type} (work : OracleComp Spec Value) : Trace → OracleComp Spec (Value × Trace) :=
  work.recOn (fun value journal => pure (value, journal))
    (fun request _next ih journal => do
      let reply ← Spec.query request
      ih reply (journal ++ [⟨request, reply⟩]))

theorem trace_pure {Value : Type} (value : Value) (journal : Trace) :
    trace (pure value) journal = pure (value, journal) := rfl

theorem trace_query_bind {Value : Type} (request : Request) (next : Spec.Range request → OracleComp Spec Value)
    (journal : Trace) : trace (Spec.query request >>= next) journal = (do
      let reply ← Spec.query request
      trace (next reply) (journal ++ [⟨request, reply⟩])) := rfl

theorem trace_query (request : Request) (journal : Trace) :
    trace (Spec.query request) journal = (do
      let reply ← Spec.query request
      pure (reply, journal ++ [⟨request, reply⟩])) := rfl

theorem trace_bind {Input Output : Type} (work : OracleComp Spec Input)
    (next : Input → OracleComp Spec Output) (journal : Trace) :
    trace (work >>= next) journal = (do
      let (value, current) ← trace work journal
      trace (next value) current) := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => simp only [pure_bind, trace_pure]
  | query_bind request continuation ih =>
    simp only [bind_assoc, trace_query_bind, ih]

theorem erasure {Value : Type} (work : OracleComp Spec Value) (journal : Trace) :
    Prod.fst <$> trace work journal = work := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => simp only [trace_pure, map_pure]
  | query_bind request next ih => simp only [trace_query_bind, map_bind, ih]

theorem bound {Value : Type} (work : OracleComp Spec Value) (covered : RegistrationAgreementRoleCoverage.Bound work)
    (journal : Trace) : RegistrationAgreementRoleCoverage.Bound (trace work journal) := by
  induction work using OracleComp.inductionOn generalizing journal with
  | pure value => exact isQueryBound_pure _ _ _ _
  | query_bind request next ih =>
    rw [RegistrationAgreementRoleCoverage.Bound, isQueryBound_query_bind_iff] at covered
    rw [trace_query_bind, RegistrationAgreementRoleCoverage.Bound, isQueryBound_query_bind_iff]
    exact ⟨covered.1, fun reply => ih reply (covered.2 reply) _⟩
end BeaconcryptCore.Computational.RegistrationAgreementQueryTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_query_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_query

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.trace_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTrace.bound
