-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition
/-! The exact unarmed operational source lowers to protocol and public hash leaves only. Removing the public markers cannot introduce a selector query, across every arbitrary adaptive source continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec Unarmed record)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}
abbrev NewSpec := RegistrationNativeIdentityTemplateCensorRecognition.Spec

def Allowed : NewSpec.Domain → Prop
  | .inl (.inl (.inr _)) => False
  | _ => True

private theorem record_scope (placeholder : Ed25519Signature) (query : SourceSpec.Domain) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record query).run before))).AllQueriesSatisfy Allowed := by
  cases query with
  | inl query =>
    simp only [record, StateT.run, RegistrationNativeIdentityCensorPrefix.embed,
      RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_bind, simulateQ_spec_query,
      RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase,
      simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _
  | inr bytes =>
    simp only [record, StateT.run, RegistrationNativeIdentityCensorPrefix.embed,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _

private theorem recorder (placeholder : Ed25519Signature) (work : OracleComp SourceSpec A) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run before))).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind (record_scope placeholder query before)
    intro result
    exact ih result.1 result.2

/-- Actual unarmed lowering emits no selector leaf after template marker erasure, for every current source reply. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (before : Mode) (prior : Unarmed before) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run before)).AllQueriesSatisfy Allowed := by
  rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request before prior]
  exact record_scope placeholder request before

/-- The complete adaptive unarmed source prefix cannot consult public fresh-message selection. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp SourceSpec A)
    (before : Mode) (prior : Unarmed before) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before)).AllQueriesSatisfy Allowed := by
  rw [RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder work before prior]
  exact recorder placeholder work before

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect.program
