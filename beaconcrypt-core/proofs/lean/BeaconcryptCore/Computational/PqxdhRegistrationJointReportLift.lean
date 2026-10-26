-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRawSignatures

/-! Transparent public candidate reporting beside an arbitrary actual oracle program. Reports carry only the original public signature fields and a generated target index. Erasing reports must preserve the complete program, including every state coordinate and continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift
open PqxdhJointPhase1Reports (CandidateSpec CandidateReport)
variable {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ} {A S : Type}
abbrev Spec (source : OracleSpec ι) := source + CandidateSpec

def lift (program : OracleComp source A) : OracleComp (Spec source) A :=
  simulateQ (fun query => ((Spec source).query (.inl query) : OracleComp (Spec source) _)) program

def erase : QueryImpl (Spec source) (OracleComp source)
  | .inl query => source.query query
  | .inr _ => pure ()

def extend (impl : QueryImpl source (StateT S (OracleComp target))) :
    QueryImpl (Spec source) (StateT S (OracleComp (Spec target)))
  | .inl query => fun state => lift (impl query state)
  | .inr report => fun state => (fun _ => ((), state)) <$> (Spec target).query (.inr report)

/-- Public bookkeeping does not alter any source request or its complete adaptive continuation. -/
theorem erase_lift (program : OracleComp source A) : simulateQ erase (lift program) = program := by
  unfold lift
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, erase, ih]

/-- Extending a stateful compiler with public reports preserves its whole original execution after forgetting only reporting requests. -/
theorem extend_erase (impl : QueryImpl source (StateT S (OracleComp target)))
    (program : OracleComp (Spec source) A) (state : S) :
    simulateQ erase ((simulateQ (extend impl) program).run state) =
      (simulateQ impl (simulateQ erase program)).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, extend, erase, ih]
          simp only [StateT.run, erase_lift]
      | inr report =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, extend, erase, pure_bind, ih]
          simp only [StateT.run, simulateQ_map, simulateQ_spec_query, erase, map_pure, pure_bind]

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift.erase_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift.erase_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift.extend_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift.extend_erase
