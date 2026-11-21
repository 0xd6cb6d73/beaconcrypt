-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportLift

/-! Original raw candidates reported immediately after actual successful acceptance. Every bounded generated target index is considered, so key collisions never become an ownership assumption. Public reporting retains the original source reply and the whole remaining adaptive schedule. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports
open PqxdhJointPhase1Reports (CandidateReport)
open PqxdhRegistrationJointReportLift (Spec lift erase extend)
open PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Report the same original public fields at every explicit generated index. This is report work, not a second target-selection experiment. -/
def batch {κ : Type} {source : OracleSpec κ} (indices : List Nat) (original : PqxdhEd25519EufCma.Phase1Candidate) :
    OracleComp (Spec source) Unit :=
  match indices with
  | [] => pure ()
  | index :: rest => do
    (Spec source).query (.inr ⟨index, original⟩)
    batch rest original

/-- Malformed and failed native acceptances emit no candidate. A successful raw acceptance reports only the candidate read from its unchanged original public bytes. -/
def report (codec : Codec Reader Response) (count : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (answer : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query)
    {κ : Type} {source : OracleSpec κ} : OracleComp (Spec source) Unit :=
  match query, answer with
  | .inl (.inr (.accept raw)), some _ =>
      match PqxdhRegistrationJointRawSignatures.candidate codec raw with
      | none => pure ()
      | some original => batch (List.range count) original
  | _, _ => pure ()

/-- The actual command executes first. Its exact optional answer controls public reporting and is then returned without changing the adversary continuation. -/
def instrument (codec : Codec Reader Response) (count : Nat) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (OracleComp (Spec (PqxdhRegistrationJointRevealSchedule.Spec KemSK))) := fun query => do
  let answer ← (Spec (PqxdhRegistrationJointRevealSchedule.Spec KemSK)).query (.inl query)
  report codec count query answer
  pure answer

/-- Every explicit public report vanishes under the nonobserving bookkeeping erasure. -/
theorem batch_erase {κ : Type} {source : OracleSpec κ}
    (indices : List Nat) (original : PqxdhEd25519EufCma.Phase1Candidate) :
    simulateQ (erase (source := source)) (batch indices original) = pure () := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [batch, simulateQ_bind, simulateQ_spec_query, erase, pure_bind, ih]

/-- Erasing reports preserves every original source reply and cryptographic request; public verification and scanning remain separately added report work. -/
theorem report_erase {κ : Type} {source : OracleSpec κ}
    (codec : Codec Reader Response) (count : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (answer : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query) :
    simulateQ (erase (source := source)) (report codec count query answer) = pure () := by
  rcases query with (coin | request) | request
  · rfl
  · cases request <;> try rfl
    rename_i raw
    cases answer with
    | none => rfl
    | some index =>
        simp only [report]
        split
        · rfl
        · exact batch_erase _ _
  · rfl

/-- Forgetting only reports gives precisely the original whole adaptive source-command tree, including optional answers and every subsequent command. -/
theorem instrument_erase (codec : Codec Reader Response) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) :
    simulateQ erase (simulateQ (instrument codec count) program) = program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, instrument, erase,
        simulateQ_pure, pure_bind, report_erase, ih, bind_pure]

end BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.batch_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.batch_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.report_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.report_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.instrument_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRawReports.instrument_erase
