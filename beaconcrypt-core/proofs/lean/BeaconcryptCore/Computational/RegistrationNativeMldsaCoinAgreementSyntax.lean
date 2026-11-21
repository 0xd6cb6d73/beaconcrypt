-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementExecutor
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Literal query bounds for both original native agreement entries. Each fuel step either terminates or invokes one actual extracted getter, primitive request and resume. Optional failure, Rust failure and divergence retain their exact prefixes; the bound does not assert successful completion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax

private theorem continue_bound {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationAgreementExecutor.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem step (phase : agreement.AgreementEffect) :
    (RegistrationAgreementExecutor.step phase).IsTotalQueryBound 1 := by
  cases phase <;> simp only [RegistrationAgreementExecutor.step]
  all_goals first
    | trivial
    | apply continue_bound
      intro request
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => by trivial⟩

/-- Every reply path of the actual driver fits its literal fuel allowance. -/
theorem drive (fuel : Nat) (phase : agreement.AgreementEffect) :
    (RegistrationAgreementExecutor.drive fuel phase).IsTotalQueryBound fuel := by
  induction fuel generalizing phase with
  | zero => trivial
  | succ fuel ih =>
      rw [RegistrationAgreementExecutor.drive]
      have rest : ∀ result, (RegistrationAgreementExecutor.continueWith result
          (RegistrationAgreementExecutor.drive fuel)).IsTotalQueryBound fuel :=
        fun result => continue_bound result _ fuel ih
      simpa only [Nat.add_comm 1 fuel] using isTotalQueryBound_bind (step phase) rest

/-- The actual Server entry executes no more than its nine driver slots. -/
theorem server (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) :
    (RegistrationAgreementExecutor.server control status authenticated).IsTotalQueryBound 9 :=
  continue_bound _ _ 9 (drive 9)

/-- The actual Beacon entry executes no more than its nine driver slots. -/
theorem beacon (authenticated : registration.AuthenticatedResponse) :
    (RegistrationAgreementExecutor.beacon authenticated).IsTotalQueryBound 9 :=
  continue_bound _ _ 9 (drive 9)
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.drive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.drive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAgreementSyntax.beacon
