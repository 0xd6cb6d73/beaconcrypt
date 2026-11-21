-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCandidate
import BeaconcryptCore.Computational.RegistrationBoundPublication

/-! The actual 108-byte and thin material44 Server publication controllers retain the admitted candidate identity for arbitrary primitive replies. This includes dynamic response encoding, failed raw writes and mandatory ML signature admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseBound
variable {Encoded Index Target Value : Type} {source : OracleSpec Index} {target : OracleSpec Target}

private theorem simulation_support (implementation : QueryImpl source (OracleComp target))
    (work : OracleComp source Value) (value : Value)
    (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure result => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _reached, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ _, ih reply continued⟩

/-- Supplying the complete 108-byte source output never changes the identity eventually encoded by the actual publication controller. -/
theorem program_identity (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (RegistrationBoundPublication.program encode initial output)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode initial.candidate.server_identity_public_key published.encoded := by
  simp only [RegistrationBoundPublication.program, mem_support_bind_iff] at supported
  obtain ⟨record, reached, continued⟩ := supported
  cases record with
  | fail error => simp only [RegistrationBoundPublication.after, mem_support_pure_iff] at continued; cases continued
  | div => simp only [RegistrationBoundPublication.after, mem_support_pure_iff] at continued; cases continued
  | ok result => cases result with
    | Err previous => simp only [RegistrationBoundPublication.after, mem_support_pure_iff] at continued; cases continued
    | Ok pending =>
        have original := simulation_support RegistrationRawSealBridge.nativeAdapter _ _
          (simulation_support RegistrationBoundPublication.rawLift _ _ reached)
        have same := RegistrationNativeResponseCandidate.factored_identity initial output pending original
        have encoded := RegistrationNativeResponseIdentity.program_identity encode pending published
          (simulation_support RegistrationBoundPublication.signingLift _ _ continued)
        rw [same] at encoded
        exact encoded

/-- The seed-free material44 continuation encodes the same admitted candidate identity. -/
theorem thin_identity (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (RegistrationBoundPublication.thin encode initial material)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode initial.candidate.server_identity_public_key published.encoded :=
  program_identity encode initial _ published supported

end BeaconcryptCore.Computational.RegistrationNativeResponseBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseBound.program_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseBound.program_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseBound.thin_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseBound.thin_identity
