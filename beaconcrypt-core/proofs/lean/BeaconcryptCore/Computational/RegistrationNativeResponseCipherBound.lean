-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate
import BeaconcryptCore.Computational.RegistrationBoundPublication

/-! The actual 108-byte and thin material44 Server publication controllers retain the admitted candidate KEM ciphertext for arbitrary primitive replies. This includes dynamic response encoding, failed raw writes and mandatory ML signature admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound
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

/-- Supplying the complete 108-byte source output never changes the KEM ciphertext eventually encoded by the actual publication controller. -/
theorem program_ciphertext (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (RegistrationBoundPublication.program encode initial output)) :
    RegistrationNativeResponseCiphertext.EncodedFrom encode initial.candidate.kem_ciphertext published.encoded := by
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
        have same := RegistrationNativeResponseCipherCandidate.factored_ciphertext initial output pending original
        have encoded := RegistrationNativeResponseCiphertext.program_ciphertext encode pending published
          (simulation_support RegistrationBoundPublication.signingLift _ _ continued)
        rw [same] at encoded
        exact encoded

/-- The seed-free material44 continuation encodes the same admitted candidate KEM ciphertext. -/
theorem thin_ciphertext (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (RegistrationBoundPublication.thin encode initial material)) :
    RegistrationNativeResponseCiphertext.EncodedFrom encode initial.candidate.kem_ciphertext published.encoded :=
  program_ciphertext encode initial _ published supported


end BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound.program_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound.program_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound.thin_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound.thin_ciphertext
