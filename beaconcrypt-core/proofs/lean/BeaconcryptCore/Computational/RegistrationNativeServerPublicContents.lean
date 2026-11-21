-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerContents
import BeaconcryptCore.Refinement.RegistrationAd

/-! The actual checked source Server candidate retains the consumed token's public operands and current Server identity before publication. This provides public-stage correspondence without assumptions about private root equality or completed peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPublicContents

/-- Successful actual allocation/preparation retains all three public agreement fields and the current source Server identity. -/
theorem prepared (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (actual : pqxdh.server_prepare_commit state pending binding availability = .ok (.Ok candidate)) :
    candidate.server_identity_public_key = binding.identity_public_key ∧
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.ephemeral_public_key = pending.ephemeral_public_key ∧ candidate.kem_ciphertext = pending.kem_ciphertext := by
  obtain ⟨beacon, server, _, ephemeral, kem⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_prepare_fields
      state pending binding availability candidate actual
  exact ⟨server, beacon, ephemeral, kem⟩

/-- The original consuming initializer uses these exact public token fields and the actual current pin identity. -/
theorem initial (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (capability : agreement.ServerAgreement)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability capability application initial) :
    initial.candidate.server_identity_public_key = pin.binding.identity_public_key ∧
      initial.candidate.beacon_identity_public_key = capability.pending.beacon_identity_public_key ∧
      initial.candidate.ephemeral_public_key = capability.pending.ephemeral_public_key ∧
      initial.candidate.kem_ciphertext = capability.pending.kem_ciphertext := by
  obtain ⟨_, _, _, _, _, prepareRun⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding
      control pin availability capability application initial actual
  exact prepared control capability.pending pin.binding availability initial.candidate prepareRun

end BeaconcryptCore.Computational.RegistrationNativeServerPublicContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.prepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.initial
