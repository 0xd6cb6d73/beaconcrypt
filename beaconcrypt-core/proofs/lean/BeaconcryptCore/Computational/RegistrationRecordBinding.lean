-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordPeerBinding
import BeaconcryptCore.Refinement.RegistrationAd

/-! Current record metadata is constructed only from a completed AD-hash continuation. Init acceptance alone has no record binding. Completion and publication preserve exact AD151, independently of ratchet secrecy assumptions. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationRecordBinding

open PqxdhRecordLiftInterface (PeerBinding)


def ofRegistration (binding : session.CompletedRegistrationBinding) : PeerBinding :=
  ⟨binding.beacon_identity_public_key, binding.associated_data⟩

theorem registration_associated_bytes (server : RawCtxServerRouting.Identity)
    (binding : session.CompletedRegistrationBinding) :
    (ofRegistration binding).associatedBytes server = absBytes binding.associated_data := by
  rfl

/-- The actual native completion operation transfers exactly the same peer identity and populated record AD. -/
theorem finish_native (binding : session.CompletedRegistrationBinding) (assigned : Std.U64)
    (established : session.SessionBinding) (finished : binding.finish assigned = .ok established) :
    PeerBinding.ofSession established = ofRegistration binding := by
  obtain ⟨result, ran, _, _, sameIdentity, _, sameAD, _⟩ :=
    BeaconcryptCore.Refinement.SessionBinding.finish_refines binding assigned
  have same : result = established := RustM.ok.inj (ran.symm.trans finished)
  cases same
  simp only [PeerBinding.ofSession, ofRegistration, sameIdentity, sameAD]

/-- Actual AD completion assembles the fixed context and exact returned digest before a record binding exists. -/
theorem complete_associated_data (pending : session.RegistrationBinding)
    (digest : Std.Array Std.U8 64#usize) (server : RawCtxServerRouting.Identity) :
    ∃ completed, pending.complete digest = .ok completed ∧
      (ofRegistration completed).associatedBytes server =
        BeaconcryptCore.Refinement.SessionBinding.boundAssociatedData (absBytes digest) := by
  obtain ⟨completed, ran, _, _, _, sameHash, consistent⟩ :=
    BeaconcryptCore.Refinement.SessionBinding.complete_refines pending digest
  exact ⟨completed, ran, by
    rw [registration_associated_bytes]
    simpa [BeaconcryptCore.Refinement.SessionBinding.registrationConsistent, sameHash] using consistent⟩

end BeaconcryptCore.Computational.RegistrationRecordBinding

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.registration_associated_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.registration_associated_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.finish_native

/-- info: 'BeaconcryptCore.Computational.RegistrationRecordBinding.complete_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRecordBinding.complete_associated_data
