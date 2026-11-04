-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperStorage
import BeaconcryptCore.Refinement.RegistrationByteCopy

/-! The selected Beacon finish wrapper copies the completed application before installing its ratchet. This is the actual standard byte-clone model: all U8 clone calls are retained, and byte contents and the enclosing RustM result are checked. Implicit physical heap exhaustion remains the standard platform boundary. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperCopy

set_option backward.isDefEq.respectTransparency false in
theorem bytes (input : Slice U8) :
    alloc.slice.Dummy.to_vec core.U8.Insts.CoreCloneClone input = .ok input := by
  simp only [alloc.slice.Dummy.to_vec, rust_primitives.sequence.seq_empty, bind_tc_ok,
    rust_primitives.sequence.seq_extend, RegistrationByteCopy.clone_bytes]
  simp only [Slice.new, List.nil_append]
  split
  · rfl
  · exact False.elim (‹¬input.val.length ≤ Usize.max› input.property)

variable [PublicWrapperPlatform.Material]

def install (completed : registration.CompletedBeacon) :
    RustM (Option (alloc.vec.Vec U8) × U64 × beaconcrypt_public_wrapper.beacon.BeaconState) := do
  let (control, binding, kernel, application) ← registration.CompletedBeacon.into_parts completed
  let plaintext ← alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone application
  let identifier ← PublicWrapperPlatform.assignedKeyId binding
  let manager ← beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel
  .ok (some plaintext, identifier,
    beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding manager)

set_option backward.isDefEq.respectTransparency false in
theorem install_exact (completed : registration.CompletedBeacon) :
    install completed = .ok (some completed.application, completed.binding.assigned_key_id,
      beaconcrypt_public_wrapper.beacon.BeaconState.Established completed.control completed.binding
        ⟨⟨some completed.kernel⟩⟩) := by
  cases completed
  simp only [install, registration.CompletedBeacon.into_parts, bind_tc_ok,
    alloc.slice.Slice.to_vec, bytes]
  rfl

end BeaconcryptCore.Refinement.AdapterPublicWrapperCopy

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.install_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.install_exact
