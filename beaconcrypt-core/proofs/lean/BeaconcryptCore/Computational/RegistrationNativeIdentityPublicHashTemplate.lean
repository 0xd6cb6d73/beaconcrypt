-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate

/-! The actual source Init hash has a source-fixed64-byte signature window. Public framing extraction removes exactly that window and retains every other byte. Thus a source realization can reconstruct the physical address from public framing plus its private canonical signature, while the executable censor never receives that signature or address. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate
open BeaconcryptCore.Refinement
open PqxdhEd25519EufCma (Ed25519Signature)

def parts (bytes : Pqxdh.Bytes) : Pqxdh.Bytes × Pqxdh.Bytes := (bytes.take 4140, bytes.drop 4204)

/-- The constant window offset follows from the literal source tag/field widths. -/
theorem leading_length (state : registration.BeaconInitState) :
    (RegistrationNativeIdentityHashTemplate.leading state).length = 4140 := by
  simp only [RegistrationNativeIdentityHashTemplate.leading, Pqxdh.TranscriptAuth.hashField,
    List.length_append, Pqxdh.LE64_length, Pqxdh.TranscriptAuth.literal_lengths.2.1, absBytes_length]
  rfl

/-- Framing extraction discards exactly the selected signature, independent of its value. -/
theorem extracted (leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature) (width : leading.length = 4140) :
    parts (leading ++ signature.toList ++ trailing) = (leading, trailing) := by
  have signed : signature.toList.length = 64 := signature.2
  have total : (leading ++ signature.toList).length = 4204 := by simp only [List.length_append, width, signed]
  apply Prod.ext
  · have taken : (leading ++ (signature.toList ++ trailing)).take leading.length = leading := by rw [List.take_left]
    simpa only [parts, List.append_assoc, width] using taken
  · have dropped : ((leading ++ signature.toList) ++ trailing).drop (leading ++ signature.toList).length = trailing := by
      rw [List.drop_append_length]
    simpa only [parts, List.append_assoc, total] using dropped

/-- The actual successful fingerprint continuation supplies the physical request and its public framing; reconstruction uses only the private source signature. -/
theorem source (pending : registration.BeaconFingerprint) (digest : Std.Array U8 64#usize)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : absBytes pending.state.one_time_key = signature.toList ++ message) :
    ∃ next request, pending.resume (.Some digest) = .ok (.HashRequested next) ∧ next.request = .ok request ∧
      parts (RegistrationInputs.hashBytes request) =
        (RegistrationNativeIdentityHashTemplate.leading pending.state, RegistrationNativeIdentityHashTemplate.trailing pending.state message) ∧
      RegistrationInputs.hashBytes request = (parts (RegistrationInputs.hashBytes request)).1 ++ signature.toList ++
        (parts (RegistrationInputs.hashBytes request)).2 := by
  obtain ⟨next, request, resumed, requested, literal⟩ := RegistrationNativeIdentityHashTemplate.source pending digest signature message attached
  have framing := extracted (RegistrationNativeIdentityHashTemplate.leading pending.state)
    (RegistrationNativeIdentityHashTemplate.trailing pending.state message) signature (leading_length pending.state)
  refine ⟨next, request, resumed, requested, literal ▸ framing, ?_⟩
  rw [literal, framing]

end BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.leading_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.leading_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.extracted' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.extracted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate.source
