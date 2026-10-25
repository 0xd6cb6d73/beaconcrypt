-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction

/-! Exact source transport admission, with total checked arithmetic and retained borrowed views. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Refinement.Transport

def absLength : core.option.Option Std.Usize → Option Nat
  | .None => none
  | .Some length => some length.val

/-- Checked native addition always returns normally and preserves the exact natural sum, or reports its overflow. -/
theorem checked_add_exact (left right : Std.Usize) :
    ∃ result, core.num.Usize.checked_add left right = ok result ∧
      absLength result = if left.val + right.val ≤ UScalar.max .Usize then
        some (left.val + right.val) else none := by
  have overflow := UScalar.overflowing_add_eq left right
  by_cases bounded : left.val + right.val ≤ UScalar.max .Usize
  · have noOverflow := (ite_eq_right (Nat.not_lt.mpr bounded) ▸ overflow)
    refine ⟨.Some (UScalar.overflowing_add left right).1, ?_, ?_⟩
    · simp [core.num.Usize.checked_add, core.num.Usize.overflowing_add,
        rust_primitives.arithmetic.overflowing_add_usize]
      dsimp! only
      simp [noOverflow.2]
    · simp [absLength, noOverflow.1, bounded]
  · have hasOverflow := (ite_eq_left (Nat.lt_of_not_ge bounded) ▸ overflow)
    refine ⟨.None, ?_, ?_⟩
    · simp [core.num.Usize.checked_add, core.num.Usize.overflowing_add,
        rust_primitives.arithmetic.overflowing_add_usize]
      dsimp! only
      simp [hasOverflow.2]
    · simp [absLength, bounded]

def overflowCap (length : Nat) : Option Nat :=
  if length ≤ UScalar.max .Usize then some length else none

def addLength (state : Option Nat) (extra : Nat) : Option Nat :=
  match state with
  | none => none
  | some length => overflowCap (length + extra)

/-- Once a positive length sum overflows, no later nonnegative field can recover it. -/
theorem overflowCap_add (length extra : Nat) :
    addLength (overflowCap length) extra = overflowCap (length + extra) := by
  by_cases bounded : length ≤ UScalar.max .Usize
  · simp [overflowCap, addLength, bounded]
  · have tooLarge : ¬length + extra ≤ UScalar.max .Usize := by omega
    simp [overflowCap, addLength, bounded, tooLarge]

/-- The complete-message limit is representable on every supported pointer width. -/
theorem message_limit_representable : 33_554_432 ≤ UScalar.max .Usize := by
  scalar_tac

/-- Widening a native slice length to the CBOR u64 domain loses no bits. -/
theorem usize_to_u64_value (length : Std.Usize) :
    (UScalar.cast .U64 length).val = length.val := by
  simp only [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  change length.val < 18_446_744_073_709_551_616
  have range : length.val < 2 ^ System.Platform.numBits := length.bv.isLt
  rcases System.Platform.numBits_eq with bits | bits <;> simp only [bits] at range <;> omega

def messageCap (length : Nat) : Option Nat :=
  if length ≤ 33_554_432 then some length else none

def finishLength (state : Option Nat) : Option Nat :=
  match state with
  | none => none
  | some length => messageCap length

/-- Intermediate checked-add overflow cannot hide an encoding that fits the complete-message limit. -/
theorem finish_overflowCap (length : Nat) :
    finishLength (overflowCap length) = messageCap length := by
  by_cases bounded : length ≤ UScalar.max .Usize
  · simp [overflowCap, finishLength, bounded]
  · have tooLarge : ¬length ≤ 33_554_432 := by
      have := message_limit_representable
      omega
    simp [overflowCap, finishLength, messageCap, bounded, tooLarge]

/-- The source parser gate is the inclusive complete-message bound, on either modeled pointer width. -/
theorem complete_message_size_admitted_exact (length : Std.Usize) :
    transport.complete_message_size_admitted length = ok (decide (length.val ≤ 33_554_432)) := by
  simp [transport.complete_message_size_admitted, transport.MAX_MESSAGE_SIZE, UScalar.le_equiv]

/-- Sender admission returns exactly the parsed metadata and payload, or rejects before the ratchet is consulted. -/
theorem frame_admission_exact (sequence sender : Std.U64) (ciphertext : Slice Std.U8)
    (expectedSender : Std.U64) :
    transport.admit_frame sequence sender ciphertext expectedSender =
      ok (if sender = expectedSender then
        .Some (⟨sequence, sender, ciphertext⟩ : transport.FrameView) else .None) := by
  by_cases same : sender = expectedSender <;> simp [transport.admit_frame, same]

/-- Core selects the owned witness only for an omitted application and retains every provided byte view. -/
theorem normalize_registration_application_exact (application : core.option.Option (Slice Std.U8)) :
    transport.normalize_registration_application application = ok (match application with
      | .None => .Witness transport.REGISTRATION_WITNESS
      | .Some bytes => .Provided bytes) := by
  cases application <;> rfl

/-- Mathematical view of the selected descriptor. The native adapter's borrowing of this view remains external. -/
def selectedApplicationBytes : transport.RegistrationApplication → List Std.U8
  | .Witness bytes => bytes.val
  | .Provided bytes => bytes.val

/-- Actual normalization retains provided bytes, including empty input, and selects the one-byte default for None. -/
theorem normalization_selected_bytes_exact (application : core.option.Option (Slice Std.U8)) :
    ∃ request, transport.normalize_registration_application application = ok request ∧
      selectedApplicationBytes request = (match application with
        | .None => [255#u8]
        | .Some bytes => bytes.val) := by
  cases application <;> refine ⟨_, rfl, ?_⟩ <;>
    simp [selectedApplicationBytes, transport.REGISTRATION_WITNESS, Std.Array.make]

end BeaconcryptCore.Refinement.Transport

/-- info: 'BeaconcryptCore.Refinement.Transport.checked_add_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.checked_add_exact

/-- info: 'BeaconcryptCore.Refinement.Transport.overflowCap_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.overflowCap_add
/-- info: 'BeaconcryptCore.Refinement.Transport.message_limit_representable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.message_limit_representable

/-- info: 'BeaconcryptCore.Refinement.Transport.usize_to_u64_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.usize_to_u64_value

/-- info: 'BeaconcryptCore.Refinement.Transport.finish_overflowCap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.finish_overflowCap

/-- info: 'BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact

/-- info: 'BeaconcryptCore.Refinement.Transport.frame_admission_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.frame_admission_exact

/-- info: 'BeaconcryptCore.Refinement.Transport.normalize_registration_application_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.normalize_registration_application_exact

/-- info: 'BeaconcryptCore.Refinement.Transport.normalization_selected_bytes_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.Transport.normalization_selected_bytes_exact
