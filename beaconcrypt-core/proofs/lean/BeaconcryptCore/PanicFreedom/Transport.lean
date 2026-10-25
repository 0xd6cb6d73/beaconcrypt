-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.TransportSizingBridge

/-! Unconditional normal returns for transport admission, including oversized lengths, mismatched senders and every optional application. Native parsing and byte-view borrowing remain outside this source cohort. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.PanicFreedom.Transport

theorem complete_message_size_admitted_total (length : Std.Usize) :
    ∃ result, transport.complete_message_size_admitted length = ok result :=
  ⟨_, BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact length⟩

theorem admit_frame_total (sequence sender : Std.U64) (ciphertext : Slice Std.U8)
    (expectedSender : Std.U64) :
    ∃ result, transport.admit_frame sequence sender ciphertext expectedSender = ok result :=
  ⟨_, BeaconcryptCore.Refinement.Transport.frame_admission_exact sequence sender ciphertext expectedSender⟩

theorem normalize_registration_application_total (application : core.option.Option (Slice Std.U8)) :
    ∃ result, transport.normalize_registration_application application = ok result :=
  ⟨_, BeaconcryptCore.Refinement.Transport.normalize_registration_application_exact application⟩

theorem argument_len_total (value : Std.U64) :
    ∃ result, transport.argument_len value = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.argument_len_exact value).imp (fun _ normal => normal.1)

theorem cbor_length_new_total :
    ∃ result, transport.CborLength.new = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_new_exact).imp (fun _ normal => normal.1)

theorem cbor_length_integer_total (self : transport.CborLength) (value : Std.U64) :
    ∃ result, transport.CborLength.integer self value = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_integer_exact self value).imp (fun _ normal => normal.1)

theorem cbor_length_bytes_total (self : transport.CborLength) (byteLength : Std.Usize) :
    ∃ result, transport.CborLength.bytes self byteLength = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_bytes_exact self byteLength).imp (fun _ normal => normal.1)

theorem cbor_length_finish_total (self : transport.CborLength) :
    ∃ result, transport.CborLength.finish self = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_finish_exact self).imp (fun _ normal => normal.1)

theorem encoded_frame_len_total (sequence sender : Std.U64) (ciphertextLength : Std.Usize) :
    ∃ result, transport.encoded_frame_len sequence sender ciphertextLength = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.encoded_frame_len_exact sequence sender ciphertextLength).imp (fun _ normal => normal.1)

theorem encoded_init_len_total (lengths : Array Std.Usize 6#usize) :
    ∃ result, transport.encoded_init_len lengths = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.encoded_init_len_exact lengths).imp (fun _ normal => normal.1)

theorem encoded_response_len_total (lengths : Array Std.Usize 5#usize) (assigned : Std.U64) :
    ∃ result, transport.encoded_response_len lengths assigned = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.encoded_response_len_exact lengths assigned).imp (fun _ normal => normal.1)

theorem protected_frame_len_total (plaintextLength : Std.Usize) (sequence sender : Std.U64) :
    ∃ result, transport.protected_frame_len plaintextLength sequence sender = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.protected_frame_len_exact plaintextLength sequence sender).imp (fun _ normal => normal.1)

theorem registration_response_len_total (applicationLength : Std.Usize) (assigned : Std.U64) :
    ∃ result, transport.registration_response_len applicationLength assigned = ok result :=
  (BeaconcryptCore.Computational.TransportSizingBridge.registration_response_len_exact applicationLength assigned).imp (fun _ normal => normal.1)

end BeaconcryptCore.PanicFreedom.Transport

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.complete_message_size_admitted_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.complete_message_size_admitted_total
/-- info: 'BeaconcryptCore.PanicFreedom.Transport.admit_frame_total' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.admit_frame_total
/-- info: 'BeaconcryptCore.PanicFreedom.Transport.normalize_registration_application_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.normalize_registration_application_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.argument_len_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.argument_len_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.cbor_length_new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.cbor_length_new_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.cbor_length_integer_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.cbor_length_integer_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.cbor_length_bytes_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.cbor_length_bytes_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.cbor_length_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.cbor_length_finish_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.encoded_frame_len_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.encoded_frame_len_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.encoded_init_len_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.encoded_init_len_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.encoded_response_len_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.encoded_response_len_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.protected_frame_len_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.protected_frame_len_total

/-- info: 'BeaconcryptCore.PanicFreedom.Transport.registration_response_len_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.Transport.registration_response_len_total
