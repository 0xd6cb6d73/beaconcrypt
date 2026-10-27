-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.Transport
import BeaconcryptCore.Refinement.PqxdhCore
import BeaconcryptCore.Computational.CborSizing

/-!
Exact source sizing correspondence for the complete current transport layouts. The source-operation correspondence theorems run the current extracted function and relate its actual optional reply to the mathematical complete-message size. Native codec execution, allocation and compiler correspondence remain external.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.Transport
open PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Computational.TransportSizingBridge

/-- All six request byte fields, including the ML public key and signature. -/
def initLength (lengths : Array Std.Usize 6#usize) : Nat :=
  3 + CborSizing.byteStringLen lengths.val[0]!.val +
    CborSizing.byteStringLen lengths.val[1]!.val +
    CborSizing.byteStringLen lengths.val[2]!.val +
    CborSizing.byteStringLen lengths.val[3]!.val +
    CborSizing.byteStringLen lengths.val[4]!.val +
    CborSizing.byteStringLen lengths.val[5]!.val

/-- All five response byte fields and its assigned identifier in schema order. -/
def responseLength (lengths : Array Std.Usize 5#usize) (assigned : Std.U64) : Nat :=
  3 + CborSizing.byteStringLen lengths.val[0]!.val +
    CborSizing.byteStringLen lengths.val[1]!.val +
    CborSizing.byteStringLen lengths.val[2]!.val +
    CborSizing.byteStringLen lengths.val[3]!.val + CborSizing.argumentLen assigned.val +
    CborSizing.byteStringLen lengths.val[4]!.val

/-- A represented successful checked sum has exactly the supplied mathematical value. -/
theorem cap_some_value (value : Std.Usize) (total : Nat)
    (represented : absLength (.Some value) = overflowCap total) : value.val = total := by
  by_cases bounded : total ≤ UScalar.max .Usize
  · simpa [absLength, overflowCap, bounded] using represented
  · simp [absLength, overflowCap, bounded] at represented

/-- An absent checked sum certifies overflow of its exact mathematical value. -/
theorem cap_none_unbounded (total : Nat)
    (represented : absLength .None = overflowCap total) : ¬total ≤ UScalar.max .Usize := by
  intro bounded
  simp [absLength, overflowCap, bounded] at represented

/-- A total containing an overflowing nonnegative subtotal cannot fit the complete-message limit. -/
theorem message_cap_overflow (subtotal total : Nat)
    (overflow : ¬subtotal ≤ UScalar.max .Usize) (included : subtotal ≤ total) : messageCap total = none := by
  have representable := message_limit_representable
  have tooLarge : ¬total ≤ 33_554_432 := by omega
  simp [messageCap, tooLarge]

/-- Every mathematical frame includes its whole ciphertext payload. -/
theorem frame_payload_le (sequence sender payload : Nat) :
    payload ≤ CborSizing.frameLen sequence sender payload := by
  unfold CborSizing.frameLen CborSizing.byteStringLen
  omega

/-- Every mathematical response includes its whole protected application payload. -/
theorem response_payload_le (payload assigned : Nat) :
    payload ≤ CborSizing.responseLen payload assigned := by
  unfold CborSizing.responseLen CborSizing.byteStringLen
  omega

/-- The source protected-record overhead is exactly the 64-byte commitment and 16-byte tag. -/
theorem message_overhead_exact : record.MESSAGE_OVERHEAD = ok 80#usize := by
  simpa only [record.MESSAGE_OVERHEAD, record.COMMITMENT_SIZE, commitment.AEAD_TAG_SIZE] using
    usize_add_eq 64#usize 16#usize 80#usize (by simp)

/-- The actual source selects exactly the canonical CBOR argument width. -/
theorem argument_len_exact (value : Std.U64) :
    ∃ width, transport.argument_len value = ok width ∧
      width.val = CborSizing.argumentLen value.val := by
  simp only [transport.argument_len, UScalar.le_equiv]
  split_ifs <;> refine ⟨_, rfl, ?_⟩
  all_goals simp_all [CborSizing.argumentLen]
  all_goals split_ifs <;> omega

/-- The actual accumulator starts with exactly the array/version/kind prefix. -/
theorem cbor_length_new_exact :
    ∃ state, transport.CborLength.new = ok state ∧
      absLength state.value = overflowCap 3 := by
  refine ⟨⟨.Some 3#usize⟩, rfl, ?_⟩
  have bounded : 3 ≤ UScalar.max .Usize := Nat.le_trans (by decide) message_limit_representable
  simp [absLength, overflowCap, bounded]

/-- Appending an integer uses its exact canonical argument width and checked native addition. -/
theorem cbor_length_integer_exact (state : transport.CborLength) (value : Std.U64) :
    ∃ next, transport.CborLength.integer state value = ok next ∧
      absLength next.value = addLength (absLength state.value) (CborSizing.argumentLen value.val) := by
  cases valueEq : state.value with
  | none => exact ⟨⟨.None⟩, by simp [transport.CborLength.integer, valueEq], rfl⟩
  | some length =>
    obtain ⟨width, widthRun, widthValue⟩ := argument_len_exact value
    obtain ⟨reply, replyRun, replyValue⟩ := checked_add_exact length width
    refine ⟨⟨reply⟩, by simp [transport.CborLength.integer, valueEq, widthRun, replyRun], ?_⟩
    simpa [absLength, addLength, overflowCap, widthValue] using replyValue

/-- Appending a byte string includes its own header and every payload byte. -/
theorem cbor_length_bytes_exact (state : transport.CborLength) (byteLength : Std.Usize) :
    ∃ next, transport.CborLength.bytes state byteLength = ok next ∧
      absLength next.value =
        addLength (addLength (absLength state.value) (CborSizing.argumentLen byteLength.val)) byteLength.val := by
  obtain ⟨header, headerRun, headerValue⟩ := cbor_length_integer_exact state (UScalar.cast .U64 byteLength)
  rw [usize_to_u64_value] at headerValue
  cases headerEq : header.value with
  | none =>
    refine ⟨⟨.None⟩, by simp [transport.CborLength.bytes, lift, headerRun, headerEq], ?_⟩
    rw [← headerValue, headerEq]
    rfl
  | some length =>
    obtain ⟨reply, replyRun, replyValue⟩ := checked_add_exact length byteLength
    refine ⟨⟨reply⟩, by simp [transport.CborLength.bytes, lift, headerRun, headerEq, replyRun], ?_⟩
    rw [← headerValue, headerEq]
    simpa [absLength, addLength, overflowCap] using replyValue

/-- Finishing admits exactly the inclusive complete-message bound. -/
theorem cbor_length_finish_exact (state : transport.CborLength) :
    ∃ reply, transport.CborLength.finish state = ok reply ∧
      absLength reply = finishLength (absLength state.value) := by
  cases valueEq : state.value with
  | none => exact ⟨.None, by simp [transport.CborLength.finish, valueEq], rfl⟩
  | some length =>
    by_cases admitted : length.val ≤ 33_554_432
    · exact ⟨.Some length,
        by simp [transport.CborLength.finish, valueEq, complete_message_size_admitted_exact, admitted],
        by simp [finishLength, absLength, messageCap, admitted]⟩
    · exact ⟨.None,
        by simp [transport.CborLength.finish, valueEq, complete_message_size_admitted_exact, admitted],
        by simp [finishLength, absLength, messageCap, admitted]⟩

/-- The actual frame sizing operation returns its complete mathematical size exactly when admitted. -/
theorem encoded_frame_len_exact (sequence sender : Std.U64) (ciphertextLength : Std.Usize) :
    ∃ reply, transport.encoded_frame_len sequence sender ciphertextLength = ok reply ∧
      absLength reply = messageCap (CborSizing.frameLen sequence.val sender.val ciphertextLength.val) := by
  obtain ⟨start, startRun, startValue⟩ := cbor_length_new_exact
  obtain ⟨withSequence, sequenceRun, sequenceValue⟩ := cbor_length_integer_exact start sequence
  obtain ⟨withSender, senderRun, senderValue⟩ := cbor_length_integer_exact withSequence sender
  obtain ⟨withPayload, payloadRun, payloadValue⟩ := cbor_length_bytes_exact withSender ciphertextLength
  obtain ⟨reply, finishRun, finishValue⟩ := cbor_length_finish_exact withPayload
  refine ⟨reply, by simp [transport.encoded_frame_len, startRun, sequenceRun, senderRun, payloadRun, finishRun], ?_⟩
  simpa only [payloadValue, senderValue, sequenceValue, startValue, overflowCap_add, finish_overflowCap,
    CborSizing.frameLen, CborSizing.byteStringLen, Nat.add_assoc] using finishValue

/-- The actual request operation accounts for all six independently sized byte fields. -/
theorem encoded_init_len_exact (lengths : Array Std.Usize 6#usize) :
    ∃ reply, transport.encoded_init_len lengths = ok reply ∧
      absLength reply = messageCap (initLength lengths) := by
  obtain ⟨start, startRun, startValue⟩ := cbor_length_new_exact
  obtain ⟨field0, field0Run, field0Value⟩ := cbor_length_bytes_exact start lengths.val[0]!
  obtain ⟨field1, field1Run, field1Value⟩ := cbor_length_bytes_exact field0 lengths.val[1]!
  obtain ⟨field2, field2Run, field2Value⟩ := cbor_length_bytes_exact field1 lengths.val[2]!
  obtain ⟨field3, field3Run, field3Value⟩ := cbor_length_bytes_exact field2 lengths.val[3]!
  obtain ⟨field4, field4Run, field4Value⟩ := cbor_length_bytes_exact field3 lengths.val[4]!
  obtain ⟨field5, field5Run, field5Value⟩ := cbor_length_bytes_exact field4 lengths.val[5]!
  obtain ⟨reply, finishRun, finishValue⟩ := cbor_length_finish_exact field5
  refine ⟨reply, by simp only [transport.encoded_init_len, startRun,
      index_usize_eq lengths 0#usize (by simp),
      index_usize_eq lengths 1#usize (by simp),
      index_usize_eq lengths 2#usize (by simp),
      index_usize_eq lengths 3#usize (by simp),
      index_usize_eq lengths 4#usize (by simp),
      index_usize_eq lengths 5#usize (by simp),
      show (0#usize).val = 0 by simp, show (1#usize).val = 1 by simp,
      show (2#usize).val = 2 by simp, show (3#usize).val = 3 by simp,
      show (4#usize).val = 4 by simp, show (5#usize).val = 5 by simp,
      field0Run, field1Run, field2Run, field3Run, field4Run, field5Run, finishRun, bind_tc_ok], ?_⟩
  simpa only [field5Value, field4Value, field3Value, field2Value, field1Value, field0Value,
    startValue, overflowCap_add, finish_overflowCap, initLength, CborSizing.byteStringLen, Nat.add_assoc]
    using finishValue

/-- The actual response operation accounts for all five byte fields and the assigned identifier. -/
theorem encoded_response_len_exact (lengths : Array Std.Usize 5#usize) (assigned : Std.U64) :
    ∃ reply, transport.encoded_response_len lengths assigned = ok reply ∧
      absLength reply = messageCap (responseLength lengths assigned) := by
  obtain ⟨start, startRun, startValue⟩ := cbor_length_new_exact
  obtain ⟨field0, field0Run, field0Value⟩ := cbor_length_bytes_exact start lengths.val[0]!
  obtain ⟨field1, field1Run, field1Value⟩ := cbor_length_bytes_exact field0 lengths.val[1]!
  obtain ⟨field2, field2Run, field2Value⟩ := cbor_length_bytes_exact field1 lengths.val[2]!
  obtain ⟨field3, field3Run, field3Value⟩ := cbor_length_bytes_exact field2 lengths.val[3]!
  obtain ⟨withAssigned, assignedRun, assignedValue⟩ := cbor_length_integer_exact field3 assigned
  obtain ⟨field4, field4Run, field4Value⟩ := cbor_length_bytes_exact withAssigned lengths.val[4]!
  obtain ⟨reply, finishRun, finishValue⟩ := cbor_length_finish_exact field4
  refine ⟨reply, by simp only [transport.encoded_response_len, startRun,
      index_usize_eq lengths 0#usize (by simp),
      index_usize_eq lengths 1#usize (by simp),
      index_usize_eq lengths 2#usize (by simp),
      index_usize_eq lengths 3#usize (by simp),
      index_usize_eq lengths 4#usize (by simp),
      show (0#usize).val = 0 by simp,
      show (1#usize).val = 1 by simp,
      show (2#usize).val = 2 by simp,
      show (3#usize).val = 3 by simp,
      show (4#usize).val = 4 by simp,
      field0Run, field1Run, field2Run, field3Run, assignedRun, field4Run, finishRun, bind_tc_ok], ?_⟩
  simpa only [field4Value, assignedValue, field3Value, field2Value, field1Value, field0Value,
    startValue, overflowCap_add, finish_overflowCap, responseLength, CborSizing.byteStringLen, Nat.add_assoc]
    using finishValue

/-- The current response's full fixed crypto-field profile specializes the actual five-field source operation. -/
theorem encoded_current_response_len_exact (payloadLength : Std.Usize) (assigned : Std.U64) :
    ∃ reply, transport.encoded_response_len
      (Array.make 5#usize [pqxdh.SIGN_PUBLIC_KEY_SIZE, pqxdh.X25519_PUBLIC_KEY_SIZE,
        pqxdh.MLKEM768_CIPHERTEXT_SIZE, payloadLength, authentication.MLDSA_SIGNATURE_LEN]) assigned = ok reply ∧
      absLength reply = messageCap (CborSizing.responseLen payloadLength.val assigned.val) := by
  exact (encoded_response_len_exact
    (Array.make 5#usize [pqxdh.SIGN_PUBLIC_KEY_SIZE, pqxdh.X25519_PUBLIC_KEY_SIZE,
      pqxdh.MLKEM768_CIPHERTEXT_SIZE, payloadLength, authentication.MLDSA_SIGNATURE_LEN]) assigned).imp
    fun reply facts => ⟨facts.1, by simpa [responseLength, CborSizing.responseLen, Std.Array.make,
      pqxdh.SIGN_PUBLIC_KEY_SIZE, pqxdh.X25519_PUBLIC_KEY_SIZE, pqxdh.MLKEM768_CIPHERTEXT_SIZE,
      authentication.MLDSA_SIGNATURE_LEN] using facts.2⟩

/-- The actual current six-field registration-request sizing call returns exactly 6757 bytes. -/
theorem encoded_current_init_len_exact :
    ∃ reply, transport.encoded_init_len
      (Array.make 6#usize [33#usize, 98#usize, 98#usize, 1249#usize, 1952#usize, 3309#usize]) = ok reply ∧
      absLength reply = some 6757 := by
  exact (encoded_init_len_exact
    (Array.make 6#usize [33#usize, 98#usize, 98#usize, 1249#usize, 1952#usize, 3309#usize])).imp
    fun reply facts => ⟨facts.1, by simpa [initLength, messageCap, CborSizing.byteStringLen,
      CborSizing.argumentLen, Std.Array.make] using facts.2⟩

/-- Protected-frame sizing includes all eighty authentication bytes and the exact complete-message bound. -/
theorem protected_frame_len_exact (plaintextLength : Std.Usize) (sequence sender : Std.U64) :
    ∃ reply, transport.protected_frame_len plaintextLength sequence sender = ok reply ∧
      absLength reply = messageCap
        (CborSizing.frameLen sequence.val sender.val (plaintextLength.val + 80)) := by
  obtain ⟨selected, selectedRun, selectedSize⟩ := checked_add_exact plaintextLength 80#usize
  have represented : absLength selected = overflowCap (plaintextLength.val + 80) := by
    simpa [overflowCap] using selectedSize
  cases selected with
  | none =>
    refine ⟨.None, ?_, ?_⟩
    · simp only [transport.protected_frame_len, message_overhead_exact, selectedRun, bind_tc_ok]
    · exact (message_cap_overflow (plaintextLength.val + 80)
        (CborSizing.frameLen sequence.val sender.val (plaintextLength.val + 80))
        (cap_none_unbounded _ represented)
        (frame_payload_le sequence.val sender.val (plaintextLength.val + 80))).symm
  | some ciphertextLength =>
    have value := cap_some_value ciphertextLength (plaintextLength.val + 80) represented
    obtain ⟨reply, run, size⟩ := encoded_frame_len_exact sequence sender ciphertextLength
    refine ⟨reply, ?_, ?_⟩
    · simpa only [transport.protected_frame_len, message_overhead_exact, selectedRun, bind_tc_ok] using run
    · simpa only [value] using size

/-- Registration sizing includes the assigned-ID prefix, eighty authentication bytes and complete ML signature. -/
theorem registration_response_len_exact (applicationLength : Std.Usize) (assigned : Std.U64) :
    ∃ reply, transport.registration_response_len applicationLength assigned = ok reply ∧
      absLength reply = messageCap (CborSizing.responseLen (applicationLength.val + 88) assigned.val) := by
  obtain ⟨bound, boundRun, boundSize⟩ := checked_add_exact applicationLength 8#usize
  have representedBound : absLength bound = overflowCap (applicationLength.val + 8) := by
    simpa [overflowCap] using boundSize
  cases bound with
  | none =>
    refine ⟨.None, ?_, ?_⟩
    · simp only [transport.registration_response_len, boundRun, bind_tc_ok]
    · exact (message_cap_overflow (applicationLength.val + 8)
        (CborSizing.responseLen (applicationLength.val + 88) assigned.val)
        (cap_none_unbounded _ representedBound)
        (by have := response_payload_le (applicationLength.val + 88) assigned.val; omega)).symm
  | some boundLength =>
    have boundValue := cap_some_value boundLength (applicationLength.val + 8) representedBound
    obtain ⟨cipher, cipherRun, cipherSize⟩ := checked_add_exact boundLength 80#usize
    have representedCipher : absLength cipher = overflowCap (applicationLength.val + 88) := by
      simpa [overflowCap, boundValue, Nat.add_assoc] using cipherSize
    cases cipher with
    | none =>
      refine ⟨.None, ?_, ?_⟩
      · simp only [transport.registration_response_len, boundRun, message_overhead_exact,
          cipherRun, bind_tc_ok]
      · exact (message_cap_overflow (applicationLength.val + 88)
          (CborSizing.responseLen (applicationLength.val + 88) assigned.val)
          (cap_none_unbounded _ representedCipher)
          (response_payload_le (applicationLength.val + 88) assigned.val)).symm
    | some ciphertextLength =>
      have value := cap_some_value ciphertextLength (applicationLength.val + 88) representedCipher
      obtain ⟨reply, run, size⟩ := encoded_current_response_len_exact ciphertextLength assigned
      refine ⟨reply, ?_, ?_⟩
      · simpa only [transport.registration_response_len, boundRun, message_overhead_exact,
          cipherRun, bind_tc_ok] using run
      · simpa only [value] using size


end BeaconcryptCore.Computational.TransportSizingBridge

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cap_some_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cap_some_value

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cap_none_unbounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cap_none_unbounded

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.message_cap_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.message_cap_overflow

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.frame_payload_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.frame_payload_le

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.response_payload_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.response_payload_le

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.message_overhead_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.message_overhead_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.argument_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.argument_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_new_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_new_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_integer_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_integer_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_bytes_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_bytes_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.cbor_length_finish_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.encoded_frame_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.encoded_frame_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.encoded_init_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.encoded_init_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.encoded_response_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.encoded_response_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_response_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_response_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_init_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.encoded_current_init_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.protected_frame_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.protected_frame_len_exact

/-- info: 'BeaconcryptCore.Computational.TransportSizingBridge.registration_response_len_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.TransportSizingBridge.registration_response_len_exact
