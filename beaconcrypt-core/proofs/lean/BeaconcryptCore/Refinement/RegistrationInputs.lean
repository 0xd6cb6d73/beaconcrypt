-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.TranscriptAuth
import BeaconcryptCore.PanicFreedom.Pqxdh

/-!
Exact decoded registration fields and primitive request operands. The generic slice facts below interpret the actual library operations used by the extraction; they add no opaque implementation or security assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationInputs

def hashBytes : registration.HashRequest → Pqxdh.Bytes
  | .Single input => TranscriptAuthParts.absSlice input
  | .Triple parts => TranscriptAuthParts.absParts parts

theorem slice_index_exact (bytes : Slice Std.U8) (index : Std.Usize)
    (inside : index.val < bytes.val.length) :
    rust_primitives.slice.slice_index bytes index = ok bytes.val[index.val]! := by
  simp [rust_primitives.slice.slice_index, Slice.index_usize,
    List.getElem?_eq_getElem inside, getElem!_pos bytes.val index.val inside]

theorem copied_byte_exact (size : Std.Usize) (bytes : Slice Std.U8) (index : Std.Usize)
    (inside : index.val < bytes.val.length) :
    core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (N := size) core.U8.Insts.CoreMarkerCopy bytes index = ok (bytes.val[index.val]!, bytes) := by
  simp [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
    slice_index_exact bytes index inside]

/-- Owned fixed-width conversion accepts exactly that width and copies every supplied byte. -/
theorem copied_slice_exact (size : Std.Usize) (bytes : Slice Std.U8) :
    ∃ result, core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
        size core.U8.Insts.CoreMarkerCopy bytes = ok result ∧
      match result with
      | .Ok output => output.val = bytes.val ∧ bytes.val.length = size.val
      | .Err _ => bytes.val.length ≠ size.val := by
  by_cases sameSize : bytes.val.length = size.val
  · obtain ⟨output, run, values⟩ := from_fn_pure size
      (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        size core.U8.Insts.CoreMarkerCopy) bytes (fun index => bytes.val[index]!)
      (fun index inside => by
        simpa only [Std.UScalar.val, BitVec.toNat_ofNat, UScalarTy.numBits,
          Nat.mod_eq_of_lt (lt_trans inside size.bv.isLt)] using
          copied_byte_exact size bytes ⟨BitVec.ofNat _ index⟩
            (by simpa only [Std.UScalar.val, BitVec.toNat_ofNat, UScalarTy.numBits,
              Nat.mod_eq_of_lt (lt_trans inside size.bv.isLt), sameSize] using inside))
    refine ⟨.Ok output, ?_, ?_, sameSize⟩
    · simp only [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
        rust_primitives.slice.slice_length, bind_tc_ok, UScalar.eq_equiv, Slice.len_val,
        Slice.length, sameSize, ↓reduceIte]
      simpa only [core.array.from_fn, bind_tc_ok] using
        congrArg (fun action => action >>= fun value =>
          ok (core.result.Result.Ok value : core.result.Result (Std.Array Std.U8 size)
            core.array.TryFromSliceError)) run
    · simpa only [← sameSize, map_range_getElem!] using values
  · refine ⟨.Err (), ?_, sameSize⟩
    simp [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from,
      rust_primitives.slice.slice_length, UScalar.eq_equiv, sameSize]

/-- Borrowed fixed-width conversion has the same exact width admission and byte identity. -/
theorem borrowed_slice_exact (size : Std.Usize) (bytes : Slice Std.U8) :
    ∃ result, core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
        size bytes = ok result ∧
      match result with
      | .Ok output => output.val = bytes.val ∧ bytes.val.length = size.val
      | .Err _ => bytes.val.length ≠ size.val := by
  by_cases sameSize : bytes.val.length = size.val
  all_goals simp [core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from,
    Aeneas.Std.core.array.TryFromSharedArraySlice.try_from, UScalar.eq_equiv, sameSize]

theorem copied_slice_total (size : Std.Usize) (bytes : Slice Std.U8) :
    ∃ result, core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      size core.U8.Insts.CoreMarkerCopy bytes = ok result :=
  (copied_slice_exact size bytes).imp (fun _ h => h.1)

theorem borrowed_slice_total (size : Std.Usize) (bytes : Slice Std.U8) :
    ∃ result, core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from
      size bytes = ok result :=
  (borrowed_slice_exact size bytes).imp (fun _ h => h.1)

def initPacketView (packet : registration.InitPacket)
    (identity prekey oneTime pq mldsa signature : Slice Std.U8) : Prop :=
  packet.identity_key.val = identity.val ∧ packet.pre_key.val = prekey.val ∧
    packet.one_time_key.val = oneTime.val ∧ packet.pq_key.val = pq.val ∧
    packet.mldsa_public_key.val = mldsa.val ∧ packet.signature.val = signature.val

def initWidths (identity prekey oneTime pq mldsa signature : Slice Std.U8) : Prop :=
  identity.val.length = 33 ∧ prekey.val.length = 98 ∧ oneTime.val.length = 98 ∧
    pq.val.length = 1249 ∧ mldsa.val.length = 1952 ∧ signature.val.length = 3309

/-- Init admission rejects exactly malformed widths and otherwise retains every supplied byte. -/
theorem init_packet_exact (identity prekey oneTime pq mldsa signature : Slice Std.U8) :
    ∃ result, registration.InitPacket.from_slices identity prekey oneTime pq mldsa signature = ok result ∧
      match result with
      | .Some packet => initPacketView packet identity prekey oneTime pq mldsa signature
      | .None => ¬ initWidths identity prekey oneTime pq mldsa signature := by
  obtain ⟨identityResult, identityRun, identityFacts⟩ := borrowed_slice_exact 33#usize identity
  obtain ⟨prekeyResult, prekeyRun, prekeyFacts⟩ := borrowed_slice_exact 98#usize prekey
  obtain ⟨oneTimeResult, oneTimeRun, oneTimeFacts⟩ := borrowed_slice_exact 98#usize oneTime
  obtain ⟨pqResult, pqRun, pqFacts⟩ := borrowed_slice_exact 1249#usize pq
  obtain ⟨mldsaResult, mldsaRun, mldsaFacts⟩ := borrowed_slice_exact 1952#usize mldsa
  obtain ⟨signatureResult, signatureRun, signatureFacts⟩ := borrowed_slice_exact 3309#usize signature
  all_goals cases identityResult
  all_goals cases prekeyResult
  all_goals cases oneTimeResult
  all_goals cases pqResult
  all_goals cases mldsaResult
  all_goals cases signatureResult
  all_goals simp_all [registration.InitPacket.from_slices, initPacketView, initWidths, Std.UScalar.ofNatCore_val_eq]

def responsePacketView (packet : registration.ResponsePacket)
    (identity ephemeral kem : Slice Std.U8) (keyId : Std.U64)
    (application signature : Slice Std.U8) : Prop :=
  packet.public.identity_key.val = identity.val ∧ packet.public.ephemeral_key.val = ephemeral.val ∧
    packet.public.kem_cipher_text.val = kem.val ∧ packet.public.key_id = keyId ∧
    packet.application = application ∧ packet.signature.val = signature.val

def responseWidths (identity ephemeral kem signature : Slice Std.U8) : Prop :=
  identity.val.length = 32 ∧ ephemeral.val.length = 32 ∧ kem.val.length = 1088 ∧
    signature.val.length = 3309

/-- Response admission retains the entire body and metadata and rejects exactly malformed fixed widths. -/
theorem response_packet_exact (identity ephemeral kem : Slice Std.U8) (keyId : Std.U64)
    (application signature : Slice Std.U8) :
    ∃ result, registration.ResponsePacket.from_slices identity ephemeral kem keyId application signature = ok result ∧
      match result with
      | .Some packet => responsePacketView packet identity ephemeral kem keyId application signature
      | .None => ¬ responseWidths identity ephemeral kem signature := by
  obtain ⟨identityResult, identityRun, identityFacts⟩ := copied_slice_exact 32#usize identity
  obtain ⟨ephemeralResult, ephemeralRun, ephemeralFacts⟩ := copied_slice_exact 32#usize ephemeral
  obtain ⟨kemResult, kemRun, kemFacts⟩ := copied_slice_exact 1088#usize kem
  obtain ⟨signatureResult, signatureRun, signatureFacts⟩ := borrowed_slice_exact 3309#usize signature
  all_goals cases identityResult
  all_goals cases ephemeralResult
  all_goals cases kemResult
  all_goals cases signatureResult
  all_goals simp_all [registration.ResponsePacket.from_slices, responsePacketView, responseWidths, Std.UScalar.ofNatCore_val_eq]

end BeaconcryptCore.Refinement.RegistrationInputs

/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.slice_index_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.slice_index_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.copied_byte_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.copied_byte_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.copied_slice_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.copied_slice_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.borrowed_slice_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.borrowed_slice_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.copied_slice_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.copied_slice_total
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.borrowed_slice_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.borrowed_slice_total
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.init_packet_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.init_packet_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInputs.response_packet_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInputs.response_packet_exact
