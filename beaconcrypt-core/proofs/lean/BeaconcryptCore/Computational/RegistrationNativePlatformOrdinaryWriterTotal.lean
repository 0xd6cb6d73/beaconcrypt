-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter
import BeaconcryptCore.Refinement.AdapterRecordFrameRejection
/-! The actual source Frame3 helper is interpreted on all byte-slice inputs. Prefix overflow, complete overflow and complete-message refusal are derived from the source checked arithmetic before allocation. Successful trusted serialization is the existing checked generated encoder. Only normal fallible reservation replies are selected here; arbitrary enclosing Rust failures remain in the generic source helper and outer driver. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal
open BeaconcryptCore.Refinement
open RegistrationNativePlatformOrdinaryWriter (write capacity)
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}

def frame (sequence sender : U64) (first second third : Slice U8) : RawCtxReceive.DecodedFrame :=
  ⟨sequence, sender, TranscriptAuthParts.absSlice first ++ TranscriptAuthParts.absSlice second ++ TranscriptAuthParts.absSlice third⟩

private theorem payload_length (sequence sender : U64) (first second third : Slice U8) :
    (frame sequence sender first second third).payload.length = first.val.length + second.val.length + third.val.length := by
  simp only [frame, TranscriptAuthParts.absSlice, List.length_append, List.length_map]

private theorem no_capacity (sequence sender : U64) (first second third : Slice U8)
    (subtotal : Nat) (overflow : ¬subtotal ≤ UScalar.max .Usize)
    (included : subtotal ≤ first.val.length + second.val.length + third.val.length) :
    capacity (frame sequence sender first second third) = none := by
  change Transport.messageCap (CborSizing.frameLen sequence.val sender.val (frame sequence sender first second third).payload.length) = none
  exact TransportSizingBridge.message_cap_overflow subtotal _ overflow
    ((included.trans (by rw [payload_length])).trans (TransportSizingBridge.frame_payload_le _ _ _))

/-- Actual source Frame3 writing equals the private canonical writer and its public capacity gate on every input, with source overflow and cap refusal derived internally. -/
theorem source [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (sequence sender : U64) (first second third : Slice U8) :
    RegistrationNativeExtractedAllocation.abstractResult <$>
      AdapterRecordFrameBytes.frame (fun _ size => .ok <$> reserve size.val)
        (AdapterRecordFrameBytes.serializer (m := m)) sequence sender first second third =
      .ok <$> write reserve (frame sequence sender first second third) := by
  obtain ⟨prefixReply, prefixRun, prefixValue⟩ := Transport.checked_add_exact first.len second.len
  cases prefixReply with
  | some prefixLength =>
      have prefixSum : first.val.length + second.val.length = prefixLength.val := by
        simpa only [Slice.len_val, Slice.length] using
          (TransportSizingBridge.cap_some_value prefixLength _ prefixValue).symm
      obtain ⟨payload, payloadRun, payloadValue⟩ := Transport.checked_add_exact prefixLength third.len
      cases payload with
      | some payloadLength =>
          have length : prefixLength.val + third.val.length = payloadLength.val := by
            simpa only [Slice.len_val, Slice.length] using
              (TransportSizingBridge.cap_some_value payloadLength _ payloadValue).symm
          obtain ⟨capacityReply, capacityRun, capacityValue⟩ := TransportSizingBridge.encoded_frame_len_exact sequence sender payloadLength
          cases capacityReply with
          | some sourceCapacity =>
              let payloadView : Slice U8 := ⟨first.val ++ second.val ++ third.val, by
                simp only [List.length_append]
                rw [prefixSum, length]
                scalar_tac⟩
              have payloadLen : payloadView.len = payloadLength := by
                apply UScalar.eq_of_val_eq
                simp only [Slice.len_val, Slice.length, payloadView, List.length_append]
                rw [prefixSum, length]
              have admitted : transport.encoded_frame_len sequence sender payloadView.len = .ok (.Some sourceCapacity) := by
                rw [payloadLen]
                exact capacityRun
              simpa only [frame, payloadView, TranscriptAuthParts.absSlice, List.map_append] using
                RegistrationNativePlatformOrdinaryWriter.source reserve sequence sender first second third payloadView prefixLength
                  sourceCapacity prefixSum rfl admitted
          | none =>
              rw [AdapterRecordFrameRejection.capacity_rejected _ _ sequence sender first second third prefixLength payloadLength prefixSum length capacityRun]
              have refused : capacity (frame sequence sender first second third) = none := by
                change Transport.messageCap _ = none
                rw [payload_length, prefixSum, length]
                exact capacityValue.symm
              simp only [write, refused, map_pure, RegistrationNativeExtractedAllocation.abstractResult,
                RegistrationNativeExtractedAllocation.output, Option.map_none]
      | none =>
          rw [AdapterRecordFrameRejection.total_rejected _ _ sequence sender first second third prefixLength prefixSum payloadRun]
          have overflow := TransportSizingBridge.cap_none_unbounded _ payloadValue
          have refused := no_capacity sequence sender first second third (prefixLength.val + third.len.val) overflow (by
            simp only [Slice.len_val, Slice.length]
            rw [prefixSum])
          simp only [write, refused, map_pure, RegistrationNativeExtractedAllocation.abstractResult,
            RegistrationNativeExtractedAllocation.output, Option.map_none]
  | none =>
      rw [AdapterRecordFrameRejection.sum_rejected _ _ sequence sender first second third prefixRun]
      have overflow := TransportSizingBridge.cap_none_unbounded _ prefixValue
      have refused := no_capacity sequence sender first second third (first.len.val + second.len.val) overflow (by
        simp only [Slice.len_val, Slice.length]
        omega)
      simp only [write, refused, map_pure, RegistrationNativeExtractedAllocation.abstractResult,
        RegistrationNativeExtractedAllocation.output, Option.map_none]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriterTotal.source
