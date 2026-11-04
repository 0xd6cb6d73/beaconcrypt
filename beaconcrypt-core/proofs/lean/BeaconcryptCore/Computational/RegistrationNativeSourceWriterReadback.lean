-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceWire
import BeaconcryptCore.Refinement.RegistrationSourceWriterBody
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Successful source runtime writers produce the source codec bytes. The complete source request program is interpreted with arbitrary effectful reservation, including failure and its poststate. Only std reservation's preservation of initialized elements is used. No theorem makes every allocation succeed or identifies the runtime writer with the pure serialization representation. -/
namespace BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback
open BeaconcryptCore.Refinement RegistrationNativeSourceEncoders
open RegistrationSerializerReachableSource AdapterRegistrationWriterRequestMonad
variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def initVector (view : registration.SignedInitView) : alloc.vec.Vec U8 :=
  ⟨136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view), by
    rw [List.length_cons, RegistrationPublicReadback.init_payload_length _ (init_shape view)]
    scalar_tac⟩

def responseVector (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) : alloc.vec.Vec U8 :=
  ⟨136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view), by
    rw [List.length_cons, RegistrationPublicReadback.response_payload_length _ (response_shape view)]
    simpa only [UScalar.max_USize_eq] using admitted.trans Transport.message_limit_representable⟩

theorem array_length {size : Usize} (array : Array U8 size) : array.to_slice.len = size := by
  apply UScalar.eq_of_val_eq
  simp only [Slice.len_val, Array.length_to_slice]

set_option backward.isDefEq.respectTransparency false in
theorem init_capacity (view : registration.SignedInitView) :
    transport.encoded_init_len (Array.make 6#usize [(initSyntax view).identity_key.len, (initSyntax view).pre_key.len,
      (initSyntax view).one_time_key.len, (initSyntax view).pq_key.len, (initSyntax view).mldsa_public_key.len,
      (initSyntax view).signature.len]) = .ok (.Some 6757#usize) := by
  simp only [initSyntax, array_length]
  obtain ⟨reply, run, represented⟩ := TransportSizingBridge.encoded_current_init_len_exact
  cases reply with
  | none => contradiction
  | some capacity =>
    have value : capacity = 6757#usize := by
      apply UScalar.eq_of_val_eq
      exact _root_.Option.some.inj represented
    simpa only [value] using run

set_option backward.isDefEq.respectTransparency false in
theorem init_body (reserve : Usize → m (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.SignedInitView) :
    simulateQ (RegistrationSourceWriterBody.platform reserve
        (@beaconcrypt_parse.extraction_encode_init (operations other))
        (@beaconcrypt_parse.extraction_encode_response (operations other)))
      (Lifted.writeInit (E := E) (m := Program E) 6757#usize (initSyntax view)).run =
      (fun allocation => (RustM.ok (match allocation with
        | .Err _ => core.option.Option.None
        | .Ok _ => .Some (initVector view)))) <$> reserve 6757#usize := by
  obtain ⟨after, encoded, _, bytes⟩ := RegistrationNativeSourceEncoders.init_bytes other view
    (AdapterWireVector.zeros 6757#usize) (by simp only [AdapterWireVector.zeros, Slice.length, List.length_replicate]; scalar_tac)
  have actual : @beaconcrypt_parse.extraction_encode_init (operations other) (initSyntax view)
      (AdapterWireVector.zeros 6757#usize) = .ok (6757#usize, after) := encoded
  rw [RegistrationSourceWriterBody.init reserve _ _ _ _ _ _ actual]
  have truncated : AdapterWireVector.take after 6757#usize = initVector view := by
    apply Subtype.ext
    change after.val.take 6757 = _
    rw [bytes]
    have length : (136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)).length = 6757 := by
      rw [List.length_cons, RegistrationPublicReadback.init_payload_length _ (init_shape view)]
    exact List.take_left' length
  congr 1
  funext allocation
  cases allocation <;> simp only [RegistrationSourceWriterBody.reply,
    show ¬ (6757#usize = 0#usize) by decide, ↓reduceIte, truncated]

set_option backward.isDefEq.respectTransparency false in
theorem init_source (reserve : Usize → m (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.SignedInitView) :
    simulateQ (RegistrationSourceWriterBody.platform reserve
        (@beaconcrypt_parse.extraction_encode_init (operations other))
        (@beaconcrypt_parse.extraction_encode_response (operations other)))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := Program E) (initSyntax view)).run =
      (fun allocation => (RustM.ok (match allocation with
        | .Err _ => core.option.Option.None
        | .Ok _ => .Some (initVector view)))) <$> reserve 6757#usize := by
  simp! only [AdapterRegistrationWriterRequestExtraction.encodeInit, Lifted.len,
    core.slice.Slice.len, rust_primitives.slice.slice_length, Lifted.initCapacity,
    Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure, pure_bind,
    bind_tc_ok, init_capacity, Lifted.branch, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch]
  exact init_body reserve other view

set_option backward.isDefEq.respectTransparency false in
theorem response_capacity (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    ∃ capacity, transport.encoded_response_len
        (Array.make 5#usize [(responseSyntax view).identity_key.len, (responseSyntax view).ephemeral_key.len,
          (responseSyntax view).kem_cipher_text.len, (responseSyntax view).app_cipher_text.len,
          (responseSyntax view).signature.len]) (responseSyntax view).key_id = .ok (.Some capacity) ∧
      capacity.val = RegistrationSerializerResponseBytes.totalLength (responseSyntax view) := by
  obtain ⟨reply, run, represented⟩ := RegistrationSerializerResponseBytes.source_capacity (responseSyntax view) (response_shape view)
  change RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ 33554432 at admitted
  rw [Transport.messageCap, ite_eq_left admitted] at represented
  cases reply with
  | none => contradiction
  | some capacity => exact ⟨capacity, run, _root_.Option.some.inj represented⟩

set_option backward.isDefEq.respectTransparency false in
theorem response_body (reserve : Usize → m (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.SignedResponseView) (capacity : Usize)
    (capacityValue : capacity.val = RegistrationSerializerResponseBytes.totalLength (responseSyntax view))
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    simulateQ (RegistrationSourceWriterBody.platform reserve
        (@beaconcrypt_parse.extraction_encode_init (operations other))
        (@beaconcrypt_parse.extraction_encode_response (operations other)))
      (Lifted.writeResponse (E := E) (m := Program E) capacity (responseSyntax view)).run =
      (fun allocation => (RustM.ok (match allocation with
        | .Err _ => core.option.Option.None
        | .Ok _ => .Some (responseVector view admitted)))) <$> reserve capacity := by
  obtain ⟨after, encoded, _, bytes, cursor⟩ := RegistrationNativeSourceEncoders.response_bytes other view
    (AdapterWireVector.zeros capacity) (by simp only [AdapterWireVector.zeros, Slice.length, List.length_replicate]; omega) admitted
  have actual : @beaconcrypt_parse.extraction_encode_response (operations other) (responseSyntax view)
      (AdapterWireVector.zeros capacity) = .ok (RegistrationSerializerResponseBytes.finalCursor (responseSyntax view), after) := encoded
  rw [RegistrationSourceWriterBody.response reserve _ _ _ _ _ _ actual]
  have truncated : AdapterWireVector.take after (RegistrationSerializerResponseBytes.finalCursor (responseSyntax view)) = responseVector view admitted := by
    apply Subtype.ext
    change after.val.take (RegistrationSerializerResponseBytes.finalCursor (responseSyntax view)).val = _
    rw [bytes, cursor]
    exact List.take_left' (RegistrationPublicReadback.response_payload_length _ (response_shape view))
  have nonzero : RegistrationSerializerResponseBytes.finalCursor (responseSyntax view) ≠ 0#usize := by
    intro zero
    have value := congrArg UScalar.val zero
    rw [cursor] at value
    change RegistrationSerializerResponseBytes.totalLength (responseSyntax view) = 0 at value
    unfold RegistrationSerializerResponseBytes.totalLength at value
    omega
  congr 1
  funext allocation
  cases allocation <;> simp only [RegistrationSourceWriterBody.reply, nonzero, ↓reduceIte, truncated]

set_option backward.isDefEq.respectTransparency false in
theorem response_source (reserve : Usize → m (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    ∃ capacity, capacity.val = RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ∧
      simulateQ (RegistrationSourceWriterBody.platform reserve
          (@beaconcrypt_parse.extraction_encode_init (operations other))
          (@beaconcrypt_parse.extraction_encode_response (operations other)))
        (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := Program E) (responseSyntax view)).run =
        (fun allocation => (RustM.ok (match allocation with
          | .Err _ => core.option.Option.None
          | .Ok _ => .Some (responseVector view admitted)))) <$> reserve capacity := by
  obtain ⟨capacity, capacityRun, capacityValue⟩ := response_capacity view admitted
  refine ⟨capacity, capacityValue, ?_⟩
  simp! only [AdapterRegistrationWriterRequestExtraction.encodeResponse, Lifted.len,
    core.slice.Slice.len, rust_primitives.slice.slice_length, Lifted.responseCapacity,
    Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure, pure_bind,
    bind_tc_ok, capacityRun, Lifted.branch, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch]
  exact response_body reserve other view capacity capacityValue admitted

set_option backward.isDefEq.respectTransparency false in
omit [LawfulMonad m] in
theorem response_rejected (reserve : Usize → m (core.result.Result Unit E))
    (other : OtherBranches) (view : registration.SignedResponseView)
    (outside : CborSizing.maxMessageSize < RegistrationSerializerResponseBytes.totalLength (responseSyntax view)) :
    simulateQ (RegistrationSourceWriterBody.platform reserve
        (@beaconcrypt_parse.extraction_encode_init (operations other))
        (@beaconcrypt_parse.extraction_encode_response (operations other)))
      (AdapterRegistrationWriterRequestExtraction.encodeResponse (E := E) (m := Program E) (responseSyntax view)).run =
      pure (RustM.ok core.option.Option.None) := by
  obtain ⟨reply, capacityRun, represented⟩ := RegistrationSerializerResponseBytes.source_capacity (responseSyntax view) (response_shape view)
  have rejected : ¬ RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ 33554432 := Nat.not_le_of_gt outside
  rw [Transport.messageCap, ite_eq_right rejected] at represented
  cases reply with
  | some capacity => contradiction
  | none =>
    simp! only [AdapterRegistrationWriterRequestExtraction.encodeResponse, Lifted.len,
      core.slice.Slice.len, rust_primitives.slice.slice_length, Lifted.responseCapacity,
      Program.run_bind, Program.run_lift, simulateQ_bind, simulateQ_pure, pure_bind,
      bind_tc_ok, capacityRun, Lifted.branch, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      Lifted.fromResidual, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

theorem init_readback [RegistrationValidatorPrimitive.Operations] (view : registration.SignedInitView) :
    RegistrationNativePacketReadback.decodeInit (initVector view) = .ok (.Some (RegistrationNativeWire.initPacket view)) :=
  RegistrationNativePacketReadback.init_readback _ view rfl

theorem response_readback [RegistrationValidatorPrimitive.Operations] (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    RegistrationNativePacketReadback.decodeResponse (responseVector view admitted) = .ok (.Some (RegistrationNativeWire.responsePacket view)) :=
  RegistrationNativePacketReadback.response_readback _ view rfl admitted
end BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.array_length' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.array_length

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_capacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_capacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_rejected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.init_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback.response_readback
