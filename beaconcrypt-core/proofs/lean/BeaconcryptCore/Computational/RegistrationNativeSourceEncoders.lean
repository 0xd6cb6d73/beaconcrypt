-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes
import BeaconcryptCore.AdapterRegistrationWriterExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! These adapters bind the runtime writer leaves to the actual source-backed public serializers. They preserve all six native-view fields and the complete returned mutable output slice. Buffer allocation and reservation remain in the separately extracted runtime writer; decoding and readback are established separately. -/
namespace BeaconcryptCore.Computational.RegistrationNativeSourceEncoders
open beaconcrypt_core
open BeaconcryptCore.Refinement
open RegistrationSerializerReachableSource

@[instance_reducible] def sourceOperations (other : OtherBranches) : RegistrationWriterPrimitive.Operations where
  encodeInit := @beaconcrypt_parse.extraction_encode_init (RegistrationSerializerReachableSource.operations other)
  encodeResponse := @beaconcrypt_parse.extraction_encode_response (RegistrationSerializerReachableSource.operations other)

def initSyntax (view : registration.SignedInitView) : beaconcrypt_parse.transport.initkex where
  identity_key := view.fields.identity_key.to_slice
  pre_key := view.fields.pre_key.to_slice
  one_time_key := view.fields.one_time_key.to_slice
  pq_key := view.fields.pq_key.to_slice
  mldsa_public_key := view.fields.mldsa_public_key.to_slice
  signature := view.signature.to_slice

def responseSyntax (view : registration.SignedResponseView) : beaconcrypt_parse.transport.kexresponse where
  identity_key := view.identity_key.to_slice
  ephemeral_key := view.ephemeral_key.to_slice
  kem_cipher_text := view.kem_cipher_text.to_slice
  app_cipher_text := view.application_ciphertext
  key_id := view.key_id
  signature := view.signature.to_slice

def encodeInit (other : OtherBranches) (view : registration.SignedInitView) (output : Slice U8) : RustM (Usize × Slice U8) :=
  (sourceOperations other).encodeInit (initSyntax view) output

def encodeResponse (other : OtherBranches) (view : registration.SignedResponseView) (output : Slice U8) : RustM (Usize × Slice U8) :=
  (sourceOperations other).encodeResponse (responseSyntax view) output

theorem init_shape (view : registration.SignedInitView) :
    RegistrationSerializerInitBytes.InitShape (initSyntax view) := by
  simp only [RegistrationSerializerInitBytes.InitShape, initSyntax, Array.length_to_slice]
  repeat' constructor <;> scalar_tac

theorem response_shape (view : registration.SignedResponseView) :
    RegistrationSerializerResponseBytes.ResponseShape (responseSyntax view) := by
  simp only [RegistrationSerializerResponseBytes.ResponseShape, responseSyntax, Array.length_to_slice]
  repeat' constructor <;> scalar_tac

theorem init_fields (view : registration.SignedInitView) :
    (initSyntax view).identity_key.val = view.fields.identity_key.val ∧
      (initSyntax view).pre_key.val = view.fields.pre_key.val ∧
      (initSyntax view).one_time_key.val = view.fields.one_time_key.val ∧
      (initSyntax view).pq_key.val = view.fields.pq_key.val ∧
      (initSyntax view).mldsa_public_key.val = view.fields.mldsa_public_key.val ∧
      (initSyntax view).signature.val = view.signature.val := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem response_fields (view : registration.SignedResponseView) :
    (responseSyntax view).identity_key.val = view.identity_key.val ∧
      (responseSyntax view).ephemeral_key.val = view.ephemeral_key.val ∧
      (responseSyntax view).kem_cipher_text.val = view.kem_cipher_text.val ∧
      (responseSyntax view).app_cipher_text = view.application_ciphertext ∧
      (responseSyntax view).key_id = view.key_id ∧
      (responseSyntax view).signature.val = view.signature.val := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

attribute [local irreducible] beaconcrypt_parse.extraction_encode_init beaconcrypt_parse.extraction_encode_response

theorem init_bytes (other : OtherBranches) (view : registration.SignedInitView) (output : Slice U8)
    (room : 6757 ≤ output.length) :
    ∃ after, encodeInit other view output = .ok (6757#usize, after) ∧
      after.length = output.length ∧
      after.val = (136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)) ++ output.val.drop 6757 := by
  unfold encodeInit sourceOperations
  exact RegistrationSerializerInitBytes.public_bytes other (initSyntax view) output (init_shape view) room

theorem response_bytes (other : OtherBranches) (view : registration.SignedResponseView) (output : Slice U8)
    (room : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ output.length)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    ∃ after, encodeResponse other view output = .ok (RegistrationSerializerResponseBytes.finalCursor (responseSyntax view), after) ∧
      after.length = output.length ∧
      after.val = (136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view)) ++
        output.val.drop (RegistrationSerializerResponseBytes.totalLength (responseSyntax view)) ∧
      (RegistrationSerializerResponseBytes.finalCursor (responseSyntax view)).val =
        RegistrationSerializerResponseBytes.totalLength (responseSyntax view) := by
  unfold encodeResponse sourceOperations
  exact RegistrationSerializerResponseBytes.public_bytes other (responseSyntax view) output (response_shape view) room admitted

theorem response_rejected (other : OtherBranches) (view : registration.SignedResponseView) (output : Slice U8)
    (outside : CborSizing.maxMessageSize < RegistrationSerializerResponseBytes.totalLength (responseSyntax view)) :
    encodeResponse other view output = .ok (0#usize, output) := by
  unfold encodeResponse sourceOperations
  exact RegistrationSerializerResponseBytes.public_rejected other (responseSyntax view) output (response_shape view) outside

theorem runtime_init_function (other : OtherBranches) :
    @beaconcrypt_parse.encode_init (sourceOperations other) =
      @beaconcrypt_parse.extraction_encode_init (RegistrationSerializerReachableSource.operations other) := rfl

theorem runtime_init_binding (other : OtherBranches) (input : beaconcrypt_parse.transport.initkex) (output : Slice U8) :
    @beaconcrypt_parse.encode_init (sourceOperations other) input output =
      @beaconcrypt_parse.extraction_encode_init (RegistrationSerializerReachableSource.operations other) input output := by
  exact congrFun (congrFun (runtime_init_function other) input) output

theorem runtime_response_function (other : OtherBranches) :
    @beaconcrypt_parse.encode_response (sourceOperations other) =
      @beaconcrypt_parse.extraction_encode_response (RegistrationSerializerReachableSource.operations other) := rfl

theorem runtime_response_binding (other : OtherBranches) (input : beaconcrypt_parse.transport.kexresponse) (output : Slice U8) :
    @beaconcrypt_parse.encode_response (sourceOperations other) input output =
      @beaconcrypt_parse.extraction_encode_response (RegistrationSerializerReachableSource.operations other) input output := by
  exact congrFun (congrFun (runtime_response_function other) input) output

end BeaconcryptCore.Computational.RegistrationNativeSourceEncoders

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.init_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.response_rejected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_init_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_init_function

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_init_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_init_binding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_response_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_response_function

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_response_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.runtime_response_binding
