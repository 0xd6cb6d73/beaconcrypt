-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaInitStages
import BeaconcryptCore.Refinement.RegistrationSchemaResponseStages
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal
open beaconcrypt_parse cbordetveraux RegistrationSchemaIteratorReadback RegistrationSchemaViews RegistrationCodecArraySingleton
local instance (value : transport.initkex) : Decidable (RegistrationSerializerInitBytes.InitShape value) := by
  unfold RegistrationSerializerInitBytes.InitShape
  infer_instance
local instance (value : transport.kexresponse) : Decidable (RegistrationSerializerResponseBytes.ResponseShape value) := by
  unfold RegistrationSerializerResponseBytes.ResponseShape
  infer_instance

private theorem interval (expected actual : Nat) (next : RustM Bool) :
    (if expected ≤ actual then if actual ≤ expected then next else .ok false else .ok false) =
      (if actual = expected then next else .ok false) := by
  split_ifs <;> first | rfl | omega

private theorem decide_result (condition : Prop) [Decidable condition] :
    (if condition then (RustM.ok true) else .ok false) = .ok (decide condition) := by
  by_cases holds : condition <;> simp only [holds, ↓reduceIte, decide_true, decide_false]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem init (value : transport.initkex) (payload : Slice U8) (work : RegistrationSchemaInitStages.Stages value payload) :
    transport.validate_initkex (RegistrationArrayReadback.array8 payload) = .ok (decide (RegistrationSerializerInitBytes.InitShape value)) := by
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  have dec7 : U64.wrapping_sub 7#u64 1#u64 = 6#u64 := sub_small 6 (by decide)
  have dec8 : U64.wrapping_sub 8#u64 1#u64 = 7#u64 := sub_small 7 (by decide)
  simp [transport.validate_initkex.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.bcSchemaRepeatedClosure5.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex,
    RegistrationArrayReadback.array8,
    array_major,
    array_view,
    array_start,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    RegistrationSchemaInitStages.index_mut_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.pre.source,
    work.oneTime.source,
    work.pq.source,
    work.mldsa.source,
    work.signature.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,
    dec7,
    dec8,
    bind_tc_ok,
    uncurry,
    cbor_major_type_uint64,
    cbor_major_type_byte_string,
    cbor_major_type_array]

  simp only [interval]
  simp only [← ite_and]
  rw [decide_result]
  simp only [RegistrationSerializerInitBytes.InitShape, Slice.length]
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem response (value : transport.kexresponse) (payload : Slice U8) (work : RegistrationSchemaResponseStages.Stages value payload) :
    transport.validate_kexresponse (RegistrationArrayReadback.array8 payload) = .ok (decide (RegistrationSerializerResponseBytes.ResponseShape value)) := by
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  have dec7 : U64.wrapping_sub 7#u64 1#u64 = 6#u64 := sub_small 6 (by decide)
  have dec8 : U64.wrapping_sub 8#u64 1#u64 = 7#u64 := sub_small 7 (by decide)
  simp [transport.validate_kexresponse.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.bcSchemaRepeatedClosure5.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse,
    RegistrationArrayReadback.array8,
    array_major,
    array_view,
    array_start,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    RegistrationSchemaResponseStages.index_mut_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.ephemeral.source,
    work.kem.source,
    work.application.source,
    work.key.source,
    work.signature.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    uint_validate,
    bytes_validate,


    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,
    dec7,
    dec8,
    bind_tc_ok,
    uncurry,
    cbor_major_type_uint64,
    cbor_major_type_byte_string,
    cbor_major_type_array]

  simp only [interval]
  simp only [← ite_and]
  rw [decide_result]
  simp only [RegistrationSerializerResponseBytes.ResponseShape, Slice.length]
end BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal.response
