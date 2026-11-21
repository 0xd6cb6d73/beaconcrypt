-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaAtoms
import BeaconcryptCore.Refinement.RegistrationSchemaTransitions
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Six byte-derived source iterator transitions drive the unchanged original Init schema validator and parser, including their complete repeated checks, truncated rereads, length bounds and mutable singleton updates. The final source parse reconstructs all four remaining input fields exactly. Composing actual raw/canonical validation yields original validate_and_parse_initkex with an empty remainder; public preflight is separate. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaInitStages
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationCanonicalTrace RegistrationSchemaAtoms
open RegistrationSchemaIteratorReadback RegistrationSchemaViews RegistrationSchemaTransitions RegistrationCodecArraySingleton

structure Stages (value : transport.initkex) (payload : Slice U8) where
  size0 : U8
  first : Transition payload (uint size0 3#u64)
  size1 : U8
  second : Transition first.tail (uint size1 0#u64)
  size2 : U8
  identity : Transition second.tail (bytes size2 value.identity_key)
  size3 : U8
  pre : Transition identity.tail (bytes size3 value.pre_key)
  size4 : U8
  oneTime : Transition pre.tail (bytes size4 value.one_time_key)
  size5 : U8
  pq : Transition oneTime.tail (bytes size5 value.pq_key)
  consumed : pq.tail.val = []

set_option backward.isDefEq.respectTransparency false in
theorem stages (value : transport.initkex) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerInitBytes.payload value) :
    Nonempty (Stages value payload) := by
  have whole : payload.val = atomsBytes (initAtoms value) := by rw [init_bytes]; exact contents
  obtain ⟨size0, first, firstBytes⟩ := uint_transition payload 3#u64
    (atomsBytes [ .uint 0#u64, .bytes value.identity_key, .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key ]) (by simpa only [initAtoms, atomsBytes, atomBytes] using whole)
  obtain ⟨size1, second, secondBytes⟩ := uint_transition first.tail 0#u64
    (atomsBytes [ .bytes value.identity_key, .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key ]) (by simpa only [initAtoms, atomsBytes, atomBytes] using firstBytes)
  obtain ⟨size2, identity, identityBytes⟩ := bytes_transition second.tail value.identity_key
    (atomsBytes [ .bytes value.pre_key, .bytes value.one_time_key, .bytes value.pq_key ]) (by simpa only [initAtoms, atomsBytes, atomBytes] using secondBytes)
  obtain ⟨size3, pre, preBytes⟩ := bytes_transition identity.tail value.pre_key
    (atomsBytes [ .bytes value.one_time_key, .bytes value.pq_key ]) (by simpa only [initAtoms, atomsBytes, atomBytes] using identityBytes)
  obtain ⟨size4, oneTime, oneTimeBytes⟩ := bytes_transition pre.tail value.one_time_key
    (atomsBytes [ .bytes value.pq_key ]) (by simpa only [initAtoms, atomsBytes, atomBytes] using preBytes)
  obtain ⟨size5, pq, pqBytes⟩ := bytes_transition oneTime.tail value.pq_key
    (atomsBytes []) (by simpa only [initAtoms, atomsBytes, atomBytes] using oneTimeBytes)
  exact ⟨{
    size0 := size0
    first := first
    size1 := size1
    second := second
    size2 := size2
    identity := identity
    size3 := size3
    pre := pre
    size4 := size4
    oneTime := oneTime
    size5 := size5
    pq := pq
    consumed := pqBytes }⟩

theorem index_mut_pack {A : Type} (value : A) :
    Array.index_mut_usize (pack value) 0#usize = .ok (value, pack) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem validate (value : transport.initkex) (payload : Slice U8) (work : Stages value payload)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    transport.validate_initkex (RegistrationArrayReadback.array6 payload) = .ok true := by
  rcases shape with ⟨identityLength, preLength, oneTimeLength, pqLength⟩
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  simp [transport.validate_initkex.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.bcSchemaRepeatedClosure2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_1.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex.closure_2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_initkex,
    RegistrationArrayReadback.array6,
    array_major6,
    array_view6,
    array_start6,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    index_mut_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.pre.source,
    work.oneTime.source,
    work.pq.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    identityLength,
    preLength,
    oneTimeLength,
    pqLength,
    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,
    bind_tc_ok,
    uncurry,
    cbor_major_type_uint64,
    cbor_major_type_byte_string,
    cbor_major_type_array]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem parse (value : transport.initkex) (payload : Slice U8) (work : Stages value payload)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    transport.parse_initkex (RegistrationArrayReadback.array6 payload) = .ok value := by
  rcases shape with ⟨identityLength, preLength, oneTimeLength, pqLength⟩
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  have gap2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap3 : U64.wrapping_sub 3#u64 2#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap4 : U64.wrapping_sub 4#u64 3#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap5 : U64.wrapping_sub 5#u64 4#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap6 : U64.wrapping_sub 6#u64 5#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap7 : U64.wrapping_sub 7#u64 6#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap8 : U64.wrapping_sub 8#u64 7#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  simp [transport.initkex_right,
    transport.extraction_parse_initkex_check_4,
    transport.extraction_parse_initkex_check_3,
    transport.extraction_parse_initkex_check_2,
    transport.extraction_parse_initkex_check_1,
    transport.extraction_parse_initkex_check_0,
    transport.parse_initkex,
    RegistrationArrayReadback.array6,
    array_view6,
    array_start6,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    index_mut_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    RegistrationSchemaIteratorReadback.length,
    RegistrationSchemaIteratorReadback.truncate,
    sub_u64,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.pre.source,
    work.oneTime.source,
    work.pq.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    identityLength,
    preLength,
    oneTimeLength,

    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,







    bind_tc_ok,
    uncurry,
    lowstar.ignore.bcSchemaRepeatedIgnore2,
    cbor_major_type_uint64,
    cbor_major_type_byte_string,
    ]

theorem validate_source (value : transport.initkex) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerInitBytes.payload value)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    transport.validate_initkex (RegistrationArrayReadback.array6 payload) = .ok true := by
  obtain ⟨work⟩ := stages value payload contents
  exact validate value payload work shape

theorem parse_source (value : transport.initkex) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerInitBytes.payload value)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    transport.parse_initkex (RegistrationArrayReadback.array6 payload) = .ok value := by
  obtain ⟨work⟩ := stages value payload contents
  exact parse value payload work shape

set_option backward.isDefEq.respectTransparency false in
theorem validated [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    transport.validate_and_parse_initkex input = .ok (.Some (value, RegistrationFlatSkip.empty)) := by
  obtain ⟨payload, payloadBytes, source⟩ := init_parsed input value contents
  simp only [transport.validate_and_parse_initkex, source, bind_tc_ok, uncurry,
    validate_source value payload payloadBytes shape, ↓reduceIte,
    parse_source value payload payloadBytes shape]

end BeaconcryptCore.Refinement.RegistrationSchemaInitStages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.stages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.index_mut_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.index_mut_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validate

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validate_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.parse_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.parse_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaInitStages.validated
