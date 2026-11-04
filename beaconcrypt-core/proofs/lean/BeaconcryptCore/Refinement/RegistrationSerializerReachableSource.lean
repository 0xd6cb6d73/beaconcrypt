-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationSerializerControllerExtraction.Funs
import BeaconcryptCore.RegistrationArrayExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationShallowDispatch
import BeaconcryptCore.Refinement.RegistrationShallowSize
import BeaconcryptCore.Refinement.RegistrationShallowUInt
import BeaconcryptCore.Refinement.RegistrationShallowString
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! A source interpretation for the extracted encoder controller operations. Actual Int/String factories, extracted shallow bodies and array entry are installed as code, with complete mutable poststates. Every remaining unsupported branch is an explicit arbitrary complete effect. Pointwise constructor and factory compositions are proved; whole-controller branch coverage, array bytes, public parse/readback and native instantiation remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationSerializerReachableSource
open beaconcrypt_parse cbordetveraux RegistrationShallowDispatch
abbrev RawOption := cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177

/-- Interpretations of source branches outside the registration field constructors.
No law or desired output is required of these complete effects. -/
structure OtherBranches where
  deepSerialize : Serialize
  otherSerialize : Serialize
  deepSize : Size
  otherSize : Size
  textFactory : Slice U8 → RustM RawOption
  utf8Correct : Slice U8 → RustM Bool

/-- The controller uses these actual source leaves for Int/String fields and the
actual extracted array entry. Full-message branch coverage, rotation and parser
composition are separate; this is not a native codec instance. -/
@[instance_reducible] def operations (other : OtherBranches) : RegistrationSerializerPrimitive.Operations where
  mkString kind input := match kind with
    | .ByteString => extraction_mk_byte_string input
    | .TextString => other.textFactory input
  sizeRaw := sourceSize other.deepSize other.otherSize
  serializeRaw := sourceSerialize other.deepSerialize other.otherSerialize
  serializeArray := extraction_array_entry
  utf8Correct := other.utf8Correct

theorem byte_factory (other : OtherBranches) (input : Slice U8) :
    (operations other).mkString .ByteString input = extraction_mk_byte_string input := rfl

theorem int_size (other : OtherBranches) (value : cbor_int) (out : Slice Usize) :
    (operations other).sizeRaw (.CBOR_Case_Int value) out =
      extraction_size_shallow_int value out := rfl

theorem string_size (other : OtherBranches) (value : cbor_string) (out : Slice Usize) :
    (operations other).sizeRaw (.CBOR_Case_String value) out =
      extraction_size_shallow_string value out := rfl

theorem int_serialize (other : OtherBranches) (value : cbor_int) (out : Slice U8) (offset : Usize) :
    (operations other).serializeRaw (.CBOR_Case_Int value) out offset =
      extraction_serialize_shallow_int value out offset := rfl

theorem string_serialize (other : OtherBranches) (value : cbor_string) (out : Slice U8) (offset : Usize) :
    (operations other).serializeRaw (.CBOR_Case_String value) out offset =
      extraction_serialize_shallow_string value out offset := rfl

theorem array_source (other : OtherBranches) (count : U64) (out : Slice U8) (offset : Usize) :
    (operations other).serializeArray count out offset = extraction_array_entry count out offset := rfl

/-- Actual factory-to-operation compositions; no raw-value validity premise is supplied. -/
def sizeUInt (other : OtherBranches) (capacity : Usize) (value : U64) : RustM (Bool × Slice Usize) := do
  let raw ← cbordetver.cbor_det_mk_int64 .UInt64 value
  (operations other).sizeRaw raw (RegistrationHeaderSize.cell capacity)

def serializeUInt (other : OtherBranches) (out : Slice U8) (value : U64) : RustM (Usize × Slice U8) := do
  let raw ← cbordetver.cbor_det_mk_int64 .UInt64 value
  (operations other).serializeRaw raw out 0#usize

def sizeBytes (other : OtherBranches) (capacity : Usize) (input : Slice U8) : RustM (Bool × Slice Usize) := do
  let value ← (operations other).mkString .ByteString input
  match value with
  | .Some raw => (operations other).sizeRaw raw (RegistrationHeaderSize.cell capacity)
  | .None => .fail .panic

def serializeBytes (other : OtherBranches) (out input : Slice U8) : RustM (Usize × Slice U8) := do
  let value ← (operations other).mkString .ByteString input
  match value with
  | .Some raw => (operations other).serializeRaw raw out 0#usize
  | .None => .fail .panic

theorem uint_size_source (other : OtherBranches) (capacity : Usize) (value : U64) :
    sizeUInt other capacity value = RegistrationShallowSize.sourceInt capacity value := by
  obtain ⟨size, factory⟩ := RegistrationConstructorGuards.mk_uint value
  unfold sizeUInt RegistrationShallowSize.sourceInt
  rw [factory]
  rfl

theorem uint_serialize_source (other : OtherBranches) (out : Slice U8) (value : U64) :
    serializeUInt other out value = RegistrationShallowUInt.sourceSerialize out value := by
  obtain ⟨size, factory⟩ := RegistrationConstructorGuards.mk_uint value
  unfold serializeUInt RegistrationShallowUInt.sourceSerialize
  rw [factory]
  rfl

theorem bytes_size_source (other : OtherBranches) (capacity : Usize) (input : Slice U8) :
    sizeBytes other capacity input = RegistrationShallowSize.sourceString capacity input := by
  obtain ⟨size, factory, _⟩ := RegistrationStringFactory.factory_exists input
  unfold sizeBytes RegistrationShallowSize.sourceString
  rw [byte_factory, factory]
  rfl

theorem bytes_serialize_source (other : OtherBranches) (out input : Slice U8) :
    serializeBytes other out input = RegistrationShallowString.sourceSerialize out input := by
  obtain ⟨size, factory, _⟩ := RegistrationStringFactory.factory_exists input
  unfold serializeBytes RegistrationShallowString.sourceSerialize
  rw [byte_factory, factory]
  rfl

end BeaconcryptCore.Refinement.RegistrationSerializerReachableSource

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.byte_factory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.byte_factory

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.int_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.int_size

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.string_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.string_size

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.int_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.int_serialize

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.string_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.string_serialize

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.array_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.array_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.uint_size_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.uint_size_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.uint_serialize_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.uint_serialize_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.bytes_size_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.bytes_size_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.bytes_serialize_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.bytes_serialize_source
