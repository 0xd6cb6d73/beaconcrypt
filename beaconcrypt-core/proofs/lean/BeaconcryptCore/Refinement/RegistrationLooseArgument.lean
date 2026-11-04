-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightByteWords
import BeaconcryptCore.Refinement.RegistrationPreflightTotal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseArgument
open beaconcrypt_parse RegistrationHeaderBits RegistrationPreflightArgument RegistrationPreflightWordValues

inductive Form where
  | short (value : U8) (bound : value.val < 24)
  | byte (value : U8)
  | word16 (value : U16)
  | word32 (value : U32)
  | word64 (value : U64)

def value : Form → U64
  | .short n _ | .byte n => UScalar.cast .U64 n
  | .word16 n => UScalar.cast .U64 n
  | .word32 n => UScalar.cast .U64 n
  | .word64 n => n

def additional : Form → U8
  | .short n _ => n
  | .byte _ => 24#u8
  | .word16 _ => 25#u8
  | .word32 _ => 26#u8
  | .word64 _ => 27#u8

def wordBytes : Form → List U8
  | .short _ _ => []
  | .byte n => [n]
  | .word16 n => (Aeneas.Std.core.num.U16.to_be_bytes n).val
  | .word32 n => (Aeneas.Std.core.num.U32.to_be_bytes n).val
  | .word64 n => (FrameCodecWord.word n).val

def bytes (major : U8) (form : Form) : List U8 := packed major (additional form) :: wordBytes form

set_option backward.isDefEq.respectTransparency false in
theorem parse_form (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest) (majorBound : major.val < 8) :
    ∃ tail, tail.val = rest ∧ primitive_argument input major = .ok (.Some (value form, tail)) := by
  obtain ⟨start, startBytes, source⟩ := prefix_step input major (additional form) (wordBytes form ++ rest)
    contents majorBound (by cases form <;> simp only [additional] <;> scalar_tac)
  cases form with
  | short n bound =>
    refine ⟨start, startBytes, ?_⟩
    rw [source]
    have short : n ≤ 23#u8 := by scalar_tac
    simp only [additional, afterHeader, short, ↓reduceIte, value]
  | byte n =>
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 1#usize (UScalar.cast .U64 n) [n] rest
      startBytes (by rfl) (fun front bytes => argument_byte front n bytes)
    exact ⟨tail, tailBytes, by rw [source, additional, after_byte, decoded]; rfl⟩
  | word16 n =>
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 2#usize (UScalar.cast .U64 n)
      (wordBytes (.word16 n)) rest startBytes (by rw [wordBytes, RegistrationPreflightByteWords.word16_bytes]; rfl)
      (fun front bytes => argument_word16 front n (by rw [wordBytes, RegistrationPreflightByteWords.word16_bytes] at bytes; exact bytes))
    exact ⟨tail, tailBytes, by rw [source, additional, after_word16, decoded]; rfl⟩
  | word32 n =>
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 4#usize (UScalar.cast .U64 n)
      (wordBytes (.word32 n)) rest startBytes (by rw [wordBytes, RegistrationPreflightByteWords.word32_bytes]; rfl)
      (fun front bytes => argument_word32 front n (by rw [wordBytes, RegistrationPreflightByteWords.word32_bytes] at bytes; exact bytes))
    exact ⟨tail, tailBytes, by rw [source, additional, after_word32, decoded]; rfl⟩
  | word64 n =>
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 8#usize n
      (wordBytes (.word64 n)) rest startBytes (by rfl)
      (fun front bytes => argument_word64 front n bytes)
    exact ⟨tail, tailBytes, by rw [source, additional, after_word64, decoded]; rfl⟩

def used : Form → Usize
  | .short _ _ => 1#usize
  | .byte _ => 2#usize
  | .word16 _ => 3#usize
  | .word32 _ => 5#usize
  | .word64 _ => 9#usize

def sourceHeader (major : U8) (form : Form) : cbordetveraux.header :=
  ⟨⟨major, additional form⟩, match form with
    | .short _ _ => .LongArgumentOther
    | .byte n => .LongArgumentU8 n
    | .word16 n => .LongArgumentU16 n
    | .word32 n => .LongArgumentU32 n
    | .word64 n => .LongArgumentU64 n⟩

theorem used_length (major : U8) (form : Form) : (used form).val = (bytes major form).length := by
  cases form <;> simp only [used, bytes, wordBytes, RegistrationPreflightByteWords.word16_bytes,
    RegistrationPreflightByteWords.word32_bytes, FrameCodecWord.word, List.length_cons, List.length_nil]
  all_goals rfl

theorem header_major (major : U8) (form : Form) :
    (sourceHeader major form).fst.major_type = major := rfl

theorem argument_value (major : U8) (form : Form) :
    cbordetveraux.argument_as_uint64 (sourceHeader major form).fst (sourceHeader major form).snd = .ok (value form) := by
  cases form <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_form (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest) (majorBound : major.val < 8)
    (notSimple : major ≠ cbordetveraux.cbor_major_type_simple_value) :
    cbordetveraux.read_header input = .ok (sourceHeader major form) := by
  cases form with
  | short n bound => exact RegistrationHeaderReadback.read_short input major n rest contents majorBound bound
  | byte n => exact RegistrationHeaderReadback.read_byte_argument input major n rest contents majorBound notSimple
  | word16 n =>
    exact RegistrationHeaderNarrowReadback.read_u16 input major n rest
      (by simpa only [bytes, additional, wordBytes, RegistrationPreflightByteWords.word16_bytes, List.cons_append, List.nil_append] using contents) majorBound
  | word32 n =>
    exact RegistrationHeaderNarrowReadback.read_u32 input major n rest
      (by simpa only [bytes, additional, wordBytes, RegistrationPreflightByteWords.word32_bytes, List.cons_append, List.nil_append] using contents) majorBound
  | word64 n => exact RegistrationHeaderLongReadback.read_u64 input major n rest contents majorBound

theorem additional_bound (form : Form) : (additional form).val < 28 := by
  cases form <;> simp only [additional] <;> scalar_tac

set_option backward.isDefEq.respectTransparency false in
theorem count_form (form : Form) : RegistrationHeaderJump.count (additional form) = used form := by
  cases form with
  | short n bound => simp only [additional, used, RegistrationHeaderJump.count]; split_ifs <;> scalar_tac
  | byte n => rfl
  | word16 n => rfl
  | word32 n => rfl
  | word64 n => rfl



set_option backward.isDefEq.respectTransparency false in
theorem jump_form (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest) (majorBound : major.val < 8) :
    cbordetveraux.jump_header input 0#usize = .ok (used form) := by
  have source := RegistrationHeaderJump.jump_prefix input major (additional form) (wordBytes form ++ rest)
    contents majorBound (by have := additional_bound form; omega)
  simpa only [count_form] using source

set_option backward.isDefEq.respectTransparency false in
theorem word_image (information : U8) (data : List U8)
    (long : information = 24#u8 ∨ information = 25#u8 ∨ information = 26#u8 ∨ information = 27#u8)
    (length : data.length + 1 = (RegistrationHeaderJump.count information).val) :
    ∃ form : Form, additional form = information ∧ wordBytes form = data := by
  rcases long with same | same | same | same <;> subst information
  · have one : data.length = 1 := by change data.length + 1 = 2 at length; omega
    cases data with
    | nil => contradiction
    | cons byte tail =>
      have empty : tail = [] := by
        have zero : tail.length = 0 := by simp only [List.length_cons] at one; omega
        simpa using zero
      subst tail
      exact ⟨.byte byte, rfl, rfl⟩
  · have two : data.length = (2#usize).val := by change data.length = 2; change data.length + 1 = 3 at length; omega
    let input : Array U8 2#usize := ⟨data, two⟩
    let n := Aeneas.Std.core.num.U16.from_be_bytes input
    exact ⟨.word16 n, rfl, congrArg Subtype.val (RegistrationPreflightByteWords.to_from_word16 input)⟩
  · have four : data.length = (4#usize).val := by change data.length = 4; change data.length + 1 = 5 at length; omega
    let input : Array U8 4#usize := ⟨data, four⟩
    let n := Aeneas.Std.core.num.U32.from_be_bytes input
    exact ⟨.word32 n, rfl, congrArg Subtype.val (RegistrationPreflightByteWords.to_from_word32 input)⟩
  · have eight : data.length = (8#usize).val := by change data.length = 8; change data.length + 1 = 9 at length; omega
    let input : Array U8 8#usize := ⟨data, eight⟩
    let n := Aeneas.Std.core.num.U64.from_be_bytes input
    have rendered : Aeneas.Std.core.num.U64.to_be_bytes n = FrameCodecWord.word n :=
      RustM.ok.inj (FrameCodecWord.word_exact n)
    have inverse := RegistrationPreflightByteWords.to_from_word input
    exact ⟨.word64 n, rfl, congrArg Subtype.val (rendered.symm.trans inverse)⟩

def Span (input : Slice U8) (major : U8) (parsed : U64) (tail : Slice U8) : Prop :=
  ∃ form : Form, value form = parsed ∧ input.val = bytes major form ++ tail.val

set_option backward.isDefEq.respectTransparency false in
theorem span_of_form (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest) (majorBound : major.val < 8)
    (parsed : U64) (tail : Slice U8) (accepted : primitive_argument input major = .ok (.Some (parsed, tail))) :
    Span input major parsed tail := by
  obtain ⟨actualTail, tailBytes, decoded⟩ := parse_form input major form rest contents majorBound
  have pair := _root_.Option.some.inj (RustM.ok.inj (decoded.symm.trans accepted))
  have values := Prod.mk.inj pair
  refine ⟨form, values.1, ?_⟩
  rw [← values.2, tailBytes]
  exact contents


set_option backward.isDefEq.respectTransparency false in
theorem span_long (input : Slice U8) (major information : U8) (start : Slice U8) (width : Usize)
    (long : information = 24#u8 ∨ information = 25#u8 ∨ information = 26#u8 ∨ information = 27#u8)
    (widthValue : width.val + 1 = (RegistrationHeaderJump.count information).val)
    (contents : input.val = packed major information :: start.val)
    (source : primitive_argument input major = extraction_argument_long start width)
    (majorBound : major.val < 8) (parsed : U64) (tail : Slice U8)
    (accepted : primitive_argument input major = .ok (.Some (parsed, tail))) :
    Span input major parsed tail := by
  by_cases truncated : start.length < width.val
  · rw [source, long_rejected start width truncated] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible
  · have room : width.val ≤ start.val.length := by change ¬start.val.length < width.val at truncated; omega
    obtain ⟨form, informationSame, formBytes⟩ := word_image information (start.val.take width.val) long
      (by rw [List.length_take, Nat.min_eq_left room]; exact widthValue)
    have formContents : input.val = bytes major form ++ start.val.drop width.val := by
      rw [bytes, informationSame, formBytes, List.cons_append, List.take_append_drop]
      exact contents
    exact span_of_form input major form (start.val.drop width.val) formContents majorBound parsed tail accepted

set_option backward.isDefEq.respectTransparency false in
theorem argument_span (input : Slice U8) (declared : U8) (parsed : U64) (tail : Slice U8)
    (accepted : primitive_argument input declared = .ok (.Some (parsed, tail))) :
    Span input declared parsed tail := by
  cases contents : input.val with
  | nil =>
    rw [RegistrationPreflightArgument.empty input declared contents] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible
  | cons byte rest =>
    have sourceBytes : input.val = packed (RegistrationPreflightTotal.major byte) (RegistrationPreflightTotal.additional byte) :: rest := by
      rw [RegistrationPreflightTotal.unpack]
      exact contents
    by_cases same : RegistrationPreflightTotal.major byte = declared
    · subst declared
      obtain ⟨start, startBytes, source⟩ := prefix_step input (RegistrationPreflightTotal.major byte)
        (RegistrationPreflightTotal.additional byte) rest sourceBytes
        (RegistrationPreflightTotal.major_bound byte) (RegistrationPreflightTotal.additional_bound byte)
      have sourceContents : input.val = packed (RegistrationPreflightTotal.major byte) (RegistrationPreflightTotal.additional byte) :: start.val := by
        rw [startBytes]
        exact sourceBytes
      by_cases short : (RegistrationPreflightTotal.additional byte).val < 24
      · exact span_of_form input (RegistrationPreflightTotal.major byte) (.short (RegistrationPreflightTotal.additional byte) short)
          rest sourceBytes (RegistrationPreflightTotal.major_bound byte) parsed tail accepted
      · have options : RegistrationPreflightTotal.additional byte = 24#u8 ∨ RegistrationPreflightTotal.additional byte = 25#u8 ∨
            RegistrationPreflightTotal.additional byte = 26#u8 ∨ RegistrationPreflightTotal.additional byte = 27#u8 ∨
            28 ≤ (RegistrationPreflightTotal.additional byte).val := by
          have bound := RegistrationPreflightTotal.additional_bound byte
          scalar_tac
        rcases options with isByte | isWord16 | isWord32 | isWord64 | reserved
        · apply span_long input _ 24#u8 start 1#usize (Or.inl rfl) (by rfl)
            (by rw [← isByte]; exact sourceContents) ?_ (RegistrationPreflightTotal.major_bound byte) parsed tail accepted
          rw [source, isByte, after_byte]
        · apply span_long input _ 25#u8 start 2#usize (Or.inr (Or.inl rfl)) (by rfl)
            (by rw [← isWord16]; exact sourceContents) ?_ (RegistrationPreflightTotal.major_bound byte) parsed tail accepted
          rw [source, isWord16, after_word16]
        · apply span_long input _ 26#u8 start 4#usize (Or.inr (Or.inr (Or.inl rfl))) (by rfl)
            (by rw [← isWord32]; exact sourceContents) ?_ (RegistrationPreflightTotal.major_bound byte) parsed tail accepted
          rw [source, isWord32, after_word32]
        · apply span_long input _ 27#u8 start 8#usize (Or.inr (Or.inr (Or.inr rfl))) (by rfl)
            (by rw [← isWord64]; exact sourceContents) ?_ (RegistrationPreflightTotal.major_bound byte) parsed tail accepted
          rw [source, isWord64, after_word64]
        · rw [source, after_reserved _ start reserved (RegistrationPreflightTotal.additional_bound byte)] at accepted
          have impossible := RustM.ok.inj accepted
          cases impossible
    · rw [RegistrationPreflightArgument.mismatch input (RegistrationPreflightTotal.major byte) declared
        (RegistrationPreflightTotal.additional byte) rest sourceBytes (RegistrationPreflightTotal.major_bound byte) same] at accepted
      have impossible := RustM.ok.inj accepted
      cases impossible

end BeaconcryptCore.Refinement.RegistrationLooseArgument

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.parse_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.parse_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.used_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.used_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.header_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.header_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.argument_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.argument_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.read_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.read_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.additional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.additional_bound

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.count_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.count_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.jump_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.jump_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.word_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.word_image

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.span_of_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.span_of_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.span_long' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.span_long

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseArgument.argument_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseArgument.argument_span
