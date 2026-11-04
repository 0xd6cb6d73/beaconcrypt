-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseArgument
import BeaconcryptCore.Refinement.RegistrationPreflightCoverage
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseFieldSpan
open beaconcrypt_parse RegistrationLooseArgument

inductive Atom where
  | uint (form : Form)
  | bytes (form : Form) (payload : Slice U8) (size : value form = UScalar.cast .U64 payload.len)

def major : Atom → U8
  | .uint _ => 0#u8
  | .bytes _ _ _ => 2#u8

def atomBytes : Atom → List U8
  | .uint form => bytes 0#u8 form
  | .bytes form payload _ => bytes 2#u8 form ++ payload.val

set_option backward.isDefEq.respectTransparency false in
theorem try_usize_value (parsed : U64) (count : Usize)
    (accepted : core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from parsed = .ok (.Ok count)) :
    count.val = parsed.val := by
  simp only [core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, lift, bind_tc_ok] at accepted
  split_ifs at accepted with upper lower
  · have impossible := RustM.ok.inj accepted
    cases impossible
  · have impossible := RustM.ok.inj accepted
    cases impossible
  · have equal : UScalar.cast .Usize parsed = count := by
      injection (RustM.ok.inj accepted)
    rw [← equal]
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    simp only [UScalar.lt_equiv, RegistrationSerializerFields.usize_cast] at upper
    simp only [core.num.Usize.MAX, UScalar.ofNatCore_val_eq] at upper
    change parsed.val < 2 ^ System.Platform.numBits
    simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq] at upper
    have positive : 0 < 2 ^ System.Platform.numBits := Nat.pow_pos (by decide)
    omega

set_option backward.isDefEq.respectTransparency false in
theorem suffix_some (input : Slice U8) (count : Usize) (tail : Slice U8)
    (accepted : core.slice.Slice.get (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      input { start := count } = .ok (.Some tail)) :
    count.val ≤ input.length ∧ tail = input.drop count := by
  by_cases bound : count.val ≤ input.length
  · have expected := RegistrationPreflightFields.get_suffix input count bound
    have same := _root_.Option.some.inj (RustM.ok.inj (accepted.symm.trans expected))
    exact ⟨bound, same⟩
  · have outside : ¬ count ≤ input.len := by simpa only [UScalar.le_equiv, Slice.len_val] using bound
    simp only [core.slice.Slice.get, core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
      rust_primitives.slice.slice_length, bind_tc_ok, outside, ↓reduceIte] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible

set_option backward.isDefEq.respectTransparency false in
theorem uint_span (input tail : Slice U8)
    (accepted : extraction_preflight_field input 0#u8 = .ok (.Some tail)) :
    ∃ atom : Atom, major atom = 0#u8 ∧ input.val = atomBytes atom ++ tail.val := by
  obtain ⟨argument, run⟩ := RegistrationPreflightTotal.argument_total input 0#u8
  cases argument with
  | none =>
    simp only [extraction_preflight_field, run, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible
  | some pair =>
    rcases pair with ⟨parsed, rest⟩
    have notString : (0#u8 : U8) ≠ 2#u8 := by decide
    simp only [extraction_preflight_field, run, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      uncurry, notString, ↓reduceIte] at accepted
    have same := _root_.Option.some.inj (RustM.ok.inj accepted)
    obtain ⟨form, _, contents⟩ := argument_span input 0#u8 parsed rest run
    exact ⟨.uint form, rfl, by simpa only [atomBytes, ← same] using contents⟩

set_option backward.isDefEq.respectTransparency false in
theorem bytes_span (input tail : Slice U8)
    (accepted : extraction_preflight_field input 2#u8 = .ok (.Some tail)) :
    ∃ atom : Atom, major atom = 2#u8 ∧ input.val = atomBytes atom ++ tail.val := by
  obtain ⟨argument, run⟩ := RegistrationPreflightTotal.argument_total input 2#u8
  cases argument with
  | none =>
    simp only [extraction_preflight_field, run, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible
  | some pair =>
    rcases pair with ⟨parsed, rest⟩
    obtain ⟨converted, convertRun⟩ := RegistrationPreflightTotal.try_usize_total parsed
    cases converted with
    | Err error =>
      simp only [extraction_preflight_field, run, bind_tc_ok,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        uncurry, ↓reduceIte, convertRun, core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
      have impossible := RustM.ok.inj accepted
      cases impossible
    | Ok count =>
      obtain ⟨suffix, suffixRun⟩ := RegistrationPreflightTotal.suffix_total rest count
      cases suffix with
      | none =>
        simp only [extraction_preflight_field, run, bind_tc_ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          uncurry, ↓reduceIte, convertRun, core.result.Result.ok, suffixRun,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
        have impossible := RustM.ok.inj accepted
        cases impossible
      | some actualTail =>
        simp only [extraction_preflight_field, run, bind_tc_ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          uncurry, ↓reduceIte, convertRun, core.result.Result.ok, suffixRun] at accepted
        have same := _root_.Option.some.inj (RustM.ok.inj accepted)
        obtain ⟨bound, suffixEq⟩ := suffix_some rest count actualTail suffixRun
        obtain ⟨form, parsedValue, contents⟩ := argument_span input 2#u8 parsed rest run
        have countValue := try_usize_value parsed count convertRun
        let payload : Slice U8 := ⟨rest.val.take count.val, by
          rw [List.length_take]
          exact (Nat.min_le_right _ _).trans rest.property⟩
        have payloadLength : payload.length = count.val := by
          change (rest.val.take count.val).length = count.val
          rw [List.length_take, Nat.min_eq_left bound]
        have payloadValue : value form = UScalar.cast .U64 payload.len := by
          apply UScalar.eq_of_val_eq
          rw [parsedValue, RegistrationSerializerFields.usize_cast, Slice.len_val, payloadLength, countValue]
        refine ⟨.bytes form payload payloadValue, rfl, ?_⟩
        rw [← same, suffixEq]
        change input.val = (bytes 2#u8 form ++ rest.val.take count.val) ++ rest.val.drop count.val
        rw [List.append_assoc, List.take_append_drop]
        exact contents

theorem field_span (input tail : Slice U8) (declared : U8)
    (allowed : declared = 0#u8 ∨ declared = 2#u8)
    (accepted : extraction_preflight_field input declared = .ok (.Some tail)) :
    ∃ atom : Atom, major atom = declared ∧ input.val = atomBytes atom ++ tail.val := by
  rcases allowed with rfl | rfl
  · exact uint_span input tail accepted
  · exact bytes_span input tail accepted


set_option backward.isDefEq.respectTransparency false in
theorem strip_span (input start tail : Slice U8)
    (accepted : extraction_strip_prefix input start = .ok (.Some tail)) :
    input.val = start.val ++ tail.val := by
  by_cases bound : start.len ≤ input.len
  · have inside : start.length ≤ input.length := by simpa only [UScalar.le_equiv, Slice.len_val] using bound
    obtain ⟨front, actualTail, split, frontBytes, tailBytes⟩ := RegistrationHeaderJump.split_prefix input start.len
      (input.val.take start.length) (input.val.drop start.length) (List.take_append_drop _ _).symm
      (by rw [List.length_take, Nat.min_eq_left inside, Slice.len_val])
    simp only [extraction_strip_prefix, core.slice.Slice.len, rust_primitives.slice.slice_length,
      bind_tc_ok, bound, ↓reduceIte, split, uncurry, RegistrationBytePrimitives.slice_eq_exact] at accepted
    by_cases same : front.val = start.val
    · simp only [same, decide_true, ↓reduceIte] at accepted
      have tailSame := _root_.Option.some.inj (RustM.ok.inj accepted)
      rw [← same, ← tailSame, frontBytes, tailBytes, List.take_append_drop]
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte] at accepted
      have impossible := RustM.ok.inj accepted
      cases impossible
  · simp only [extraction_strip_prefix, core.slice.Slice.len, rust_primitives.slice.slice_length,
      bind_tc_ok, bound, ↓reduceIte] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible

def atomsBytes : List Atom → List U8
  | [] => []
  | atom :: rest => atomBytes atom ++ atomsBytes rest

theorem six_atoms (input start : Slice U8) (a0 a1 a2 a3 a4 a5 : U8)
    (allowed0 : a0 = 0#u8 ∨ a0 = 2#u8) (allowed1 : a1 = 0#u8 ∨ a1 = 2#u8)
    (allowed2 : a2 = 0#u8 ∨ a2 = 2#u8) (allowed3 : a3 = 0#u8 ∨ a3 = 2#u8)
    (allowed4 : a4 = 0#u8 ∨ a4 = 2#u8) (allowed5 : a5 = 0#u8 ∨ a5 = 2#u8)
    (begin : RegistrationPreflightSix.Start input start)
    (work : RegistrationPreflightSix.Chain begin.tail a0 a1 a2 a3 a4 a5) :
    ∃ atoms : List Atom, atoms.length = 6 ∧ atoms.map major = [a0, a1, a2, a3, a4, a5] ∧
      input.val = start.val ++ atomsBytes atoms := by
  have startBytes := strip_span input start begin.tail begin.source
  obtain ⟨atom0, major0, bytes0⟩ := field_span begin.tail work.first.tail a0 allowed0 work.first.source
  obtain ⟨atom1, major1, bytes1⟩ := field_span work.first.tail work.second.tail a1 allowed1 work.second.source
  obtain ⟨atom2, major2, bytes2⟩ := field_span work.second.tail work.third.tail a2 allowed2 work.third.source
  obtain ⟨atom3, major3, bytes3⟩ := field_span work.third.tail work.fourth.tail a3 allowed3 work.fourth.source
  obtain ⟨atom4, major4, bytes4⟩ := field_span work.fourth.tail work.fifth.tail a4 allowed4 work.fifth.source
  obtain ⟨atom5, major5, bytes5⟩ := field_span work.fifth.tail work.sixth.tail a5 allowed5 work.sixth.source
  refine ⟨[atom0, atom1, atom2, atom3, atom4, atom5], rfl, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, major0, major1, major2, major3, major4, major5]
  · rw [startBytes, bytes0, bytes1, bytes2, bytes3, bytes4, bytes5, work.consumed]
    rfl

end BeaconcryptCore.Refinement.RegistrationLooseFieldSpan

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.try_usize_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.try_usize_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.suffix_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.suffix_some

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.uint_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.uint_span

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.bytes_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.bytes_span

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.field_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.field_span

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.strip_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.strip_span

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.six_atoms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFieldSpan.six_atoms
