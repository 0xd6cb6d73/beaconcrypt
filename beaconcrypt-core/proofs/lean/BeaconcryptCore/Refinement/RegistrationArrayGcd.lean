-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationArrayExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationArrayPlatform
import BeaconcryptCore.Refinement.RegistrationArrayIndex

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

set_option autoImplicit false
set_option warningAsError true

/-! Exact finite evaluation of the extracted Euclidean loop for consecutive positive inputs. The source loop and its body remain explicit dependencies; no GCD, termination, parser or readback premise is assumed. -/

namespace BeaconcryptCore.Refinement.RegistrationArrayGcd
open beaconcrypt_parse.cbordetveraux

private theorem singleton_index (value : Usize) :
    Array.index_usize (Array.repeat 1#usize value) 0#usize = .ok value := rfl

private theorem singleton_update (before after : Usize) :
    Array.update (Array.repeat 1#usize before) 0#usize after =
      .ok (Array.repeat 1#usize after) := rfl

theorem remainder_one (n : Usize) :
    core.num.Usize.wrapping_rem n 1#usize = .ok 0#usize := by
  rcases WP.spec_imp_exists (UScalar.rem_spec n (by decide : (1#usize : Usize).val ≠ 0)) with
    ⟨result, actual, value⟩
  exact actual.trans (congrArg RustM.ok (UScalar.eq_of_val_eq (by
    simpa only [show (1#usize : Usize).val = 1 from rfl,
      show (0#usize : Usize).val = 0 from rfl, Nat.mod_one] using value)))

theorem remainder_consecutive (n offset : Usize) (large : 1 < offset.val)
    (consecutive : n.val = offset.val + 1) :
    core.num.Usize.wrapping_rem n offset = .ok 1#usize := by
  have spec := UScalar.rem_spec n (by omega : offset.val ≠ 0)
  rcases WP.spec_imp_exists spec with ⟨result, actual, value⟩
  change UScalar.rem n offset = RustM.ok (1#usize)
  rw [show UScalar.rem n offset = .ok result from actual, RustM.ok.injEq,
    UScalar.eq_equiv]
  simpa only [value, consecutive, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_eq_of_lt large, Nat.mod_mod] using (show 1 = (1#usize : Usize).val from rfl)

theorem body_step (n offset remainder : Usize)
    (actual : core.num.Usize.wrapping_rem n offset = .ok remainder) :
    extraction_serialize_array_loop0.body (Array.repeat 1#usize n)
      (Array.repeat 1#usize offset) true = .ok (.cont
        (Array.repeat 1#usize offset, Array.repeat 1#usize remainder,
          decide (remainder > 0#usize))) := by
  simp only [extraction_serialize_array_loop0.body, ↓reduceIte, singleton_index,
    singleton_update, actual, bind_tc_ok]

theorem body_consecutive (n offset : Usize) (large : 1 < offset.val)
    (consecutive : n.val = offset.val + 1) :
    extraction_serialize_array_loop0.body (Array.repeat 1#usize n)
      (Array.repeat 1#usize offset) true = .ok (.cont
        (Array.repeat 1#usize offset, Array.repeat 1#usize 1#usize, true)) :=
  body_step n offset 1#usize (remainder_consecutive n offset large consecutive)

theorem body_one (n : Usize) :
    extraction_serialize_array_loop0.body (Array.repeat 1#usize n)
      (Array.repeat 1#usize 1#usize) true = .ok (.cont
        (Array.repeat 1#usize 1#usize, Array.repeat 1#usize 0#usize, false)) :=
  body_step n 1#usize 0#usize (remainder_one n)

theorem loop_unfold (pn pl : Array Usize 1#usize) (condition : Bool) :
    extraction_serialize_array_loop0 pn pl condition = (do
      let step ← extraction_serialize_array_loop0.body pn pl condition
      match step with
      | .cont next => extraction_serialize_array_loop0 next.1 next.2.1 next.2.2
      | .done result => .ok result) := by
  unfold extraction_serialize_array_loop0
  conv_lhs => rw [loop]
  dsimp only
  cases extraction_serialize_array_loop0.body pn pl condition with
  | ok result => cases result <;> simp only [bind_tc_ok, Prod.eta]
  | fail error => rfl
  | div => rfl

theorem loop_step (n offset remainder : Usize)
    (actual : core.num.Usize.wrapping_rem n offset = .ok remainder) :
    extraction_serialize_array_loop0 (Array.repeat 1#usize n)
      (Array.repeat 1#usize offset) true =
      extraction_serialize_array_loop0 (Array.repeat 1#usize offset)
        (Array.repeat 1#usize remainder) (remainder > 0#usize) := by
  rw [loop_unfold, body_step n offset remainder actual]
  rfl

theorem body_stop (pn pl : Array Usize 1#usize) :
    extraction_serialize_array_loop0.body pn pl false = .ok (.done pn) := rfl

theorem loop_stop (pn pl : Array Usize 1#usize) :
    extraction_serialize_array_loop0 pn pl false = .ok pn := by
  rw [loop_unfold, body_stop]
  rfl

theorem gcd_one (n : Usize) :
    extraction_serialize_array_loop0 (Array.repeat 1#usize n)
      (Array.repeat 1#usize 1#usize) true = .ok (Array.repeat 1#usize 1#usize) := by
  rw [loop_step n 1#usize 0#usize (remainder_one n)]
  exact loop_stop (Array.repeat 1#usize 1#usize) (Array.repeat 1#usize 0#usize)

theorem gcd_consecutive (n offset : Usize) (positive : 0 < offset.val)
    (consecutive : n.val = offset.val + 1) :
    extraction_serialize_array_loop0 (Array.repeat 1#usize n)
      (Array.repeat 1#usize offset) true = .ok (Array.repeat 1#usize 1#usize) := by
  by_cases one : offset.val = 1
  · simpa only [show offset = 1#usize from UScalar.eq_of_val_eq one] using gcd_one n
  · rw [loop_step n offset 1#usize (remainder_consecutive n offset (by omega) consecutive)]
    exact gcd_one offset

theorem gcd_consecutive_nat (offset : Nat) (positive : 0 < offset)
    (representable : offset + 1 < 2 ^ UScalarTy.Usize.numBits) :
    extraction_serialize_array_loop0
      (Array.repeat 1#usize (Usize.ofNatCore (offset + 1) representable))
      (Array.repeat 1#usize (Usize.ofNatCore offset (by omega))) true =
      .ok (Array.repeat 1#usize 1#usize) := by
  exact gcd_consecutive _ _ positive rfl

theorem wrapping_div_one (n : Usize) :
    core.num.Usize.wrapping_div n 1#usize = .ok n := by
  rcases UScalar.div_spec n (by decide : (1#usize : Usize).val ≠ 0) with
    ⟨result, actual, value⟩
  exact actual.trans (congrArg RustM.ok (UScalar.eq_of_val_eq (by
    simpa only [show (1#usize : Usize).val = 1 from rfl, Nat.div_one] using value)))

end BeaconcryptCore.Refinement.RegistrationArrayGcd

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.remainder_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.remainder_one
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.remainder_consecutive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.remainder_consecutive
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.body_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.body_step
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.body_consecutive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.body_consecutive
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.body_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.body_one
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_unfold
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_step
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.body_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.body_stop
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.loop_stop
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_one
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_consecutive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_consecutive
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_consecutive_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.gcd_consecutive_nat
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayGcd.wrapping_div_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayGcd.wrapping_div_one
