import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.Model.Pqxdh.Protocol

/-!
# Byte-level abstraction between the extracted code and the ideal PQXDH model

The generated code of `BeaconcryptCore/Extraction/Funs.lean` works with Rust byte
arrays (`Aeneas.Std.Array Std.U8 n`), while the ideal model of
`BeaconcryptCore/Model/Pqxdh` works with `Pqxdh.Bytes = List UInt8`.

This file provides the abstraction function `absBytes` together with the reasoning
principle that every byte-building routine of the generated code relies on:
`core::array::from_fn` applied to a *pure* closure (one that never fails and never
updates its captured state) returns the array `(List.range N).map g`.
-/

open CoreModels Aeneas
open beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PqxdhRefinement

/-! ## Abstraction -/

/-- Abstraction of a Rust byte to a model byte. -/
def absByte (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- Abstraction of a fixed-size Rust byte array to a model byte string. -/
def absBytes {n : Std.Usize} (a : Std.Array Std.U8 n) : Pqxdh.Bytes := a.val.map absByte

@[simp] theorem absBytes_length {n : Std.Usize} (a : Std.Array Std.U8 n) :
    (absBytes a).length = n.val := by
  simp [absBytes, a.property]

/-! ## A generic list fact -/

/-- Reading a list back at every index of its range returns the list. -/
theorem map_range_getElem! {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact getElem!_pos l i h2

/-! ## `core::array::from_fn` with a pure closure -/

variable {T F : Type}

/-- The monadic fold that `from_fn` runs, when the closure is pure. -/
private theorem foldlM_pure (inst : core.ops.function.FnMut F Std.Usize T) (f : F)
    (g : ℕ → T) (l : List ℕ)
    (h : ∀ i ∈ l, inst.call_mut f ⟨BitVec.ofNat _ i⟩ = ok (g i, f)) (acc : List T) :
    l.foldlM (fun (s : List T × F) (i : Nat) =>
        inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩ >>= fun d =>
          ok (s.1 ++ [d.1], d.2)) (acc, f) = ok (acc ++ l.map g, f) := by
  induction l generalizing acc with
  | nil => simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
  | cons a l ih =>
    have ha := h a (by simp)
    simp only [List.foldlM_cons, ha, bind_tc_ok, List.map_cons]
    rw [ih (fun i hi => h i (by simp [hi]))]
    simp

private theorem array_from_fn_go_pure (inst : core.ops.function.FnMut F Std.Usize T) (f : F)
    (g : ℕ → T) (n : ℕ)
    (h : ∀ i, i < n → inst.call_mut f ⟨BitVec.ofNat _ i⟩ = ok (g i, f)) :
    rust_primitives.slice.array_from_fn_go inst f n = ok ((List.range n).map g, f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rust_primitives.slice.array_from_fn_go]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    simp only [bind_tc_ok]
    rw [h n (Nat.lt_succ_self n)]
    simp [List.range_succ]

/-- `core::array::from_fn` applied to a closure that never fails and never changes its
captured state produces the array of the values of that closure. -/
theorem from_fn_pure (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (f : F) (g : ℕ → T)
    (h : ∀ i, i < N.val → inst.call_mut f ⟨BitVec.ofNat _ i⟩ = ok (g i, f)) :
    ∃ a : Std.Array T N,
      core.array.from_fn N inst f = ok a ∧ a.val = (List.range N.val).map g := by
  have hgo := array_from_fn_go_pure inst f g N.val h
  refine ⟨⟨(List.range N.val).map g, by simp⟩, ?_, rfl⟩
  simp only [core.array.from_fn, rust_primitives.slice.array_from_fn]
  rw [hgo]
  simp

/-! ## Small scalar and array facts -/

@[simp] theorem usize_val_1 : (1#usize).val = 1 := by scalar_tac
@[simp] theorem usize_val_2 : (2#usize).val = 2 := by scalar_tac
@[simp] theorem usize_val_8 : (8#usize).val = 8 := by scalar_tac
@[simp] theorem usize_val_32 : (32#usize).val = 32 := by scalar_tac
@[simp] theorem usize_val_33 : (33#usize).val = 33 := by scalar_tac
@[simp] theorem usize_val_34 : (34#usize).val = 34 := by scalar_tac
@[simp] theorem usize_val_64 : (64#usize).val = 64 := by scalar_tac
@[simp] theorem usize_val_153 : (153#usize).val = 153 := by scalar_tac
@[simp] theorem usize_val_192 : (192#usize).val = 192 := by scalar_tac
@[simp] theorem usize_val_1088 : (1088#usize).val = 1088 := by scalar_tac
@[simp] theorem usize_val_1184 : (1184#usize).val = 1184 := by scalar_tac
@[simp] theorem usize_val_1185 : (1185#usize).val = 1185 := by scalar_tac

/-- The `Usize` built from a natural number below `2 ^ 32` has that value. -/
theorem usize_mk_val (i : ℕ) (h : i < 2 ^ 32) :
    (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := by
  have h64 : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := by norm_num
  have hb : i < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  simp [Std.UScalar.val, Nat.mod_eq_of_lt hb]

/-- Indexing inside the bounds of a Rust array. -/
theorem index_usize_eq {α : Type} [Inhabited α] {n : Std.Usize} (a : Std.Array α n)
    (i : Std.Usize) (h : i.val < n.val) :
    Std.Array.index_usize a i = ok (a.val[i.val]!) := by
  have hlen : a.val.length = n.val := a.property
  have hi : i.val < a.val.length := by omega
  unfold Std.Array.index_usize
  rw [Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem hi, getElem!_pos a.val i.val hi]

/-- Indexing a Rust array through the slice interface. -/
theorem array_index_eq {α : Type} [Inhabited α] {n : Std.Usize} (a : Std.Array α n)
    (i : Std.Usize) (h : i.val < n.val) :
    rust_primitives.slice.array_index a i = ok a.val[i.val]! := by
  have hlen : a.val.length = n.val := a.property
  have hi : i.val < a.val.length := by omega
  unfold rust_primitives.slice.array_index Std.Slice.index_usize
  rw [show ((Std.Array.to_slice a)[i]?) = a.val[i.val]? from rfl,
    List.getElem?_eq_getElem hi, getElem!_pos a.val i.val hi]

/-- Checked Rust subtraction succeeds and computes the difference when it does not
underflow. -/
theorem usize_sub_eq (x y : Std.Usize) (h : y.val ≤ x.val) :
    x - y = ok ⟨BitVec.ofNat _ (x.val - y.val)⟩ := by
  show Std.UScalar.sub x y = _
  simp [Std.UScalar.sub, Nat.not_lt.mpr h]

/-- Checked Rust addition succeeds and computes the sum when it does not overflow. -/
theorem usize_add_val (x y : Std.Usize) (h : x.val + y.val < 2 ^ System.Platform.numBits) :
    ∃ z : Std.Usize, x + y = ok z ∧ z.val = x.val + y.val := by
  have hb : Std.UScalar.inBounds .Usize (x.val + y.val) := h
  have hspec := Std.UScalar.tryMk_eq .Usize (x.val + y.val)
  show ∃ z, Std.UScalar.add x y = ok z ∧ _
  unfold Std.UScalar.add
  cases hc : Std.UScalar.tryMk (.Usize) (x.val + y.val) with
  | ok z => rw [hc] at hspec; exact ⟨z, rfl, hspec.1⟩
  | fail e => rw [hc] at hspec; exact absurd hb hspec
  | div => rw [hc] at hspec; exact absurd hspec (by simp)

/-! ## Injectivity of the byte abstraction -/

theorem absByte_injective : Function.Injective absByte := by
  intro x y h
  have hx : x.val < 2 ^ 8 := x.bv.isLt
  have hy : y.val < 2 ^ 8 := y.bv.isLt
  have hv : x.val = y.val := by
    have := congrArg UInt8.toNat h
    simpa [absByte, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this
  cases x; cases y
  simpa [Std.UScalar.val, BitVec.toNat_inj] using hv

theorem absBytes_inj_iff {n : Std.Usize} (a b : Std.Array Std.U8 n) :
    absBytes a = absBytes b ↔ a.val = b.val := by
  constructor
  · exact fun h => List.map_injective_iff.mpr absByte_injective h
  · intro h; simp [absBytes, h]

/-! ## Rust array equality -/

/-- One unfolding of the generic Rust loop combinator. -/
theorem loop_unfold {α β : Type} (body : α → RustM (ControlFlow α β)) (x : α) :
    Std.loop body x = (body x >>= fun r =>
      match r with
      | ControlFlow.cont y => Std.loop body y
      | ControlFlow.done v => ok v) := by
  conv_lhs => rw [Std.loop]
  cases body x <;> rfl

private theorem array_eq_loop_aux {n : Std.Usize} (a b : Std.Array Std.U8 n) (k : ℕ) :
    ∀ i : Std.Usize, i.val + k = n.val →
      core.Array.Insts.CoreCmpPartialEqArray.eq_loop core.U8.Insts.CoreCmpPartialEqU8 a b i
        = ok (decide (∀ j, i.val ≤ j → j < n.val → a.val[j]! = b.val[j]!)) := by
  induction k with
  | zero =>
    intro i hi
    have hnot : ¬ (i < n) := by rw [Std.UScalar.lt_equiv]; omega
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
    rw [loop_unfold]
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    rw [if_neg hnot]
    simp only [bind_tc_ok]
    congr 1
    symm
    simp only [decide_eq_true_eq]
    intro j h1 h2; omega
  | succ k ih =>
    intro i hi
    have hlt : i < n := by rw [Std.UScalar.lt_equiv]; omega
    have hia : i.val < n.val := by omega
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
    rw [loop_unfold]
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    rw [if_pos hlt, array_index_eq a i hia]
    simp only [bind_tc_ok]
    rw [array_index_eq b i hia]
    simp only [bind_tc_ok, core.U8.Insts.CoreCmpPartialEqU8]
    by_cases heq : a.val[i.val]! = b.val[i.val]!
    · have hnb : n.val < 2 ^ System.Platform.numBits := n.bv.isLt
      obtain ⟨z, hz, hzv⟩ := usize_add_val i 1#usize (by simp; omega)
      simp only [heq, beq_self_eq_true, if_true, hz, bind_tc_ok]
      have hih := ih z (by rw [hzv]; simp; omega)
      unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
        core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body at hih
      simp only [core.U8.Insts.CoreCmpPartialEqU8, bind_tc_ok] at hih
      rw [hih]
      congr 1
      simp only [decide_eq_decide]
      have hzv' : z.val = i.val + 1 := by rw [hzv, usize_val_1]
      constructor
      · intro h j h1 h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | h3
        · exact heq
        · exact h j (by omega) h2
      · intro h j h1 h2
        exact h j (by omega) h2
    · have hne : (a.val[i.val]! == b.val[i.val]!) = false := by simpa using heq
      simp only [hne, if_false, bind_tc_ok, Bool.false_eq_true]
      congr 1
      symm
      simp only [decide_eq_false_iff_not]
      exact fun hc => heq (hc i.val le_rfl hia)

/-- Generated array equality decides equality of the abstracted byte strings. -/
theorem array_eq_abs {n : Std.Usize} (a b : Std.Array Std.U8 n) :
    core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
      = ok (decide (absBytes a = absBytes b)) := by
  have hla : a.val.length = n.val := a.property
  have hlb : b.val.length = n.val := b.property
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq
  rw [array_eq_loop_aux a b n.val 0#usize (by simp)]
  congr 1
  simp only [decide_eq_decide, absBytes_inj_iff]
  constructor
  · intro h
    apply List.ext_getElem (by omega)
    intro j h1 h2
    have := h j (by simp) (by omega)
    rwa [getElem!_pos a.val j h1, getElem!_pos b.val j h2] at this
  · intro h j _ h2
    rw [h]

end PqxdhRefinement
