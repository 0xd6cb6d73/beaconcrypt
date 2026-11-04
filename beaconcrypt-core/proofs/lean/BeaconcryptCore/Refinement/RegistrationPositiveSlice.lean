import Aeneas

set_option warningAsError true

/-!
A strictly positive representation of the existing bounded slice. The pinned
slice's length proof depends on its list, which prevents using it inside mutual
CBOR datatypes. Here the proof depends on a separate natural number; the indexed
list fixes that number without referring to its elements in a proposition.
Both conversions preserve the full bounded list and are inverse. No codec law
or parser operation is assumed.
-/

namespace BeaconcryptCore.Refinement.RegistrationPositiveSlice

inductive Items (α : Type u) : Nat → Type u where
  | nil : Items α 0
  | cons : α → Items α n → Items α (n + 1)

def Items.toList : Items α n → List α
  | .nil => []
  | .cons value rest => value :: rest.toList

def Items.ofList : (values : List α) → Items α values.length
  | [] => .nil
  | value :: rest => .cons value (ofList rest)

@[simp] theorem Items.length_toList (values : Items α n) :
    values.toList.length = n := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [toList, ih]

@[simp] theorem Items.toList_ofList (values : List α) :
    (Items.ofList values).toList = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [ofList, toList, ih]

theorem Items.eq_of_toList_eq (left right : Items α n)
    (h : left.toList = right.toList) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons value rest ih =>
    cases right with
    | cons other tail =>
      have parts := List.cons.inj h
      rcases parts with ⟨rfl, same⟩
      rw [ih tail same]

structure PositiveSlice (α : Type u) where
  length : Nat
  items : Items α length
  bound : length ≤ Aeneas.Std.Usize.max

def PositiveSlice.toSlice (value : PositiveSlice α) : Aeneas.Std.Slice α :=
  ⟨value.items.toList, by simpa using value.bound⟩

def PositiveSlice.ofSlice (value : Aeneas.Std.Slice α) : PositiveSlice α :=
  ⟨value.val.length, Items.ofList value.val, value.property⟩

@[simp] theorem PositiveSlice.toSlice_ofSlice (value : Aeneas.Std.Slice α) :
    (PositiveSlice.ofSlice value).toSlice = value := by
  apply Subtype.ext
  exact Items.toList_ofList value.val

theorem PositiveSlice.ext (left right : PositiveSlice α)
    (h : left.toSlice = right.toSlice) : left = right := by
  cases left with
  | mk leftLength leftItems leftBound =>
    cases right with
    | mk rightLength rightItems rightBound =>
      have sameList : leftItems.toList = rightItems.toList := congrArg Subtype.val h
      have sameLength : leftLength = rightLength := by
        simpa using congrArg List.length sameList
      subst rightLength
      have sameItems := Items.eq_of_toList_eq leftItems rightItems sameList
      subst rightItems
      rfl

@[simp] theorem PositiveSlice.ofSlice_toSlice (value : PositiveSlice α) :
    PositiveSlice.ofSlice value.toSlice = value := by
  apply PositiveSlice.ext
  exact PositiveSlice.toSlice_ofSlice value.toSlice

instance : Coe (Aeneas.Std.Slice α) (PositiveSlice α) := ⟨PositiveSlice.ofSlice⟩
instance : Coe (PositiveSlice α) (Aeneas.Std.Slice α) := ⟨PositiveSlice.toSlice⟩

/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.Items.length_toList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Items.length_toList
/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.Items.toList_ofList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Items.toList_ofList
/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.Items.eq_of_toList_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Items.eq_of_toList_eq
/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice.toSlice_ofSlice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PositiveSlice.toSlice_ofSlice
/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice.ext' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PositiveSlice.ext
/-- info: 'BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice.ofSlice_toSlice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PositiveSlice.ofSlice_toSlice

end BeaconcryptCore.Refinement.RegistrationPositiveSlice
