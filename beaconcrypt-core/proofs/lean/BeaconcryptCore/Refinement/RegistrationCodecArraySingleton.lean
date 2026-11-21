import Aeneas
import BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization

/-! The actual Aeneas array of length one is isomorphic to the finite singleton state used by the source normalization algebra. Index zero and assignment return the exact source value and updated array. Arbitrary effects and their returned state are retained when the array is copied through a scalar helper. No codec or primitive law is assumed. -/

set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
open Aeneas.Std
variable {S : Type}

abbrev Single (S : Type) := Aeneas.Std.Array S 1#usize

def pack (value : S) : Single S := Aeneas.Std.Array.repeat 1#usize value

def unpack (cell : Single S) : S :=
  cell.val[0]'(by have bound : cell.val.length = 1 := cell.property; simp [bound])

theorem unpack_pack (value : S) : unpack (pack value) = value := rfl

theorem pack_unpack (cell : Single S) : pack (unpack cell) = cell := by
  rcases cell with ⟨values, length⟩
  cases values with
  | nil => simp at length
  | cons value rest =>
      have empty : rest = [] := by simpa using length
      subst rest
      rfl

theorem index_pack (value : S) :
    Aeneas.Std.Array.index_usize (pack value) 0#usize = .ok value := rfl

theorem update_pack (before after : S) :
    Aeneas.Std.Array.update (pack before) 0#usize after = .ok (pack after) := rfl

def toCell (cell : Single S) : RegistrationCodecSingletonNormalization.Cell S :=
  RegistrationCodecSingletonNormalization.pack (unpack cell)

def ofCell (cell : RegistrationCodecSingletonNormalization.Cell S) : Single S :=
  pack (RegistrationCodecSingletonNormalization.unpack cell)

theorem ofCell_toCell (cell : Single S) : ofCell (toCell cell) = cell :=
  pack_unpack cell

theorem toCell_ofCell (cell : RegistrationCodecSingletonNormalization.Cell S) :
    toCell (ofCell cell) = cell := by
  change RegistrationCodecSingletonNormalization.pack (unpack (pack
    (RegistrationCodecSingletonNormalization.unpack cell))) = cell
  rw [unpack_pack, RegistrationCodecSingletonNormalization.pack_unpack]

universe v
variable {m : Type → Type v} {A B : Type}

def scalarize [Functor m] (work : Single S → m (A × Single S)) (before : S) : m (A × S) :=
  (fun result => (result.1, unpack result.2)) <$> work (pack before)

def restore [Functor m] (work : S → m (A × S)) (before : Single S) : m (A × Single S) :=
  (fun result => (result.1, pack result.2)) <$> work (unpack before)

theorem restore_scalarize [Functor m] [LawfulFunctor m]
    (work : Single S → m (A × Single S)) (before : Single S) :
    restore (scalarize work) before = work before := by
  simp only [restore, scalarize, pack_unpack, Functor.map_map]
  change id <$> work before = work before
  exact id_map _

theorem continuation_preserved [Monad m] [LawfulMonad m]
    (work : Single S → m (A × Single S)) (before : Single S)
    (next : A → Single S → m B) :
    (restore (scalarize work) before >>= fun result => next result.1 result.2) =
      (work before >>= fun result => next result.1 result.2) := by
  rw [restore_scalarize]

theorem ignored_result_preserved [Monad m] [LawfulMonad m]
    (work : Single S → m (Bool × Single S)) (before : Single S)
    (next : Single S → m B) :
    (restore (scalarize work) before >>= fun result => next result.2) =
      (work before >>= fun result => next result.2) := by
  rw [restore_scalarize]

end BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.unpack_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.unpack_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.pack_unpack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.pack_unpack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.index_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.index_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.update_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.update_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.ofCell_toCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.ofCell_toCell

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.toCell_ofCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.toCell_ofCell

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.restore_scalarize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.restore_scalarize

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.continuation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.continuation_preserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.ignored_result_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecArraySingleton.ignored_result_preserved
