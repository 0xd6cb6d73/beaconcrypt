-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCodecControlNormalization

/-! The local singleton cells used by the generated codec have one observable slot. Copying that slot into a value helper and copying its returned slot back preserves arbitrary effects and their returned state. This algebra applies only after the source checker has established that the local cell never escapes and every access is at index zero. -/

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization

universe v
variable {S A B : Type} {m : Type → Type v}

abbrev Cell (S : Type) := Fin 1 → S

def pack (value : S) : Cell S := fun _ => value
def unpack (cell : Cell S) : S := cell 0

theorem unpack_pack (value : S) : unpack (pack value) = value := rfl

theorem pack_unpack (cell : Cell S) : pack (unpack cell) = cell := by
  funext index
  have unique : index = 0 := Fin.eq_zero index
  subst index
  rfl

def scalarize [Functor m] (work : Cell S → m (A × Cell S)) (before : S) : m (A × S) :=
  (fun result => (result.1, unpack result.2)) <$> work (pack before)

def restore [Functor m] (work : S → m (A × S)) (before : Cell S) : m (A × Cell S) :=
  (fun result => (result.1, pack result.2)) <$> work (unpack before)

theorem restore_scalarize [Functor m] [LawfulFunctor m]
    (work : Cell S → m (A × Cell S)) (before : Cell S) :
    restore (scalarize work) before = work before := by
  simp only [restore, scalarize, pack_unpack, Functor.map_map]
  change id <$> work before = work before
  exact id_map _

theorem scalarize_restore [Functor m] [LawfulFunctor m]
    (work : S → m (A × S)) (before : S) :
    scalarize (restore work) before = work before := by
  simp only [restore, scalarize, unpack_pack, Functor.map_map]
  change id <$> work before = work before
  exact id_map _

theorem continuation_preserved [Monad m] [LawfulMonad m]
    (work : Cell S → m (A × Cell S)) (before : Cell S)
    (next : A → Cell S → m B) :
    (restore (scalarize work) before >>= fun result => next result.1 result.2) =
      (work before >>= fun result => next result.1 result.2) := by
  rw [restore_scalarize]

/-- An ignored Boolean result still forwards the updated cell before the next effect. -/
theorem ignored_result_preserved [Monad m] [LawfulMonad m]
    (work : Cell S → m (Bool × Cell S)) (before : Cell S)
    (next : Cell S → m B) :
    (restore (scalarize work) before >>= fun result => next result.2) =
      (work before >>= fun result => next result.2) := by
  rw [restore_scalarize]

end BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.unpack_pack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.unpack_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.pack_unpack' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.pack_unpack

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.restore_scalarize' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.restore_scalarize

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.scalarize_restore' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.scalarize_restore

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.continuation_preserved' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.continuation_preserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.ignored_result_preserved' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSingletonNormalization.ignored_result_preserved
