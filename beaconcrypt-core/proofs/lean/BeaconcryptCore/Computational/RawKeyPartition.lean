import BeaconcryptCore.Computational.AdaptiveRawKeyPreparation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Eight statements split the actual independently sampled finite key family at any selected index. The index bijection preserves coincident values and charges no hidden extra key draw. The sampling law quantifies over the complete evaluated continuation, including all retained private state. Update and reconstruction laws preserve the original index and every unselected entry.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawKeyPartition

noncomputable def join {Value : Type} {count : Nat} (target : Fin (count + 1))
    (selected : Value) (others : Fin count → Value) : Fin (count + 1) → Value :=
  fun index => match finSuccEquiv' target index with
  | none => selected
  | some other => others other

/-- Selecting the designated original index returns exactly the selected value. -/
theorem join_target {Value : Type} {count : Nat} (target : Fin (count + 1))
    (selected : Value) (others : Fin count → Value) :
    join target selected others target = selected := by
  simp [join]

/-- Every other original index retains its corresponding other-family value. -/
theorem join_other {Value : Type} {count : Nat} (target : Fin (count + 1))
    (selected : Value) (others : Fin count → Value) (other : Fin count) :
    join target selected others (target.succAbove other) = others other := by
  simp [join]

noncomputable def partition {Value : Type} {count : Nat} (target : Fin (count + 1)) :
    (Value × (Fin count → Value)) ≃ (Fin (count + 1) → Value) where
  toFun pair := join target pair.1 pair.2
  invFun values := (values target, fun other => values (target.succAbove other))
  left_inv pair := by simp [join_target, join_other]
  right_inv values := by
    funext index
    obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
    cases position <;> simp [join]

/-- The selected draw and remaining-family draw reproduce the actual full-family distribution. -/
theorem sampled_partition (count : Nat) (target : Fin (count + 1)) :
    𝒮[do let key ← $ᵗ CtxRomAuth.CtxKey
          let others ← $ᵗ (Fin count → CtxRomAuth.CtxKey)
          pure (join target key others)] =
      𝒮[$ᵗ (Fin (count + 1) → CtxRomAuth.CtxKey)] := by
  have transported := @evalSPMF_uniformSample (Fin (count + 1) → CtxRomAuth.CtxKey)
    (SampleableType.ofEquiv (partition target)) inferInstance inferInstance
  change 𝒮[partition target <$> (Prod.mk <$> ($ᵗ CtxRomAuth.CtxKey) <*> ($ᵗ (Fin count → CtxRomAuth.CtxKey)))] = _ at transported
  simpa only [seq_eq_bind_map, bind_map_left, map_bind, Functor.map_map, bind_pure_comp, partition, Equiv.coe_fn_mk] using
    transported.trans (evalSPMF_uniformSample (Fin (count + 1) → CtxRomAuth.CtxKey)).symm

/-- The sampling partition is valid under every complete evaluated continuation. -/
theorem partition_continuation {Result : Type} (count : Nat) (target : Fin (count + 1))
    (next : (Fin (count + 1) → CtxRomAuth.CtxKey) → ProbComp Result) :
    𝒮[($ᵗ (Fin (count + 1) → CtxRomAuth.CtxKey)) >>= next] =
      𝒮[do let key ← $ᵗ CtxRomAuth.CtxKey
            let others ← $ᵗ (Fin count → CtxRomAuth.CtxKey)
            next (join target key others)] := by
  have complete := congrArg (fun distribution => distribution >>= fun keys => 𝒮[next keys])
    (sampled_partition count target).symm
  simpa only [← evalSPMF_bind, bind_assoc, pure_bind] using complete

/-- Updating the selected state changes exactly its original source entry. -/
theorem join_selected_update {Value : Type} {count : Nat} (target : Fin (count + 1))
    (selected updated : Value) (others : Fin count → Value) :
    join target updated others = Function.update (join target selected others) target updated := by
  funext index
  obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
  cases position <;> simp [join, Function.update]

/-- Updating an unselected state preserves its original source index and every other entry. -/
theorem join_other_update {Value : Type} {count : Nat} (target : Fin (count + 1))
    (selected updated : Value) (others : Fin count → Value) (other : Fin count) :
    join target selected (Function.update others other updated) =
      Function.update (join target selected others) (target.succAbove other) updated := by
  funext index
  obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
  cases position with
  | none => simp [join, Function.update]
  | some position =>
    by_cases equal : position = other
    · subst position
      simp [join, Function.update]
    · simp [join, Function.update, equal]

/-- Empty identical initial states reconstruct the complete source family. -/
theorem join_constant {Value : Type} {count : Nat} (target : Fin (count + 1)) (value : Value) :
    join target value (fun _ => value) = fun _ => value := by
  funext index
  simp only [join]
  split <;> rfl

/-- Partitioning and reconstructing an arbitrary value family loses no value or alias. -/
theorem join_reconstruct {Value : Type} {count : Nat} (target : Fin (count + 1))
    (values : Fin (count + 1) → Value) :
    join target (values target) (fun other => values (target.succAbove other)) = values :=
  (partition target).apply_symm_apply values

end BeaconcryptCore.Computational.RawKeyPartition

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_target

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_other

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.sampled_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.sampled_partition

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.partition_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.partition_continuation

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_selected_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_selected_update

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_other_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_other_update

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_constant

/-- info: 'BeaconcryptCore.Computational.RawKeyPartition.join_reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawKeyPartition.join_reconstruct
