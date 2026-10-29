-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth

/-! Alignment is an invariant of the actual current roster and current private key list. The owner index, private handle and public key remain separately represented; the invariant derives their relation. Reservation capacity is deliberately separate from this unconditional current-state property. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment
open RegistrationNativeSecretWordTargetPublication (key)
variable {KemSK : Type} {source : RegistrationNativeMldsa.Source}

def Aligned (owners : RegistrationNativePublicOwners.State source)
    (keys : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) : Prop :=
  keys.length = owners.length ∧ ∀ index owner, owners[index]? = some owner →
    ∃ pair, keys[index]? = some pair ∧ key owner = (index, pair.1)

/-- Empty public and private rosters satisfy the alignment invariant directly. -/
theorem empty : Aligned (source := source) ([] : RegistrationNativePublicOwners.State source)
    ([] : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) := by
  refine ⟨rfl, ?_⟩
  intro index owner found
  simp only [List.getElem?_nil] at found
  cases found

/-- A retained owner has the exact current private pair at its independently represented local index. -/
theorem owner (owners : RegistrationNativePublicOwners.State source)
    (keys : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (aligned : Aligned owners keys)
    (index : Nat) (selected : RegistrationNativePublicOwners.Owner source) (found : owners[index]? = some selected) :
    ∃ pair, keys[index]? = some pair ∧ selected.view.kemHandle = index ∧ selected.view.kemPublic = pair.1 := by
  obtain ⟨pair, current, same⟩ := aligned.2 index selected found
  exact ⟨pair, current, congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- Keeping the actual private keys and ordered owner metadata preserves alignment through arbitrary other state changes. -/
theorem same (before after : RegistrationNativePublicOwners.State source)
    (keys : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (aligned : Aligned before keys)
    (retained : after.map key = before.map key) : Aligned after keys := by
  refine ⟨?_, ?_⟩
  · have lengths := congrArg List.length retained
    simpa only [List.length_map, aligned.1] using lengths.symm
  · intro index selected found
    have mapped : (before.map key)[index]? = some (key selected) := by
      rw [← retained, List.getElem?_map, found, Option.map_some]
    rw [List.getElem?_map, Option.map_eq_some_iff] at mapped
    obtain ⟨earlier, earlierAt, sameKey⟩ := mapped
    obtain ⟨pair, privateAt, oldKey⟩ := aligned.2 index earlier earlierAt
    exact ⟨pair, privateAt, sameKey.symm.trans oldKey⟩

/-- A genuine birth followed by the total owner append extends alignment, including public-key aliases. -/
theorem append (before after : RegistrationNativePublicOwners.State source)
    (keys : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (aligned : Aligned before keys)
    (appended : after.map key = before.map key ++ [(keys.length, pair.1)]) :
    Aligned after (keys ++ [pair]) := by
  have lengths := congrArg List.length appended
  simp only [List.length_map, List.length_append, List.length_singleton] at lengths
  refine ⟨by rw [List.length_append, List.length_singleton, lengths, aligned.1], ?_⟩
  intro index selected found
  have mapped : (after.map key)[index]? = some (key selected) := by
    rw [List.getElem?_map, found, Option.map_some]
  rw [appended] at mapped
  by_cases earlier : index < before.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using earlier), List.getElem?_map,
      Option.map_eq_some_iff] at mapped
    obtain ⟨old, oldAt, sameKey⟩ := mapped
    obtain ⟨earlierPair, privateAt, oldKey⟩ := aligned.2 index old oldAt
    refine ⟨earlierPair, ?_, sameKey.symm.trans oldKey⟩
    rw [List.getElem?_append_left (by simpa only [aligned.1] using earlier), privateAt]
  · have within := (List.getElem?_eq_some_iff.mp found).1
    have last : index = before.length := by omega
    subst index
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self] at mapped
    simp only [List.getElem?_cons_zero, Option.some.injEq] at mapped
    refine ⟨pair, ?_, ?_⟩
    · rw [← aligned.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    · exact mapped.symm.trans (congrArg (fun count => (count, pair.1)) aligned.1)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.owner
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.same
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignment.append
