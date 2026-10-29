-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceState

/-! The public owner roster erases exactly the selected scalar and retains its public prekey. This canonical mask is pure metadata, initialized by the empty roster and re-established by actual native birth/outgoing packing. Only private source reconstruction supplies the erased scalar. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask
open RegistrationNativePublicOwners (Owner State pack)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
variable {source : RegistrationNativeMldsa.Source}

def At (selected index : Nat) (publicPrekey : PeerEncoding) (owner : Owner source) : Prop :=
  if index = selected then owner.scalar = none ∧
    owner.view.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey
  else owner.scalar.isSome = true

def Canonical (selected : Nat) (publicPrekey : PeerEncoding) (owners : State source) : Prop :=
  ∀ index owner, owners[index]? = some owner → At selected index publicPrekey owner

/-- Empty startup contains no scalar to restore or erase. -/
theorem empty (selected : Nat) (publicPrekey : PeerEncoding) :
    Canonical selected publicPrekey ([] : State source) := by
  intro index owner found
  simp at found

/-- Packing any actual native roster erases only the selected scalar and retains its challenge public key. -/
theorem packed (selected : Nat) (publicPrekey : PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) : Canonical selected publicPrekey (pack selected publicPrekey owners) := by
  intro index owner found
  simp only [pack, List.getElem?_mapIdx, Option.map_eq_some_iff] at found
  obtain ⟨original, _present, rfl⟩ := found
  by_cases chosen : index = selected
  · simp [At, chosen, RegistrationBeaconReferenceCompiler.eraseOwner]
  · simp only [At, chosen, ite_false]
    rfl

private theorem restore_at (selected index : Nat) (publicPrekey : PeerEncoding)
    (scalar : ScalarBytes) (owner : Owner source) (valid : At selected index publicPrekey owner) :
    (if index = selected then
      (⟨RegistrationBeaconReferenceCompiler.eraseOwner
        { RegistrationNativePublicSourceState.owner scalar owner with prekeyPublic := PqxdhRootTableInitialization.rootArray publicPrekey }, none⟩ : Owner source)
    else ⟨RegistrationBeaconReferenceCompiler.eraseOwner (RegistrationNativePublicSourceState.owner scalar owner),
      some (RegistrationNativePublicSourceState.owner scalar owner).prekeyScalar⟩) = owner := by
  rcases owner with ⟨view, localScalar⟩
  by_cases chosen : index = selected
  · simp only [At, chosen, ite_true] at valid ⊢
    obtain ⟨absent, publicKey⟩ := valid
    subst localScalar
    rw [← publicKey]
    rfl
  · simp only [At, chosen, ite_false] at valid ⊢
    cases actual : localScalar with
    | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at valid
    | some actual =>
        simp only [RegistrationNativePublicSourceState.owner, Option.getD_some,
          RegistrationBeaconReferenceCompiler.erase_restore]
        rfl

/-- Restoring the selected private scalar and packing again leaves every canonical public owner field exactly unchanged. -/
theorem pack_restore (selected : Nat) (publicPrekey : PeerEncoding) (scalar : ScalarBytes)
    (owners : State source) (valid : Canonical selected publicPrekey owners) :
    pack selected publicPrekey (RegistrationNativePublicSourceState.owners scalar owners) = owners := by
  apply List.ext_getElem?
  intro index
  simp only [pack, RegistrationNativePublicSourceState.owners, List.getElem?_mapIdx, List.getElem?_map]
  cases found : owners[index]? with
  | none => simp only [Option.map_none]
  | some owner =>
      simp only [Option.map_some]
      rw [restore_at selected index publicPrekey scalar owner (valid index owner found)]

end BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.packed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.packed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.pack_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask.pack_restore
