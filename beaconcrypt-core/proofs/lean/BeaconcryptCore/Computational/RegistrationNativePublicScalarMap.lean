-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore

/-! Scalar-only reconstruction commutes with the actual local lifecycle updates. Public fields, signing history, phase, pool and environment remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicScalarMap
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeBeaconFrontend (Owner State M Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {source : RegistrationNativeMldsa.Source} {n : Nat} {KemSK Auxiliary Value Next : Type}

def alter (selected : Nat) (scalar : ScalarBytes) (index : Nat) (owner : Owner source) : Owner source :=
  if index = selected then { owner with prekeyScalar := scalar } else owner

def change (selected : Nat) (scalar : ScalarBytes) (owners : State source) : State source := owners.mapIdx (alter selected scalar)

/-- Lookup retains every public owner field while restoring only the selected scalar. -/
theorem lookup (selected : Nat) (scalar : ScalarBytes) (owners : State source) (index : Nat) :
    (change selected scalar owners)[index]? = (owners[index]?).map (alter selected scalar index) := List.getElem?_mapIdx

/-- Indexed owner updates commute with reconstruction at the same literal index. -/
theorem set (selected : Nat) (scalar : ScalarBytes) (owners : State source) (index : Nat) (owner : Owner source) :
    change selected scalar (owners.set index owner) = (change selected scalar owners).set index (alter selected scalar index owner) := List.mapIdx_set

/-- The scalar reconstruction and public prekey mask agree whenever the selected public key is already canonical. -/
theorem mask_eq (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : State source) (valid : ∀ owner, owners[selected]? = some owner → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey) :
    RegistrationNativePublicOwnerRestore.mask selected scalar publicPrekey owners = change selected scalar owners := by
  apply List.ext_getElem?
  intro index
  simp only [RegistrationNativePublicOwnerRestore.mask, change, List.getElem?_mapIdx]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [Option.map_some, alter]
      by_cases chosen : index = selected
      · subst index
        simp only [ite_true, valid owner found]
      · simp only [chosen, ite_false]

/-- A canonical public roster needs only its selected scalar restored; its public key is already exact. -/
theorem restored_dummy (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source)
    (valid : RegistrationNativePublicOwnerMask.Canonical selected publicPrekey owners) :
    change selected scalar (owners.map RegistrationNativePublicOwners.restore) = RegistrationNativePublicSourceState.owners scalar owners := by
  rw [← RegistrationNativePublicOwnerRestore.restored_dummy selected scalar publicPrekey owners valid]
  apply (mask_eq selected scalar publicPrekey _ _).symm
  intro owner found
  simp only [List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨exposed, present, rfl⟩ := found
  have chosen := (valid selected exposed present)
  simp only [RegistrationNativePublicOwnerMask.At, ite_true] at chosen
  exact chosen.2

def Equivariant (selected : Nat) (scalar : ScalarBytes) (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env, Prod.map (Prod.map id (change selected scalar)) id <$> (work.run owners).run env =
    (work.run (change selected scalar owners)).run env

end BeaconcryptCore.Computational.RegistrationNativePublicScalarMap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.lookup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.set
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.mask_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.mask_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.restored_dummy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicScalarMap.restored_dummy
