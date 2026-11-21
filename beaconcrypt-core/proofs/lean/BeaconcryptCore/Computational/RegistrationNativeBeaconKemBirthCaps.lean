-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationNativeBeaconKemCaps (Bounded pure_bound bind_bound)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
def Born : (Trusted n KemSK).Domain → Prop
  | .inr (.inr (.inl .create)) => True
  | _ => False
instance (query : (Trusted n KemSK).Domain) : Decidable (Born query) := by
  cases query with
  | inl query => exact isFalse (fun h => h)
  | inr query => cases query with
    | inl query => exact isFalse (fun h => h)
    | inr query => cases query with
      | inr query => exact isFalse (fun h => h)
      | inl query => cases query with
        | create => exact isTrue trivial
        | decapsulate handle ciphertext => exact isFalse (fun h => h)
        | reveal handle => exact isFalse (fun h => h)

theorem effect_free (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded Born 0 (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) := by
  intro owners env
  change IsQueryBoundP ((fun reply => ((reply, owners), env)) <$>
    ((Trusted n KemSK).query (.inl query) : OracleComp (Trusted n KemSK) _)) Born 0
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  exact False.elim

theorem sample_free (work : ProbComp A) :
    Bounded Born 0 (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  intro owners env
  apply RegistrationNativePlatformQueryBounds.simulate_bound (fun _ => False) Born
    (fun query => RegistrationNativeBeaconFrontend.effect (.inl query)) _ work 0 (isQueryBoundP_false work 0) owners env
  intro query current previous
  exact effect_free (.inl query) current previous

theorem kem_bound (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Bounded Born (if Born (n := n) (KemSK := KemSK) (.inr query : (Trusted n KemSK).Domain) then 1 else 0)
      (RegistrationNativeBeaconFrontend.kem (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) query) := by
  intro owners env
  change IsQueryBoundP ((fun reply => ((reply, owners), env)) <$>
    ((Trusted n KemSK).query (.inr query) : OracleComp (Trusted n KemSK) _)) Born _
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro called
  rw [ite_eq_left called]
  omega

theorem prepare_free (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded Born 0 (RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.prepare
  cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div =>
      exact pure_bound Born 0 _
  | ok pin =>
      simp only
      apply bind_bound Born _ _ 0 0 (sample_free _)
      intro identity
      exact bind_bound Born _ _ 0 0 (sample_free _) (fun _ => pure_bound Born 0 _)

theorem appendBorn (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed)
    (prekey : PqxdhJointGapDh.ScalarBytes) :
    Bounded Born 1 (RegistrationNativeBeaconFrontend.appendBorn (n := n) (Auxiliary := Auxiliary) setup source edPin keyId pin identity prekey) := by
  unfold RegistrationNativeBeaconFrontend.appendBorn
  apply bind_bound _ _ _ 1 0 (kem_bound _)
  intro born
  apply bind_bound _ _ _ 0 0 (effect_free _)
  intro worldOwner
  apply bind_bound _ _ _ 0 0
  · intro owners env
    change IsQueryBoundP (pure ((owners, owners), env)) Born 0
    trivial
  · intro owners
    apply bind_bound _ _ _ 0 0
    · intro before env
      change IsQueryBoundP (pure (((), _), env)) Born 0
      trivial
    · intro unused
      exact pure_bound _ 0 _

theorem create (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded Born 1 (RegistrationNativeBeaconFrontend.create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
  unfold RegistrationNativeBeaconFrontend.create
  apply bind_bound _ _ _ 0 1 (prepare_free edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_bound _ 1 _
  | ok prepared => cases prepared with
    | none => exact pure_bound _ 1 _
    | some prepared => exact appendBorn setup edPin keyId prepared.pin prepared.identity prepared.prekey
end BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.effect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.effect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.sample_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.sample_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.kem_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.prepare_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.prepare_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.appendBorn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.appendBorn
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps.create
