-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemBirth
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
/-! The literal new shared-platform Word constructor preserves or appends exactly its same genuine private KEM row under arbitrary persistent Word interpretation. Native preparation failures, public owner packing, external state and all returned outcomes remain source-derived. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message zero)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordTargetPublication (key pack_keys restore_keys)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform Private A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "trusted" => RegistrationNativePlatformLorSourceKemBirth.trusted implementation

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

/-- Exact source owner restoration/packing retains the same private interpretation and literal external poststate. -/
theorem local_run (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (before : Private) :
    (simulateQ implementation (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
      ((((RegistrationNativePlatformPublicOwners.executeLocal selectedOwner publicPrekey
        (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformPublicFrontend.trusted work)).run owners).run env).run previous))).run before =
    (fun result => ((((result.1.1.1,RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2),result.1.2),previous),result.2)) <$>
      (simulateQ trusted ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env)).run before := by
  simp only [RegistrationNativePlatformPublicOwners.executeLocal,RegistrationNativePlatformGenericBundle.liftLegacy,
    StateT.run,simulateQ_map,map_apply]
  have nativeEq := RegistrationNativePlatformSecretWordAliasCreate.native_program ((work.run (owners.map RegistrationNativePublicOwners.restore)).run env) previous
  simp only [StateT.run] at nativeEq
  rw [nativeEq]
  simp only [simulateQ_map,map_apply,Functor.map_map,RegistrationNativePlatformLorSourceKemBirth.trusted,QueryImpl.simulateQ_compose]
  rfl

variable (setup : Setup base KemSK) (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable {E : Type} (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordOrdinary.handler (n := n) setup source selectedOwner publicPrekey reserveFrame writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

/-- The actual current shared-platform constructor has its genuine native body under the same arbitrary persistent private interpretation. -/
theorem create_run (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State source Platform Private) :
    (typed (.inr (.create edPin mlPin keyId))).run before =
    (fun result => (result.1.1.1,
      (({before.1.1 with beacons := RegistrationNativePublicOwners.pack selectedOwner publicPrekey result.1.1.2,environment := result.1.2},before.1.2),result.2))) <$>
      (simulateQ trusted (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run
        (before.1.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.1.environment)).run before.2 := by
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run]
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler,RegistrationNativePlatformSecretWordOrdinary.beacon,
    RegistrationNativePlatformPublicOwners.create,StateT.run,simulateQ_map,map_apply,Functor.map_map]
  have localSource := local_run implementation selectedOwner publicPrekey (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)
    before.1.1.beacons before.1.1.environment before.1.2 before.2
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))

include contract in
/-- Every actual new shared-platform creation outcome retains both rosters or appends exactly its same genuine private pair and returned handle. -/
theorem create_shape (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State source Platform Private) (result : RustM (Option Nat) × State source Platform Private)
    (supported : result ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    ((kem result.2.2).1.keys = (kem before.2).1.keys ∧ result.2.1.1.beacons.map key = before.1.1.beacons.map key) ∨
    ∃ pair, (kem result.2.2).1.keys = (kem before.2).1.keys ++ [pair] ∧
      result.2.1.1.beacons.map key = before.1.1.beacons.map key ++ [((kem before.2).1.keys.length,pair.1)] := by
  rw [create_run,support_map] at supported
  obtain ⟨reached,actual,equal⟩ := supported
  have shape := RegistrationNativePlatformLorSourceKemBirth.native_shape setup selected pairs publicKey challenge implementation kem input contract
    edPin mlPin keyId (before.1.1.beacons.map RegistrationNativePublicOwners.restore) before.1.1.environment before.2 reached actual
  cases equal
  rcases shape with same | ⟨pair,keys,owners⟩
  · exact Or.inl ⟨same.1,by rw [pack_keys,same.2,restore_keys]⟩
  · exact Or.inr ⟨pair,keys,by rw [pack_keys,owners,restore_keys]⟩

include contract in
/-- Literal source creation derives public-owner/private-row alignment while allowing equal public keys at different handles. -/
theorem aligned (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State source Platform Private) (result : RustM (Option Nat) × State source Platform Private)
    (prior : RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons (kem before.2).1.keys)
    (supported : result ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    RegistrationNativeSecretWordTargetAlignment.Aligned result.2.1.1.beacons (kem result.2.2).1.keys := by
  rcases create_shape implementation setup selectedOwner publicPrekey reserveFrame writer selected pairs publicKey challenge kem input contract
    edPin mlPin keyId before result supported with same | ⟨pair,keys,owners⟩
  · rw [same.1]
    exact RegistrationNativeSecretWordTargetAlignment.same _ _ _ prior same.2
  · rw [keys]
    exact RegistrationNativeSecretWordTargetAlignment.append _ _ _ pair prior owners

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.local_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.create_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.create_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate.aligned
