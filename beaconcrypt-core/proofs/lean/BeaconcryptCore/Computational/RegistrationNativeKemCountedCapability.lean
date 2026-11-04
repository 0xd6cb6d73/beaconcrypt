-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCapability
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! Private indexed KEM capabilities retain the actual complete pool and the exact number of underlying source uniform draws. The client receives only the original leaf reply and its private accounting receipt. No uniform counter is masked, no key-byte injectivity is required, and optional invalid-handle decapsulation is preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability
open PqxdhKemIndCca (MlKemScheme)
open PqxdhLiveKemBirth (Pool PoolSpec)
open RegistrationNativeKemInterface (EncapsulationSpec)
variable {ι KemSK V : Type} {base : OracleSpec ι} {n : Nat}

abbrev LeafSpec (KemSK : Type) := PoolSpec KemSK + EncapsulationSpec
abbrev Spec (KemSK : Type) : OracleSpec (LeafSpec KemSK).Domain :=
  fun query => (LeafSpec KemSK).Range query × Nat

noncomputable def draw (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) :
    QueryImpl (LeafSpec KemSK) (StateT (Pool KemSK) ProbComp)
  | .inl query => PqxdhLiveKemBirth.poolImpl baseImpl kem query
  | .inr key => StateT.lift (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key))

/-- The actual private service counts precisely the original source leaf, including invalid-handle and optional failure paths. -/
noncomputable def actual (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) :
    QueryImpl (Spec KemSK) (StateT (Pool KemSK) ProbComp) := fun query before =>
  (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ PqxdhRecordLiftWorld.countCoin ((draw baseImpl kem query).run before)).run 0

/-- Erasing only the private cost receipt returns the exact original leaf reply and complete private pool. -/
theorem actual_forget (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (query : (LeafSpec KemSK).Domain) (before : Pool KemSK) :
    (fun result => (result.1.1, result.2)) <$> (actual baseImpl kem query).run before = (draw baseImpl kem query).run before := by
  have law := PqxdhRecordLiftWorld.countCoin_forget ((draw baseImpl kem query).run before) 0
  simpa only [actual, StateT.run, Functor.map_map] using law

/-- Restoring the private count retains the literal full reached World and complete indexed pool, without a counter projection. -/
theorem actual_native (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (query : (LeafSpec KemSK).Domain) (pool : Pool KemSK) (world : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1.1, (RegistrationNativeMldsaCapability.advance .native world result.1.2, result.2))) <$>
        (actual baseImpl kem query).run pool =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (PqxdhRecordLiftWorld.sampled ((draw baseImpl kem query).run pool)).run world := by
  have law := congrArg (fun distribution => (fun result => (result.1.1, (result.2, result.1.2))) <$> distribution)
    (RegistrationNativeMldsaCapability.native_count ((draw baseImpl kem query).run pool) world)
  simpa only [actual, StateT.run, Functor.map_map] using law

end BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability.actual_forget' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability.actual_forget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability.actual_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCapability.actual_native
