-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInterpreter

/-! Ordinary native World/KEM/signing operations do not inspect the separate retained-root memo. These concrete frame laws move that private memo into the root service without changing any other World, pool, receipt, callback or counter field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicRootFrame
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State world effect publication common kem routedKem)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def replace (memo : RegistrationNativeReferenceInterpreter.State) (state : State n KemSK) : State n KemSK :=
  { state with roots := memo }

/-- Actual World operations never read the private root memo, and retain every other state/counter literally. -/
theorem world_replace (memo : RegistrationNativeReferenceInterpreter.State)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) (before : State n KemSK) :
    Prod.map id (replace memo) <$> (world work).run before = (world work).run (replace memo before) := by
  simp only [world, StateT.run, replace, Functor.map_map, Prod.map, id_eq]

/-- Arbitrary actual environment-effect programs satisfy the same root-memo frame law. -/
theorem effects_replace (memo : RegistrationNativeReferenceInterpreter.State)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK) :
    Prod.map id (replace memo) <$> (simulateQ effect work).run before =
      (simulateQ effect work).run (replace memo before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (replace memo)
    (fun _ state => world_replace memo _ state) work before

/-- The actual signing component reads only its chronological receipt field, leaving the separate root memo opaque. -/
theorem publication_replace (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK) :
    Prod.map id (replace memo) <$> (publication setup wire sign query).run before =
      (publication setup wire sign query).run (replace memo before) := by
  simp only [publication, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp]
  rw [← effects_replace memo _ before]
  simp only [Functor.map_map, replace, Prod.map, id_eq]

/-- Public and private indexed KEM operations keep the root memo separate from their actual pool and World effects. -/
theorem kem_replace (setup : Setup base KemSK) (memo : RegistrationNativeReferenceInterpreter.State)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : State n KemSK) :
    Prod.map id (replace memo) <$> (kem setup query).run before =
      (kem setup query).run (replace memo before) := by
  cases query with
  | inl query =>
      simp only [kem, StateT.run_lift, bind_pure_comp, Functor.map_map, replace, Prod.map, id_eq]
  | inr query => cases query with
    | inl query =>
        simp only [kem, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_map,
          StateT.run_modify, map_pure, bind_pure_comp]
        rw [← world_replace memo _ before]
        simp only [Functor.map_map, replace, Prod.map, id_eq]
    | inr key => exact world_replace memo _ before

/-- Both actual real encapsulation routes preserve the same private-root frame. -/
theorem routed_replace (setup : Setup base KemSK) (memo : RegistrationNativeReferenceInterpreter.State)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : State n KemSK) :
    Prod.map id (replace memo) <$> (routedKem setup query).run before =
      (routedKem setup query).run (replace memo before) := by
  rcases query with (query | key) | query
  · exact kem_replace setup memo (.inl query) before
  · exact kem_replace setup memo (.inr (.inr key)) before
  · exact kem_replace setup memo (.inr query) before

/-- The complete paired native common service is independent of the separate private root memo. -/
theorem common_replace (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    Prod.map id (replace memo) <$> (common setup wire sign query).run before =
      (common setup wire sign query).run (replace memo before) := by
  cases query with
  | inl query => exact publication_replace setup wire sign memo query before
  | inr query => exact world_replace memo _ before

def IsRoot : RegistrationNativeRelatedRoot.RootSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsRoot := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr _ => exact isTrue trivial

/-- Actual local World computations forward only their original uniform draws through the root interface. -/
theorem world_free (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) (before : State n KemSK) :
    ((world work).run before).IsQueryBoundP IsRoot 0 := by
  simp only [world, StateT.run, isQueryBoundP_map_iff]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) IsRoot _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativePublicInterpreter.coins, IsRoot, isQueryBoundP_query_iff]

/-- Entire environment-effect components issue no root/sign/public-HMAC callback. -/
theorem effects_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK) :
    ((simulateQ effect work).run before).IsQueryBoundP IsRoot 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    contradiction
  · intro query _ current
    exact world_free _ current

/-- The actual MD/raw publication component cannot reach a root callback through a local primitive. -/
theorem publication_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n KemSK) :
    ((publication setup wire sign query).run before).IsQueryBoundP IsRoot 0 := by
  simp only [publication, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_map,
    StateT.run_modify, map_pure, bind_pure_comp, isQueryBoundP_map_iff]
  exact effects_free _ before

/-- Actual generated-key pool and encapsulation programs use only their uniform draws. -/
theorem kem_free (setup : Setup base KemSK)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : State n KemSK) : ((kem setup query).run before).IsQueryBoundP IsRoot 0 := by
  cases query with
  | inl query =>
      simp only [kem, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) IsRoot _ 0 (isQueryBoundP_false _ 0)
      intro coin
      simp [RegistrationNativePublicInterpreter.coins, IsRoot, isQueryBoundP_query_iff]
  | inr query => cases query with
    | inl query =>
        simp only [kem, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_map,
          StateT.run_modify, map_pure, bind_pure_comp, isQueryBoundP_map_iff]
        exact world_free _ before
    | inr key => exact world_free _ before

/-- Ordinary and selected public getters keep the same zero-root-query footprint. -/
theorem routed_free (setup : Setup base KemSK)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : State n KemSK) :
    ((routedKem setup query).run before).IsQueryBoundP IsRoot 0 := by
  rcases query with (query | key) | query
  · exact kem_free setup (.inl query) before
  · exact kem_free setup (.inr (.inr key)) before
  · exact kem_free setup (.inr query) before

/-- The complete common service cannot execute a root, signature-root or public-HMAC query. -/
theorem common_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (before : State n KemSK) :
    ((common setup wire sign query).run before).IsQueryBoundP IsRoot 0 := by
  cases query with
  | inl query => exact publication_free setup wire sign query before
  | inr query => exact world_free _ before

/-- Concrete root-field commutation implies that reached ordinary operations retain the original memo exactly. -/
theorem roots_kept (work : RegistrationNativePublicInterpreter.M n KemSK Value)
    (framed : ∀ memo before, Prod.map id (replace memo) <$> work.run before = work.run (replace memo before))
    (before : State n KemSK) (result : Value × State n KemSK)
    (reached : result ∈ support (work.run before)) : result.2.roots = before.roots := by
  have same := framed before.roots before
  have restored : replace before.roots before = before := rfl
  rw [restored] at same
  rw [← same, support_map] at reached
  obtain ⟨inner, _possible, equal⟩ := reached
  exact (congrArg (fun value : Value × State n KemSK => value.2.roots) equal).symm

end BeaconcryptCore.Computational.RegistrationNativePublicRootFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.world_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.world_replace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.effects_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.effects_replace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.publication_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.publication_replace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.kem_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.kem_replace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.routed_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.routed_replace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.common_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.common_replace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.world_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.world_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.effects_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.effects_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.publication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.publication_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.roots_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.roots_kept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.kem_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.kem_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.routed_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.routed_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.common_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootFrame.common_free
