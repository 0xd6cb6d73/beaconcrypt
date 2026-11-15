-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemBirthCaps
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps
open RegistrationNativeKemCountedProgram (Spec)
variable {n : Nat} {I KemSK S A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Born : (Spec KemSK).Domain → Prop
  | .inr (.inl .create) => True
  | _ => False
instance (query : (Spec KemSK).Domain) : Decidable (Born query) := by
  cases query with
  | inl query => exact isFalse (fun h => h)
  | inr query => cases query with
    | inr query => exact isFalse (fun h => h)
    | inl query => cases query with
      | create => exact isTrue trivial
      | decapsulate handle ciphertext | reveal handle => exact isFalse (fun h => h)

def Bounded (cap : Nat) (work : StateT S (OracleComp (Spec KemSK)) A) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP Born cap

theorem simulate_bound {J : Type} {queries : OracleSpec J}
    (predicate : J → Prop) [DecidablePred predicate]
    (handler : QueryImpl queries (StateT S (OracleComp (Spec KemSK))))
    (steps : ∀ query, Bounded (if predicate query then 1 else 0) (handler query))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    Bounded cap (simulateQ handler work) := by
  intro before
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have total : (if predicate query then 1 else 0) + (if predicate query then cap - 1 else cap) = cap := by
        by_cases paid : predicate query
        · have positive := bounded.1.resolve_left (not_not_intro paid)
          simp only [paid, ite_true]
          omega
        · simp only [paid, ite_false, Nat.zero_add]
      simpa only [total] using isQueryBoundP_bind (steps query before)
        (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)

theorem ordinary_free (work : ProbComp A) :
    (RegistrationNativeKemCountedProgram.lift (KemSK := KemSK) work).IsQueryBoundP Born 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step
  · intro query paid
    exact False.elim paid
  · intro query unused
    simp [RegistrationNativeKemCountedProgram.ordinary, Born]

theorem liftState_free (work : StateT S ProbComp A) :
    Bounded 0 (RegistrationNativeKemCountedProgram.liftState (KemSK := KemSK) work) :=
  fun before => ordinary_free (work.run before)

theorem world_bound (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) A)
    (cap : Nat) (bounded : Bounded cap work) :
    Bounded cap (RegistrationNativeKemCountedTrusted.world (source := source) work) := by
  intro before
  change IsQueryBoundP ((fun result => (result.1, RegistrationNativeKemCountedTrusted.withWorld before result.2)) <$>
    work.run before.server.world.world.1) Born cap
  rw [isQueryBoundP_map_iff]
  exact bounded _

theorem call_bound (query : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Domain) :
    Bounded (if Born (KemSK := KemSK) (Sum.inr query : (Spec KemSK).Domain) then 1 else 0)
      (RegistrationNativeKemCountedProgram.call (n := n) query) := by
  intro before
  change IsQueryBoundP ((fun result => (result.1, RegistrationNativeMldsaCapability.advance .native before result.2)) <$>
    ((Spec KemSK).query (.inr query) : OracleComp (Spec KemSK) _)) Born _
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro paid
  rw [ite_eq_left paid]
  omega

theorem trusted_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Bounded (if RegistrationNativeBeaconKemBirthCaps.Born (n := n) (KemSK := KemSK) query then 1 else 0)
      (RegistrationNativeKemCountedTrusted.implementation (source := source) setup checks representation created query) := by
  cases query with
  | inl query => exact world_bound _ 0 (liftState_free _)
  | inr query => cases query with
    | inl query => exact liftState_free _
    | inr query => cases query with
      | inl query => cases query <;> exact world_bound _ _ (call_bound _)
      | inr key => exact world_bound _ _ (call_bound _)

theorem beacon_program (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (cap : Nat) (bounded : RegistrationNativeBeaconKemCaps.Bounded
      (RegistrationNativeBeaconKemBirthCaps.Born (n := n) (KemSK := KemSK)) cap work) :
    Bounded cap (RegistrationNativeKemCountedBeacon.program setup checks representation created work) := by
  intro before
  change IsQueryBoundP ((simulateQ (RegistrationNativeKemCountedTrusted.implementation setup checks representation created)
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before >>= fun result =>
    pure (result.1.1.1, { result.2 with beacons := result.1.1.2, server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })) Born cap
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact simulate_bound (RegistrationNativeBeaconKemBirthCaps.Born (n := n) (KemSK := KemSK)) _
    (trusted_bound setup checks representation created) _ cap
    (bounded before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before

theorem create_one (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded 1 (RegistrationNativeKemCountedBeacon.program (n := n) (source := source) setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)) :=
  beacon_program setup checks representation created _ 1
    (RegistrationNativeBeaconKemBirthCaps.create setup edPin mlPin keyId)
end BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.simulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.simulate_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.ordinary_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.liftState_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.liftState_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.world_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.world_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.call_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.trusted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.trusted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.beacon_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.create_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedBirthCaps.create_one
