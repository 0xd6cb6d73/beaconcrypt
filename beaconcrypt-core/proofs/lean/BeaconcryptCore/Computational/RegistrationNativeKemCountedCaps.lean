-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame
import BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps
open RegistrationAgreementKemBounds (Kind counted)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativeKemServerState (State)
variable {n : Nat} {I KemSK S A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Counted (kind : Kind) := RegistrationNativeKemCallBounds.Counted (I := unifSpec.Domain) kind

def Bounded (kind : Kind) (cap : Nat) (work : StateT S (OracleComp (Spec KemSK)) A) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP (Counted kind) cap

theorem pure_bound (kind : Kind) (cap : Nat) (value : A) :
    Bounded kind cap (pure value : StateT S (OracleComp (Spec KemSK)) A) := fun _ => isQueryBoundP_pure _ _ _

theorem bind_bound (kind : Kind) (work : StateT S (OracleComp (Spec KemSK)) A)
    (next : A → StateT S (OracleComp (Spec KemSK)) B) (first later : Nat)
    (bounded : Bounded kind first work) (continued : ∀ value, Bounded kind later (next value)) :
    Bounded kind (first + later) (work >>= next) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => continued result.1 result.2)

theorem simulate_bound {J : Type} {queries : OracleSpec J}
    (kind : Kind) (predicate : J → Prop) [DecidablePred predicate]
    (handler : QueryImpl queries (StateT S (OracleComp (Spec KemSK))))
    (steps : ∀ query, Bounded kind (if predicate query then 1 else 0) (handler query))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    Bounded kind cap (simulateQ handler work) := by
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

theorem ordinary_free (kind : Kind) (work : ProbComp A) :
    (RegistrationNativeKemCountedProgram.lift (KemSK := KemSK) work).IsQueryBoundP (Counted kind) 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step
  · intro query paid
    exact False.elim paid
  · intro query unused
    cases kind <;> simp [RegistrationNativeKemCountedProgram.ordinary, Counted, RegistrationNativeKemCallBounds.Counted]

theorem liftState_free (kind : Kind) (work : StateT S ProbComp A) :
    Bounded kind 0 (RegistrationNativeKemCountedProgram.liftState (KemSK := KemSK) work) :=
  fun before => ordinary_free kind (work.run before)

theorem world_bound (kind : Kind) (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) A)
    (cap : Nat) (bounded : Bounded kind cap work) :
    Bounded kind cap (RegistrationNativeKemCountedTrusted.world (source := source) work) := by
  intro before
  change IsQueryBoundP ((fun result => (result.1, RegistrationNativeKemCountedTrusted.withWorld before result.2)) <$>
    work.run before.server.world.world.1) (Counted kind) cap
  rw [isQueryBoundP_map_iff]
  exact bounded _

theorem call_bound (kind : Kind) (query : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Domain) :
    Bounded kind (if Counted kind (Sum.inr query : (Spec KemSK).Domain) then 1 else 0)
      (RegistrationNativeKemCountedProgram.call (n := n) query) := by
  intro before
  change IsQueryBoundP ((fun result => (result.1, RegistrationNativeMldsaCapability.advance .native before result.2)) <$>
    ((Spec KemSK).query (.inr query) : OracleComp (Spec KemSK) _)) (Counted kind) _
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro paid
  rw [ite_eq_left paid]
  omega

theorem trusted_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Bounded kind (if RegistrationNativeBeaconKemCaps.NativeCounted kind query then 1 else 0)
      (RegistrationNativeKemCountedTrusted.implementation (source := source) setup checks representation created query) := by
  cases query with
  | inl query => exact world_bound kind _ 0 (liftState_free kind _)
  | inr query => cases query with
    | inl query =>
        change Bounded kind (if RegistrationNativeKemCallBounds.Counted kind (.inl query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) then 1 else 0) _
        have free : ¬ RegistrationNativeKemCallBounds.Counted kind (.inl query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) := by cases kind <;> exact not_false
        rw [ite_eq_right free]
        exact liftState_free kind _
    | inr query =>
        cases kind with
        | encapsulate =>
            cases query with
            | inl query => cases query <;> exact world_bound .encapsulate _ _ (call_bound .encapsulate _)
            | inr key => exact world_bound .encapsulate _ _ (call_bound .encapsulate _)
        | decapsulate =>
            cases query with
            | inl query => cases query <;> exact world_bound .decapsulate _ _ (call_bound .decapsulate _)
            | inr key => exact world_bound .decapsulate _ _ (call_bound .decapsulate _)

theorem primitive_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : RegistrationAgreementShared.PrimitiveRequest) :
    Bounded kind (if counted kind query.toRequest then 1 else 0)
      (RegistrationNativeKemCountedServerPrimitive.program (n := n) (source := source) setup checks representation created query) :=
  simulate_bound kind (RegistrationNativeKemCallBounds.Counted kind) _
    (fun request => trusted_bound kind setup checks representation created (.inr request)) _ _
    (RegistrationNativeKemCallBounds.server_step kind checks query)

theorem core_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : RegistrationAgreementExecutor.Request) :
    Bounded kind (if counted kind query then 1 else 0)
      (RegistrationNativeKemCountedServerPrimitive.core (n := n) (source := source) setup checks representation created query) := by
  cases query with
  | root request => exact pure_bound kind _ _
  | _ => exact primitive_bound kind setup checks representation created _

theorem agreement_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : RegistrationAgreementExecutor.Request) :
    Bounded kind (if counted kind query then 1 else 0)
      (RegistrationNativeKemCountedServerPrimitive.agreement (n := n) (source := source) setup checks representation created query) := by
  unfold RegistrationNativeKemCountedServerPrimitive.agreement
  intro before
  rw [StateT.run_bind, StateT.run_modify, pure_bind]
  exact core_bound kind setup checks representation created query _

theorem server_program (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : OracleComp RegistrationAgreementExecutor.Spec A)
    (cap : Nat) (bounded : work.IsQueryBoundP (counted kind) cap) :
    Bounded kind cap (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement (n := n) (source := source) setup checks representation created) work) :=
  simulate_bound kind (counted kind) _ (agreement_bound kind setup checks representation created) work cap bounded

theorem agree_one (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (authenticated : registration.AuthenticatedInit) :
    Bounded kind 1 (RegistrationNativeKemCountedServerPrimitive.agree (n := n) (source := source) setup checks representation created authenticated) := by
  unfold RegistrationNativeKemCountedServerPrimitive.agree
  apply bind_bound kind _ _ 0 1
  · intro before
    change IsQueryBoundP (pure (before, before)) (Counted kind) 0
    trivial
  · intro before
    apply server_program kind setup checks representation created _ 1
    rw [RegistrationReplaySchedule.begin_eq]
    split
    · trivial
    · exact RegistrationAgreementKemBounds.server kind before.server.control .Fresh authenticated
theorem beacon_program (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (cap : Nat) (bounded : RegistrationNativeBeaconKemCaps.Bounded
      (RegistrationNativeBeaconKemCaps.NativeCounted kind) cap work) :
    Bounded kind cap (RegistrationNativeKemCountedBeacon.program setup checks representation created work) := by
  intro before
  change IsQueryBoundP ((simulateQ (RegistrationNativeKemCountedTrusted.implementation setup checks representation created)
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before >>= fun result =>
    pure (result.1.1.1, { result.2 with beacons := result.1.1.2, server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } }))
    (Counted kind) cap
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact simulate_bound kind (RegistrationNativeBeaconKemCaps.NativeCounted kind) _
    (trusted_bound kind setup checks representation created) _ cap
    (bounded before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before

theorem finish_one (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded kind 1 (RegistrationNativeKemCountedBeacon.program (n := n) (source := source) setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)) :=
  beacon_program kind setup checks representation created _ 1
    (RegistrationNativeBeaconKemFrame.finish kind setup wire index packet)

end BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.pure_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.simulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.simulate_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.ordinary_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.liftState_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.liftState_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.world_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.world_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.call_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.call_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.trusted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.trusted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.core_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.core_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.server_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.agree_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.agree_one

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.beacon_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.finish_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedCaps.finish_one
