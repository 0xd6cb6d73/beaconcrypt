-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps
open RegistrationNativeKemResourceFootprint (Kind)
open RegistrationNativeKemCountedProgram (Spec)
variable {n : Nat} {I KemSK S A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Counted : Kind → (Spec KemSK).Domain → Prop
  | .birth => RegistrationNativeKemCountedBirthCaps.Born
  | .encapsulate => RegistrationNativeKemCountedCaps.Counted .encapsulate
  | .decapsulate => RegistrationNativeKemCountedCaps.Counted .decapsulate
instance (kind : Kind) : DecidablePred (Counted (KemSK := KemSK) kind) := by
  cases kind <;> unfold Counted <;> exact inferInstance

abbrev NativeCounted : Kind → (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain → Prop
  | .birth => RegistrationNativeBeaconKemBirthCaps.Born
  | .encapsulate => RegistrationNativeBeaconKemCaps.NativeCounted .encapsulate
  | .decapsulate => RegistrationNativeBeaconKemCaps.NativeCounted .decapsulate
instance (kind : Kind) : DecidablePred (NativeCounted (n := n) (KemSK := KemSK) kind) := by
  cases kind <;> unfold NativeCounted <;> exact inferInstance

theorem native_counted_eq (kind : Kind) : NativeCounted (n := n) (KemSK := KemSK) kind = RegistrationNativeKemResourceFootprint.counted kind := by
  funext query
  cases query with
  | inl query => cases kind <;> rfl
  | inr query => cases query with
    | inl query => cases kind <;> rfl
    | inr query => cases query with
      | inr key => cases kind <;> simp [NativeCounted, RegistrationNativeBeaconKemBirthCaps.Born, RegistrationNativeBeaconKemCaps.NativeCounted, RegistrationNativeKemCallBounds.Counted, RegistrationNativeKemResourceFootprint.counted]
      | inl query => cases query <;> cases kind <;> simp [NativeCounted, RegistrationNativeBeaconKemBirthCaps.Born, RegistrationNativeBeaconKemCaps.NativeCounted, RegistrationNativeKemCallBounds.Counted, RegistrationNativeKemResourceFootprint.counted]

abbrev Bounded (kind : Kind) (cap : Nat) (work : StateT S (OracleComp (Spec KemSK)) A) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP (Counted kind) cap

theorem pure_bound (kind : Kind) (cap : Nat) (value : A) : Bounded kind cap (pure value : StateT S (OracleComp (Spec KemSK)) A) := fun _ => isQueryBoundP_pure _ _ _
theorem bind_bound (kind : Kind) (work : StateT S (OracleComp (Spec KemSK)) A) (next : A → StateT S (OracleComp (Spec KemSK)) B) (first later : Nat)
    (bounded : Bounded kind first work) (continued : ∀ value, Bounded kind later (next value)) : Bounded kind (first + later) (work >>= next) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => continued result.1 result.2)

theorem simulate_bound {J : Type} {queries : OracleSpec J}
    (kind : Kind) (predicate : J → Prop) [DecidablePred predicate]
    (handler : QueryImpl queries (StateT S (OracleComp (Spec KemSK))))
    (steps : ∀ query, Bounded kind (if predicate query then 1 else 0) (handler query))
    (work : OracleComp queries A) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    Bounded kind cap (simulateQ handler work) := by
  cases kind with
  | birth => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedBirthCaps.simulate_bound predicate handler (by simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using steps) work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)
  | encapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.simulate_bound .encapsulate predicate handler (by simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using steps) work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)
  | decapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.simulate_bound .decapsulate predicate handler (by simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using steps) work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)

theorem liftState_free (kind : Kind) (work : StateT S ProbComp A) :
    Bounded kind 0 (RegistrationNativeKemCountedProgram.liftState (KemSK := KemSK) work) := by
  cases kind with
  | birth => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedBirthCaps.liftState_free work
  | encapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.liftState_free .encapsulate work
  | decapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.liftState_free .decapsulate work

theorem trusted_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Bounded kind (if NativeCounted kind query then 1 else 0)
      (RegistrationNativeKemCountedTrusted.implementation (source := source) setup checks representation created query) := by
  cases kind with
  | birth => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedBirthCaps.trusted_bound setup checks representation created query
  | encapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.trusted_bound .encapsulate setup checks representation created query
  | decapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.trusted_bound .decapsulate setup checks representation created query

theorem beacon_program (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (cap : Nat) (bounded : RegistrationNativeBeaconKemCaps.Bounded (NativeCounted kind) cap work) :
    Bounded kind cap (RegistrationNativeKemCountedBeacon.program setup checks representation created work) := by
  cases kind with
  | birth => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedBirthCaps.beacon_program setup checks representation created work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)
  | encapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.beacon_program .encapsulate setup checks representation created work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)
  | decapsulate => simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded] using RegistrationNativeKemCountedCaps.beacon_program .decapsulate setup checks representation created work cap (by simpa only [NativeCounted, RegistrationNativeBeaconKemCaps.Bounded] using bounded)

theorem create (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded kind (if kind = .birth then 1 else 0)
      (RegistrationNativeKemCountedBeacon.program (n := n) (source := source) setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)) := by
  apply beacon_program kind setup checks representation created
  simpa only [RegistrationNativeBeaconKemCaps.Bounded, native_counted_eq, RegistrationNativeKemResourceFootprint.Bounded] using
    RegistrationNativeKemResourceFootprint.create_bound (n := n) (Auxiliary := RegistrationServerRoleBackend.State) (source := source) setup kind edPin mlPin keyId

theorem finish (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded kind (if kind = .decapsulate then 1 else 0)
      (RegistrationNativeKemCountedBeacon.program (n := n) (source := source) setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)) := by
  by_cases charged : kind = .decapsulate
  · subst kind
    simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded, ite_true] using RegistrationNativeKemCountedCaps.finish_one (n := n) (source := source) .decapsulate setup checks representation created wire index packet
  · rw [ite_eq_right charged]
    apply beacon_program kind setup checks representation created
    simpa only [RegistrationNativeBeaconKemCaps.Bounded, native_counted_eq, RegistrationNativeKemResourceFootprint.Bounded] using
      RegistrationNativeKemResourceFootprint.finish_zero (n := n) (Auxiliary := RegistrationServerRoleBackend.State) (source := source) setup kind charged wire index packet

theorem server_lower_zero (kind : Kind) (quiet : kind ≠ .encapsulate)
    (checks : PqxdhServerAuthExperiment.Checks) (query : RegistrationAgreementShared.PrimitiveRequest) :
    (RegistrationNativeKemInterface.server (KemSK := KemSK) checks query).IsQueryBoundP
      (fun request => NativeCounted (n := n) (KemSK := KemSK) kind (.inr request)) 0 := by
  cases query with
  | convertPublic key | convertSecret role | generate role | dh request =>
      cases kind <;> simp [RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other,
        NativeCounted, RegistrationNativeBeaconKemBirthCaps.Born, RegistrationNativeBeaconKemCaps.NativeCounted,
        RegistrationNativeKemCallBounds.Counted, isQueryBoundP_query_iff]
  | decapsulate ciphertext => simp [RegistrationNativeKemInterface.server]
  | encapsulate key =>
      cases key with
      | none => simp [RegistrationNativeKemInterface.server]
      | some key =>
          cases kind with
          | encapsulate => exact False.elim (quiet rfl)
          | birth | decapsulate =>
              simp only [RegistrationNativeKemInterface.server]
              split <;> simp [RegistrationNativeKemInterface.encapsulate,
                NativeCounted, RegistrationNativeBeaconKemBirthCaps.Born, RegistrationNativeBeaconKemCaps.NativeCounted,
                RegistrationNativeKemCallBounds.Counted, isQueryBoundP_query_iff]

theorem server_primitive_zero (kind : Kind) (quiet : kind ≠ .encapsulate)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : RegistrationAgreementShared.PrimitiveRequest) :
    Bounded kind 0 (RegistrationNativeKemCountedServerPrimitive.program (n := n) (source := source) setup checks representation created query) :=
  simulate_bound kind (fun request => NativeCounted kind (.inr request)) _
    (fun request => trusted_bound kind setup checks representation created (.inr request)) _ 0
    (server_lower_zero kind quiet checks query)

theorem server_core_zero (kind : Kind) (quiet : kind ≠ .encapsulate)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : RegistrationAgreementExecutor.Request) :
    Bounded kind 0 (RegistrationNativeKemCountedServerPrimitive.core (n := n) (source := source) setup checks representation created query) := by
  cases query with
  | root request => exact pure_bound kind 0 _
  | _ => exact server_primitive_zero kind quiet setup checks representation created _

theorem server_agreement_zero (kind : Kind) (quiet : kind ≠ .encapsulate)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : RegistrationAgreementExecutor.Request) :
    Bounded kind 0 (RegistrationNativeKemCountedServerPrimitive.agreement (n := n) (source := source) setup checks representation created query) := by
  intro before
  rw [RegistrationNativeKemCountedServerPrimitive.agreement, StateT.run_bind, StateT.run_modify, pure_bind]
  exact server_core_zero kind quiet setup checks representation created query _

theorem agree (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (authenticated : registration.AuthenticatedInit) :
    Bounded kind (if kind = .encapsulate then 1 else 0)
      (RegistrationNativeKemCountedServerPrimitive.agree (n := n) (source := source) setup checks representation created authenticated) := by
  by_cases charged : kind = .encapsulate
  · subst kind
    simpa only [Bounded, Counted, NativeCounted, RegistrationNativeKemCountedCaps.Bounded, RegistrationNativeKemCountedBirthCaps.Bounded, RegistrationNativeBeaconKemCaps.Bounded, ite_true] using RegistrationNativeKemCountedCaps.agree_one (n := n) (source := source) .encapsulate setup checks representation created authenticated
  · rw [ite_eq_right charged]
    unfold RegistrationNativeKemCountedServerPrimitive.agree
    apply bind_bound kind _ _ 0 0
    · intro before
      change IsQueryBoundP (pure (before, before)) (Counted kind) 0
      trivial
    · intro before
      exact simulate_bound kind (fun _ => False) _
        (fun request => server_agreement_zero kind charged setup checks representation created request)
        _ 0 (isQueryBoundP_false _ 0)

end BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.native_counted_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.native_counted_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.pure_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.simulate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.simulate_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.liftState_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.liftState_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.trusted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.trusted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.beacon_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_lower_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_lower_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_primitive_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_primitive_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_core_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_core_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_agreement_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.server_agreement_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps.agree
