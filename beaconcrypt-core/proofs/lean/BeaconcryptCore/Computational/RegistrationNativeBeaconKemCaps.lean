-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCallBounds
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds
/-! KEM algorithm-call budgets hold in the actual full Native Beacon owner/Env state stack before primitive interpretation. Ordinary world/uniform callbacks cost zero KEM calls; an indexed KEM leaf pays only its reached selected call. The literal agreement journal adds no KEM call. Complete adaptive request programs retain all returned values and both poststates; no uniform-counter or state projection is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationAgreementKemBounds (Kind counted)
open RegistrationNativeKemCallBounds (Counted)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def NativeCounted (kind : Kind) : (Trusted n KemSK).Domain → Prop
  | .inl _ => False
  | .inr query => Counted kind query

instance (kind : Kind) (query : (Trusted n KemSK).Domain) : Decidable (NativeCounted kind query) := by
  cases query with
  | inl query => exact isFalse (fun impossible => impossible)
  | inr query => exact inferInstanceAs (Decidable (Counted kind query))

def Bounded (predicate : (Trusted n KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (work : M n KemSK source Auxiliary A) : Prop :=
  ∀ owners env, ((work.run owners).run env).IsQueryBoundP predicate cap

theorem pure_bound (predicate : (Trusted n KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (value : A) : Bounded predicate cap (pure value : M n KemSK source Auxiliary A) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

theorem bind_bound (predicate : (Trusted n KemSK).Domain → Prop) [DecidablePred predicate]
    (work : M n KemSK source Auxiliary A) (next : A → M n KemSK source Auxiliary B)
    (first later : Nat) (bounded : Bounded predicate first work)
    (continued : ∀ value, Bounded predicate later (next value)) :
    Bounded predicate (first + later) (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded owners env) (fun result _ => continued result.1.1 result.1.2 result.2)

theorem effect_free (kind : Kind) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) := by
  intro owners env
  change IsQueryBoundP ((fun reply => ((reply, owners), env)) <$>
    ((Trusted n KemSK).query (.inl query) : OracleComp (Trusted n KemSK) _)) (NativeCounted kind) 0
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  exact False.elim

theorem sample_free (kind : Kind) (work : ProbComp A) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  intro owners env
  apply RegistrationNativePlatformQueryBounds.simulate_bound (fun _ => False) (NativeCounted kind)
    (fun query => RegistrationNativeBeaconFrontend.effect (.inl query)) _ work 0 (isQueryBoundP_false work 0) owners env
  intro query current previous
  exact effect_free kind (.inl query) current previous

theorem kem_bound (kind : Kind) (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Bounded (NativeCounted kind) (if Counted kind query then 1 else 0)
      (RegistrationNativeBeaconFrontend.kem (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) query) := by
  intro owners env
  change IsQueryBoundP ((fun reply => ((reply, owners), env)) <$>
    ((Trusted n KemSK).query (.inr query) : OracleComp (Trusted n KemSK) _)) (NativeCounted kind)
      (if Counted kind query then 1 else 0)
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  change Counted kind query → 0 < (if Counted kind query then 1 else 0)
  intro called
  rw [ite_eq_left called]
  omega

theorem primitive_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveRequest) :
    Bounded (NativeCounted kind) (if counted kind query.toRequest then 1 else 0)
      (RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  intro owners env
  unfold RegistrationNativeBeaconFrontend.primitive
  apply RegistrationNativePlatformQueryBounds.simulate_bound (Counted kind) (NativeCounted kind) _ _ _ _
    (RegistrationNativeKemCallBounds.beacon_step kind (some owner.kemHandle) query) owners env
  intro lower current previous
  cases lower with
  | inl other =>
      change IsQueryBoundP
        (((RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary)
          (Prod.fst <$> (RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar other).run
            ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩)).run current).run previous)
        (NativeCounted kind)
        (if Counted kind (Sum.inl other : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) then 1 else 0)
      have free : ¬ Counted kind (Sum.inl other : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) := by
        cases kind <;> exact not_false
      simpa only [free, ite_false] using sample_free kind
        (Prod.fst <$> (RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar other).run
          ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩) current previous
  | inr other => exact kem_bound kind (.inr other) current previous

theorem core_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Bounded (NativeCounted kind) (if counted kind query then 1 else 0)
      (RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  cases query with
  | convertPublic key => exact primitive_bound kind setup owner oneTime (.convertPublic key)
  | convertSecret role => exact primitive_bound kind setup owner oneTime (.convertSecret role)
  | generate role => exact primitive_bound kind setup owner oneTime (.generate role)
  | encapsulate key => exact primitive_bound kind setup owner oneTime (.encapsulate key)
  | decapsulate ciphertext => exact primitive_bound kind setup owner oneTime (.decapsulate ciphertext)
  | dh request => exact primitive_bound kind setup owner oneTime (.dh request)
  | root request => exact pure_bound _ _ _

theorem agreement_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Bounded (NativeCounted kind) (if counted kind query then 1 else 0)
      (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  have metadataFree : Bounded (NativeCounted kind) 0
      (RegistrationNativeBeaconFrontend.updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary)
        (fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query })) := by
    intro owners env
    change IsQueryBoundP (pure (((), owners), {env with requests := env.requests ++ RegistrationWorldAgreement.recorded query})) (NativeCounted kind) 0
    trivial
  simpa only [Nat.zero_add] using bind_bound (NativeCounted kind) _ _ 0
    (if counted kind query then 1 else 0) metadataFree (fun _ => core_bound kind setup owner oneTime query)

theorem program_bound (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (counted kind) cap) :
    Bounded (NativeCounted kind) cap
      (simulateQ (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime) work) := by
  intro owners env
  exact RegistrationNativePlatformQueryBounds.simulate_bound (counted kind) (NativeCounted kind) _
    (agreement_bound kind setup owner oneTime) work cap bounded owners env

theorem beacon_one (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Bounded (NativeCounted kind) 1
      (simulateQ (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)) :=
  program_bound kind setup owner oneTime _ 1 (RegistrationAgreementKemBounds.beacon kind authenticated)
end BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.effect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.effect_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.sample_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.sample_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.kem_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.core_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.core_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.beacon_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps.beacon_one
