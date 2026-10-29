-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService

/-! The selective service preserves the actual hidden-slot allocator and its demand count while its extra nonselected108-byte cache changes. All branches, including failed preparation and overflow, charge exactly one demand. The nonselected cache can invoke only literal probability coins, so it cannot allocate an owner, inspect a hidden seed or install any kernel. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant
open RegistrationNativeSelectiveHiddenService (State known demand onHidden)
open RegistrationNativeHiddenServiceInvariant (Ordered InjectiveSlots)
open RegistrationNativeHiddenServiceBounds (IsCapability)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat}
attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot uniformSample

/-- A nonselected full-output read retains every selected service field and records its literal output persistently. -/
theorem known_fields (bytes : Pqxdh.Bytes) (before after : State n) (value : PqxdhServerAuthKeySchedule.Output)
    (supported : (value, after) ∈ support ((known bytes).run before)) :
    after.1 = before.1 ∧ after.2 bytes = some value := by
  cases found : before.2 bytes with
  | some output =>
      rw [RegistrationNativeSelectiveHiddenService.known_hit bytes before output found, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, found⟩
  | none =>
      rw [RegistrationNativeSelectiveHiddenService.known_miss bytes before found, support_map] at supported
      obtain ⟨output, _sampled, equal⟩ := supported
      cases equal
      exact ⟨rfl, QueryCache.cacheQuery_self _ _ _⟩

private theorem old_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (ordered : Ordered before.1) (injective : InjectiveSlots before.1)
    (supported : (reply, after) ∈ support
      ((onHidden (RegistrationNativeHiddenService.demand source input inside message)).run before)) :
    after.1.demands = before.1.demands + 1 ∧ Ordered after.1 ∧ InjectiveSlots after.1 := by
  simp only [onHidden, StateT.run, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  cases equal
  exact RegistrationNativeHiddenServiceDemand.demand_keeps source input inside message before.1 reached.2 reached.1 ordered injective possible

/-- The actual selective demand preserves the allocator invariants and charges once across every hidden, known and failure branch. -/
theorem demand_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before after : State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (ordered : Ordered before.1) (injective : InjectiveSlots before.1)
    (supported : (reply, after) ∈ support ((demand source input inside candidate message).run before)) :
    after.1.demands = before.1.demands + 1 ∧ Ordered after.1 ∧ InjectiveSlots after.1 := by
  simp only [demand, StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none =>
        simp only [realized] at supported
        exact old_demand source input _ message before after reply ordered injective supported
    | some bytes =>
        simp only [realized] at supported
        split at supported
        · simp only [support_map] at supported
          obtain ⟨reached, possible, equal⟩ := supported
          cases equal
          have fields := known_fields bytes ({ before.1 with demands := before.1.demands + 1 }, before.2) reached.2 reached.1 possible
          rw [fields.1]
          have counts : before.1.next ≤ before.1.demands := ordered.2.1
          exact ⟨rfl, ⟨ordered.1, by dsimp only; omega, ordered.2.2⟩, injective⟩
        · exact old_demand source input _ message before after reply ordered injective supported
  · exact old_demand source input _ message before after reply ordered injective supported

/-- Locally owned nonselected108-byte sampling has no World capability at all. -/
theorem known_free (bytes : Pqxdh.Bytes) (before : State n) :
    ((known bytes).run before).IsQueryBoundP IsCapability 0 := by
  cases found : before.2 bytes with
  | some output => rw [RegistrationNativeSelectiveHiddenService.known_hit bytes before output found]; trivial
  | none =>
      rw [RegistrationNativeSelectiveHiddenService.known_miss bytes before found, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      intro query
      simp [RegistrationNativeHiddenService.coins, IsCapability, isQueryBoundP_query_iff]

/-- Selective demand cannot access World state; actual installation remains in the later native continuation. -/
theorem demand_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) (before : State n) :
    ((demand source input inside candidate message).run before).IsQueryBoundP IsCapability 0 := by
  simp only [demand, StateT.run]
  split
  · cases realized : input message with
    | none =>
        simp only []
        exact (isQueryBoundP_map_iff _ _ _).mpr (RegistrationNativeHiddenServiceBounds.demand_free source input _ message before.1)
    | some bytes =>
        simp only []
        split
        · rw [isQueryBoundP_map_iff]
          exact known_free bytes _
        · exact (isQueryBoundP_map_iff _ _ _).mpr (RegistrationNativeHiddenServiceBounds.demand_free source input _ message before.1)
  · exact (isQueryBoundP_map_iff _ _ _).mpr (RegistrationNativeHiddenServiceBounds.demand_free source input _ message before.1)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.known_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.known_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.demand_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.demand_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.known_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.known_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.demand_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant.demand_free
