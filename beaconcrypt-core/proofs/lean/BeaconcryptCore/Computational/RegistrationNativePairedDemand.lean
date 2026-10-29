-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativePairedServices

/-! The actual paired material service uses one persistent material table and the existing World seed table. It is invoked after native preflight; root preparation itself never invokes it. Every underlying material/seed draw goes through the World's uniform counter, and failed later publication cannot roll either table back. Only a slot and material leave the private interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedDemand
open RegistrationNativePairedServices (State MaterialSpec reserve)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material joinOutput splitOutput)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat}

/-- The only public material reply omits both generated chains. -/
structure Reference (n : Nat) where
  slot : Slot n
  material : Material

noncomputable def readMaterial (slot : Slot n) : StateT (State n) ProbComp Material := fun before => do
  let reached ← (PqxdhRecordLiftWorld.sampled
    ((PqxdhRecordLiftLazyTable.impl slot).run before.materials)).run before.world
  pure (reached.1.1, { before with materials := reached.1.2, world := reached.2 })

/-- This query uses the World's own private lazy table rather than a parallel seed cache. -/
noncomputable def readSeed (slot : Slot n) : StateT (State n) ProbComp PqxdhRecordLiftSeed.Seed := fun before => do
  let reached ← (PqxdhRecordLiftWorld.sampled
    ((PqxdhRecordLiftLazyTable.impl slot).run before.world.seeds)).run before.world
  pure (reached.1.1, { before with world := { reached.2 with seeds := reached.1.2 } })

/-- Full108 bytes are assembled only inside the private interpreter. -/
noncomputable def output (slot : Slot n) : StateT (State n) ProbComp PqxdhServerAuthKeySchedule.Output := do
  let material ← readMaterial slot
  let seed ← readSeed slot
  pure (joinOutput material seed)

/-- The explicit overflow branch performs no material or seed operation. -/
noncomputable def privateDemand (bytes : Pqxdh.Bytes) :
    StateT (State n) ProbComp (Option (Slot n × PqxdhServerAuthKeySchedule.Output)) := fun before =>
  let assigned := reserve bytes before
  match assigned.1 with
  | none => pure (none, assigned.2)
  | some slot => (fun reached => (some (slot, reached.1), reached.2)) <$> (output slot).run assigned.2

def publicReply : Option (Slot n × PqxdhServerAuthKeySchedule.Output) → Option (Reference n) :=
  Option.map fun value => ⟨value.1, (splitOutput value.2).1⟩

noncomputable def demand (bytes : Pqxdh.Bytes) : StateT (State n) ProbComp (Option (Reference n)) :=
  publicReply <$> privateDemand bytes

abbrev Spec (n : Nat) := Message →ₒ Option (Reference n)

/-- Selected secrets appear only in this private address realization. Literal aliases share the same executable demand. -/
noncomputable def implementation (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) : QueryImpl (Spec n) (StateT (State n) ProbComp) := fun message =>
  match RegistrationNativeRelatedFamily.input joint dh seed scalar message with
  | none => fun before => pure (none, { before with demands := before.demands + 1 })
  | some bytes => demand bytes

theorem implementation_rejected (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message)
    (invalid : RegistrationNativeRelatedFamily.input joint dh seed scalar message = none) (before : State n) :
    (implementation joint dh seed scalar message).run before =
      pure (none, { before with demands := before.demands + 1 }) := by
  simp only [implementation, invalid, StateT.run]

theorem implementation_alias (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (left right : Message)
    (same : RegistrationNativeRelatedFamily.input joint dh seed scalar left =
      RegistrationNativeRelatedFamily.input joint dh seed scalar right) :
    implementation (n := n) joint dh seed scalar left = implementation joint dh seed scalar right := by
  simp only [implementation, same]

/-- Capacity exhaustion is explicit and retains both complete tables and all native World state. -/
theorem demand_exhausted (bytes : Pqxdh.Bytes) (before : State n)
    (missing : before.slots bytes = none) (full : n ≤ before.next) :
    (demand bytes).run before = pure (none, { before with demands := before.demands + 1 }) := by
  unfold demand
  rw [StateT.run_map]
  simp only [privateDemand, StateT.run,
    RegistrationNativePairedServices.reserve_exhausted bytes before missing full, map_pure]
  rfl

/-- Reading private material retains all previous material values and every seed, cursor, binding and primitive cache cell. -/
theorem readMaterial_facts (slot : Slot n) (before : State n) (result : Material × State n)
    (supported : result ∈ support ((readMaterial slot).run before)) :
    result.2.materials.1 slot = some result.1 ∧ before.materials.1 ≤ result.2.materials.1 ∧
    result.2.world.seeds = before.world.seeds ∧ result.2.slots = before.slots ∧
    result.2.next = before.next ∧ result.2.demands = before.demands ∧
    result.2.world.primitive.2 = before.world.primitive.2 ∧
    result.2.world.server = before.world.server ∧ result.2.world.owners = before.world.owners := by
  simp only [readMaterial, PqxdhRecordLiftWorld.sampled, StateT.run,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run before.materials) := by
    rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run before.materials)
      before.world.primitive.1.uniform, support_map]
    exact ⟨inner, reached, rfl⟩
  have facts := PqxdhRecordLiftLazyTable.step_facts slot before.materials inner.1 original
  exact ⟨facts.1, facts.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading the private seed records its actual answer in the canonical World cache and cannot erase any prior seed or material. -/
theorem readSeed_facts (slot : Slot n) (before : State n) (result : PqxdhRecordLiftSeed.Seed × State n)
    (supported : result ∈ support ((readSeed slot).run before)) :
    result.2.world.seeds.1 slot = some result.1 ∧ before.world.seeds.1 ≤ result.2.world.seeds.1 ∧
    result.2.materials = before.materials ∧ result.2.slots = before.slots ∧
    result.2.next = before.next ∧ result.2.demands = before.demands ∧
    result.2.world.primitive.2 = before.world.primitive.2 ∧
    result.2.world.server = before.world.server ∧ result.2.world.owners = before.world.owners := by
  simp only [readSeed, PqxdhRecordLiftWorld.sampled, StateT.run,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run before.world.seeds) := by
    rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run before.world.seeds)
      before.world.primitive.1.uniform, support_map]
    exact ⟨inner, reached, rfl⟩
  have facts := PqxdhRecordLiftLazyTable.step_facts slot before.world.seeds inner.1 original
  exact ⟨facts.1, facts.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same actual canonical seed read supplies either role's complete World kernel. -/
theorem readSeed_resolve (role : PqxdhRecordLiftInterface.Role) (slot : Slot n) (before : State n) :
    (fun result => (PqxdhRecordLiftWorld.kernel role result.1, result.2.world)) <$>
      (readSeed slot).run before =
      (PqxdhRecordLiftWorld.resolve role (.hidden slot)).run before.world := by
  simp only [readSeed, PqxdhRecordLiftWorld.resolve, StateT.run,
    bind_pure_comp, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePairedDemand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.implementation_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.implementation_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.implementation_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.implementation_alias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.demand_exhausted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.demand_exhausted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.readMaterial_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.readMaterial_facts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.readSeed_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.readSeed_facts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDemand.readSeed_resolve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDemand.readSeed_resolve
