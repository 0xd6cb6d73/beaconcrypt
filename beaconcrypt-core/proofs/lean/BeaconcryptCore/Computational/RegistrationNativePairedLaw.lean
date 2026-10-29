-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedDemand
import BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit

/-! The private native material/seed reads project to the existing split lazy service. This establishes the byte-distribution bridge through arbitrary adaptive slot clients; it does not replace the separate related-root or key-schedule primitive hops. The projection forgets instrumentation and unrelated World fields only for this table theorem. Native continuation/installation receipts retain those fields separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedLaw
open RegistrationNativePairedServices (State MaterialSpec)
open RegistrationNativePairedDemand (readMaterial readSeed output)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open LazyOracleDiscard (StateLens LawEq)
variable {n : Nat}

abbrev Caches (n : Nat) := (MaterialSpec n).QueryCache × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache

def project (state : State n) : Caches n := (state.materials.1, state.world.seeds.1)

inductive Request (n : Nat) where
  | material : Slot n → Request n
  | seed : Slot n → Request n

abbrev Spec (n : Nat) : OracleSpec (Request n)
  | .material _ => Material
  | .seed _ => PqxdhRecordLiftSeed.Seed

noncomputable def implementation : QueryImpl (Spec n) (StateT (State n) ProbComp)
  | .material slot => readMaterial slot
  | .seed slot => readSeed slot

noncomputable def reference : QueryImpl (Spec n) (StateT (Caches n) ProbComp)
  | .material slot => (StateLens.fst _ _).query (spec := MaterialSpec n) slot
  | .seed slot => (StateLens.snd _ _).query (spec := PqxdhRecordLiftWorld.SeedSpec n) slot

theorem material_project (slot : Slot n) (before : State n) :
    Prod.map id project <$> (readMaterial slot).run before =
      (reference (.material slot)).run (project before) := by
  have counted := congrArg (fun work => (fun result : Material × PqxdhRecordLiftLazyTable.State (MaterialSpec n) =>
    (result.1, (result.2.1, before.world.seeds.1))) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget
      ((PqxdhRecordLiftLazyTable.impl slot).run before.materials) before.world.primitive.1.uniform)
  have cached := congrArg (fun work => (fun result : Material × (MaterialSpec n).QueryCache =>
    (result.1, (result.2, before.world.seeds.1))) <$> work)
    (LazyOracleDiscard.impl_project slot before.materials)
  calc
    _ = (fun result : Material × PqxdhRecordLiftLazyTable.State (MaterialSpec n) =>
        (result.1, (result.2.1, before.world.seeds.1))) <$>
          (PqxdhRecordLiftLazyTable.impl slot).run before.materials := by
      simpa only [readMaterial, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, Prod.map, id_eq, project] using counted
    _ = _ := by
      simpa only [Functor.map_map, Prod.map, id_eq, reference, StateLens.query,
        StateLens.lift, StateLens.fst, StateT.run, project] using cached

theorem seed_project (slot : Slot n) (before : State n) :
    Prod.map id project <$> (readSeed slot).run before =
      (reference (.seed slot)).run (project before) := by
  have counted := congrArg (fun work => (fun result : PqxdhRecordLiftSeed.Seed ×
      PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n) =>
    (result.1, (before.materials.1, result.2.1))) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget
      ((PqxdhRecordLiftLazyTable.impl slot).run before.world.seeds) before.world.primitive.1.uniform)
  have cached := congrArg (fun work => (fun result : PqxdhRecordLiftSeed.Seed ×
      (PqxdhRecordLiftWorld.SeedSpec n).QueryCache =>
    (result.1, (before.materials.1, result.2))) <$> work)
    (LazyOracleDiscard.impl_project slot before.world.seeds)
  calc
    _ = (fun result : PqxdhRecordLiftSeed.Seed ×
        PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n) =>
        (result.1, (before.materials.1, result.2.1))) <$>
          (PqxdhRecordLiftLazyTable.impl slot).run before.world.seeds := by
      simpa only [readSeed, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, Prod.map, id_eq, project] using counted
    _ = _ := by
      simpa only [Functor.map_map, Prod.map, id_eq, reference, StateLens.query,
        StateLens.lift, StateLens.snd, StateT.run, project] using cached

theorem query_project (query : (Spec n).Domain) (before : State n) :
    Prod.map id project <$> (implementation query).run before =
      (reference query).run (project before) := by
  cases query with
  | material slot => exact material_project slot before
  | seed slot => exact seed_project slot before

/-- The full108 private service uses exactly the existing two-cache split service, including repeat hits. -/
theorem output_project (slot : Slot n) (before : State n) :
    Prod.map id project <$> (output slot).run before =
      (PqxdhDeploymentSeedSplit.splitService slot).run (project before) := by
  let work : OracleComp (Spec n) PqxdhServerAuthKeySchedule.Output := do
    let material ← (Spec n).query (.material slot)
    let seed ← (Spec n).query (.seed slot)
    pure (PqxdhDeploymentHiddenLayout.joinOutput material seed)
  simpa only [work, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    implementation, reference, output, PqxdhDeploymentSeedSplit.splitService] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation reference project query_project work before

def Coherent (state : State n) : Prop := PqxdhDeploymentSeedSplit.BothOrNeither (project state)

def joined (state : State n) : (PqxdhDeploymentSeedSplit.OutputSpec n).QueryCache :=
  PqxdhDeploymentSeedSplit.joinTable (project state)

/-- Fresh source initialization has no hidden seed, so the material and seed caches start coherent. -/
theorem initial_coherent (world : PqxdhRecordLiftWorld.State n)
    (empty : world.seeds.1 = ∅) :
    Coherent (RegistrationNativePairedServices.initial world) := by
  intro slot
  simp only [project, RegistrationNativePairedServices.initial, PqxdhRecordLiftLazyTable.initial, empty]
  rfl

/-- Every completed material/seed service call preserves coherence, including repeats. -/
theorem output_coherent (slot : Slot n) (before : State n) (coherent : Coherent before)
    (result : PqxdhServerAuthKeySchedule.Output × State n)
    (supported : result ∈ support ((output slot).run before)) : Coherent result.2 := by
  have projected : (result.1, project result.2) ∈ support
      ((PqxdhDeploymentSeedSplit.splitService slot).run (project before)) := by
    rw [← output_project slot before, support_map]
    exact ⟨result, supported, rfl⟩
  exact (PqxdhDeploymentSeedSplit.split_service_proj slot (project before) coherent).2 _ projected

/-- A private108 read has the law of the complete uniform lazy output table under the actual two-cache invariant. -/
theorem output_law (slot : Slot n) (before : State n) (coherent : Coherent before) :
    LawEq (Prod.map id joined <$> (output slot).run before)
      ((PqxdhDeploymentSeedSplit.lazyService slot).run (joined before)) := by
  have exactStep := congrArg (fun work => Prod.map id PqxdhDeploymentSeedSplit.joinTable <$> work)
    (output_project slot before)
  have first : LawEq (Prod.map id joined <$> (output slot).run before)
      (Prod.map id PqxdhDeploymentSeedSplit.joinTable <$>
        (PqxdhDeploymentSeedSplit.splitService slot).run (project before)) := by
    apply LawEq.of_eq
    change (fun result : PqxdhServerAuthKeySchedule.Output × State n =>
      (result.1, PqxdhDeploymentSeedSplit.joinTable (project result.2))) <$>
      (output slot).run before = _
    simpa only [Functor.map_map, Prod.map, id_eq] using exactStep
  exact first.trans (PqxdhDeploymentSeedSplit.split_service_proj slot (project before) coherent).1

/-- Arbitrarily adaptive slot clients use the persistent uniform108 table, with no supplied naturality or table-alias equality premise. -/
theorem program_law {Value : Type} (work : OracleComp (PqxdhDeploymentSeedSplit.OutputSpec n) Value)
    (before : State n) (coherent : Coherent before) :
    LawEq (Prod.map id joined <$> (simulateQ output work).run before)
      ((simulateQ PqxdhDeploymentSeedSplit.lazyService work).run (joined before)) :=
  PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj output PqxdhDeploymentSeedSplit.lazyService
    Coherent joined output_law output_coherent work before coherent

end BeaconcryptCore.Computational.RegistrationNativePairedLaw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.material_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.material_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.seed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.seed_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.initial_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.initial_coherent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_coherent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.output_law
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedLaw.program_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedLaw.program_law
