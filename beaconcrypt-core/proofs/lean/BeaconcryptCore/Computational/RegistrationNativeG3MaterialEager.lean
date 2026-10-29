-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3CellEager
import BeaconcryptCore.Computational.RegistrationNativeHiddenService
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform

/-! The actual public material44 reader forwards every fresh sampler through EnvEffects coins. This component completes that finite cache through arbitrary adaptive material/coin programs, retaining all other HiddenService fields and every World coordinate except the named coin-effect and uniform-draw counters. It changes neither seed caches nor role-use markers. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager
open PqxdhRecordLiftInterface (Slot EnvEffects)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeHiddenService (State coins material)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {Value : Type}

abbrev Spec (n : Nat) := RegistrationNativeG3CellEager.Spec (Slot n) Material

def put (before : State n) (cache : (Slot n →ₒ Material).QueryCache) : State n := { before with materials := cache }
def drop (before : State n) : State n := put before ∅

noncomputable def source : QueryImpl (Spec n) (StateT (State n) (OracleComp (EnvEffects n)))
  | .inl coin => StateT.lift (coins coin)
  | .inr slot => material slot

def worldView (before : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  RegistrationNativeKemWorldUniform.mask (RegistrationWorldCoinCompiler.eraseCoin before)

private theorem source_step (before : State n) (query : (Spec n).Domain)
    (cache : (Slot n →ₒ Material).QueryCache) :
    Prod.map id (put before) <$>
      ((coins.mapStateTBase RegistrationNativeG3CellEager.lazy) query).run cache =
        (source query).run (put before cache) := by
  cases query with
  | inl coin =>
      simp only [QueryImpl.mapStateTBase, RegistrationNativeG3CellEager.lazy, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run, StateT.lift, bind_pure_comp, source]
      rfl
  | inr slot =>
      change Prod.map id (put before) <$> simulateQ coins (((Slot n →ₒ Material).randomOracle slot).run cache) =
        (material slot).run (put before cache)
      cases found : cache slot with
      | some value =>
          rw [QueryImpl.withCaching_run_some _ found, simulateQ_pure, map_pure]
          exact (RegistrationNativeHiddenService.material_hit slot (put before cache) value found).symm
      | none =>
          rw [QueryImpl.withCaching_run_none _ found, simulateQ_map, Functor.map_map,
            RegistrationNativeHiddenService.material_miss slot (put before cache) found]
          rfl

/-- The actual HiddenService material/coin AST retains every nonmaterial field and exactly the reached lazy material cache. -/
theorem program_source (work : OracleComp (Spec n) Value) (before : State n) :
    (simulateQ source work).run before =
      Prod.map id (put before) <$>
        simulateQ coins ((simulateQ RegistrationNativeG3CellEager.lazy work).run before.materials) := by
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (coins.mapStateTBase RegistrationNativeG3CellEager.lazy) source (put before)
    (source_step before) work before.materials
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at projected
  exact projected.symm

/-- Forgetting only the private material cache leaves the exact original material/coin values and all other service fields. -/
theorem program_values (work : OracleComp (Spec n) Value) (before : State n) :
    Prod.map id drop <$> (simulateQ source work).run before =
      (fun value => (value, drop before)) <$>
        simulateQ coins (RegistrationNativeG3CellEager.lazyRun work before.materials) := by
  rw [program_source, RegistrationNativeG3CellEager.lazyRun, StateT.run'_eq, simulateQ_map, Functor.map_map,
    Functor.map_map]
  rfl

private theorem coins_world (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id worldView <$>
      (simulateQ PqxdhRecordLiftWorld.effects (simulateQ coins draw)).run before =
        (fun value => (value, worldView before)) <$> draw := by
  have erased := congrArg (fun distribution => Prod.map id RegistrationNativeKemWorldUniform.mask <$> distribution)
    (RegistrationWorldCoinCompiler.coins_erase draw before)
  have sampled := RegistrationNativeKemWorldUniform.sampled_mask draw (RegistrationWorldCoinCompiler.eraseCoin before)
  rw [RegistrationWorldCoinCompiler.sampled_erase] at erased
  convert erased.trans sampled using 1
  all_goals first | rfl | (simp only [Functor.map_map, Prod.map, id_eq]; rfl)

/-- The actual World coin interpreter retains every operational field, seed cache and role-use marker while the two named coin counters are omitted. -/
theorem world_values (work : OracleComp (Spec n) Value) (before : State n)
    (world : PqxdhRecordLiftWorld.State n) :
    Prod.map (Prod.map id drop) worldView <$>
      (simulateQ PqxdhRecordLiftWorld.effects ((simulateQ source work).run before)).run world =
      (fun value => ((value, drop before), worldView world)) <$>
        RegistrationNativeG3CellEager.lazyRun work before.materials := by
  have projected := congrArg (fun program =>
    Prod.map id worldView <$> (simulateQ PqxdhRecordLiftWorld.effects program).run world)
    (program_values work before)
  simp only [simulateQ_map, StateT.run_map, Functor.map_map] at projected
  have sampled := congrArg (fun distribution => (fun result => ((result.1, drop before), result.2)) <$> distribution)
    (coins_world (RegistrationNativeG3CellEager.lazyRun work before.materials) world)
  simp only [Functor.map_map, Prod.map, id_eq] at projected sampled ⊢
  exact projected.trans sampled

/-- The actual partial-cache public material reader has the completed material44 table law under its original environment coin forwarding. -/
theorem world_eager (work : OracleComp (Spec n) Value) (before : State n)
    (world : PqxdhRecordLiftWorld.State n) :
    LawEq
      (Prod.map (Prod.map id drop) worldView <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((simulateQ source work).run before)).run world)
      (do
        let table ← $ᵗ (Slot n → Material)
        (fun value => ((value, drop before), worldView world)) <$>
          RegistrationNativeG3CellEager.fixedRun (OracleComp.completeTable before.materials table) work) := by
  rw [world_values]
  have completed := (RegistrationNativeG3CellEager.cached_eager work before.materials).map
    (fun value => ((value, drop before), worldView world))
  simpa only [map_bind] using completed

end BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.program_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.program_values
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.world_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.world_values
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.world_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterialEager.world_eager
