-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap
import BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual Server authentication World callback is lifted into the same complete Native/platform state through the existing World field. This lens retains role journals, owners, the private KEM pool and the parsed-attempt counter. Its monad equations derive whole authentication interpretation from individual callbacks. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerWorldLens
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK A B : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

def world (work : WorldM A) : NativeM A := fun before =>
  (fun result => (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
    work.run before.server.world.world.1

omit [LawfulMonad m] in
theorem world_run (work : WorldM A) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (world work).run before = (fun result => (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
      work.run before.server.world.world.1 := rfl

theorem pure_world (value : A) : world (n := n) (KemSK := KemSK) (mlSource := mlSource) (pure value : WorldM A) = pure value := by
  apply StateT.ext
  intro before
  rw [world_run, StateT.run_pure, StateT.run_pure, map_pure]
  rfl

theorem bind_world (work : WorldM A) (next : A → WorldM B) :
    world (KemSK := KemSK) (mlSource := mlSource) (work >>= next) = (world work >>= fun value => world (next value)) := by
  apply StateT.ext
  intro before
  rw [world_run, StateT.run_bind, StateT.run_bind]
  simp only [world_run, map_bind, bind_map_left]
  rfl

theorem simulate_world {I : Type} {spec : OracleSpec I} (handler : QueryImpl spec WorldM)
    (work : OracleComp spec A) :
    world (KemSK := KemSK) (mlSource := mlSource) (simulateQ handler work) =
      simulateQ (fun query => world (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_world]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_world]
    apply bind_congr
    exact ih

end BeaconcryptCore.Refinement.AdapterPublicServerWorldLens

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.world_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.world_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.pure_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.pure_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.bind_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.bind_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.simulate_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerWorldLens.simulate_world
