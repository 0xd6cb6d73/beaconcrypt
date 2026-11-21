-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementMonadMap
import BeaconcryptCore.Computational.RegistrationNativeExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The literal existing Native World lens is a lawful monad interpretation. Lifting actual source Rust computations through it preserves all enclosing failures and the complete owner, pool, parsed-attempt and Server metadata outside World. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicAgreementMonadMap
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK A B : Type} {source : RegistrationNativeMldsa.Source}
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) ProbComp
local notation "NativeM" => RegistrationNativeExperiment.M n KemSK source

def putWorld (before : RegistrationNativeExperiment.State n KemSK source) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeExperiment.State n KemSK source :=
  { before with server := { before.server with world := { before.server.world with world := (world, before.server.world.world.2) } } }

theorem world_run (work : WorldM A) (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.world work).run before =
      (fun result => (result.1, putWorld before result.2)) <$> work.run before.server.world.world.1 := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run, Functor.map_map]
  rfl

theorem world_pure (value : A) :
    RegistrationNativeExperiment.world (n := n) (KemSK := KemSK) (mlSource := source) (pure value) = pure value := by
  funext before
  change (RegistrationNativeExperiment.world (pure value : WorldM A)).run before = (pure value : NativeM A).run before
  rw [world_run, StateT.run_pure, StateT.run_pure, map_pure]
  rfl

theorem world_bind (work : WorldM A) (next : A → WorldM B) :
    RegistrationNativeExperiment.world (KemSK := KemSK) (mlSource := source) (work >>= next) =
      (RegistrationNativeExperiment.world work >>= fun value => RegistrationNativeExperiment.world (next value)) := by
  funext before
  change (RegistrationNativeExperiment.world (work >>= next)).run before =
    ((RegistrationNativeExperiment.world work >>= fun value => RegistrationNativeExperiment.world (next value)) : NativeM B).run before
  rw [world_run, StateT.run_bind, StateT.run_bind]
  simp only [world_run, map_bind, bind_map_left]
  rfl

noncomputable def transform (work : RustT WorldM A) : RustT NativeM A :=
  ⟨RegistrationNativeExperiment.world work.run⟩

theorem transform_pure (value : A) : transform (n := n) (KemSK := KemSK) (source := source) (pure value) = pure value := by
  apply RustT.ext
  exact world_pure (RustM.ok value)

theorem transform_liftRust (result : RustM A) :
    transform (n := n) (KemSK := KemSK) (source := source) (AdapterRecordRequestMonad.liftRust result) = AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  exact world_pure result

theorem transform_bind (work : RustT WorldM A) (next : A → RustT WorldM B) :
    transform (KemSK := KemSK) (source := source) (work >>= next) =
      (transform work >>= fun value => transform (next value)) := by
  apply RustT.ext
  change RegistrationNativeExperiment.world ((work >>= next).run) = _
  rw [RustT.run_bind, world_bind]
  change (RegistrationNativeExperiment.world work.run >>= fun reply =>
    RegistrationNativeExperiment.world (match reply with
      | .ok value => (next value).run
      | .fail error => pure (.fail error)
      | .div => pure .div)) = _
  rw [RustT.run_bind]
  apply bind_congr
  intro reply
  cases reply <;> rfl

@[instance_reducible] noncomputable def translation : Transformation WorldM NativeM where
  transform := transform
  lawful := Cslib.IsMonadHom.mk' transform_pure transform_bind
  lift := transform_liftRust
end BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_liftRust' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_liftRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.transform_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap.world_run
