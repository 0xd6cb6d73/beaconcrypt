-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-! Named ML generation and signing calls retain their complete source optional reply under count normalization inside the full native World lens. Only the explicitly named accounting view is applied; no primitive output or generated-key ownership law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaMainView (project)
open RegistrationNativeMldsaCountRules (Correct)
variable {source : RegistrationNativeMldsa.Source} {n : Nat} {KemSK : Type}

def setWorld (before : RegistrationNativeExperiment.State n KemSK source) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeExperiment.State n KemSK source :=
  { before with server := { before.server with world := { before.server.world with world := (world, before.server.world.world.2) } } }

private theorem project_set (before : RegistrationNativeExperiment.State n KemSK source) (world : PqxdhRecordLiftWorld.State n) :
    project (setWorld before world) = setWorld (project before) (RegistrationNativeMldsaWorldView.project world) := rfl

private theorem advance (before : RegistrationNativeExperiment.State n KemSK source)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (count : Nat) :
    project (setWorld before (RegistrationNativeMldsaCapability.advance accounting before.server.world.world.1 count)) = project before := by
  rw [project_set, RegistrationNativeMldsaWorldView.advance]
  rfl

private theorem original (before : RegistrationNativeExperiment.State n KemSK source)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (query : RegistrationNativeMldsaCapability.Request source) :
    Prod.map id project <$>
      (RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call accounting query)).run before =
        (fun result => (result.1, project before)) <$>
          (liftM ((Spec source).query (.inr query)) : OracleComp (Spec source) (RegistrationNativeMldsaCapability.Reply query × Nat)) := by
  change Prod.map id project <$>
    ((fun result => (result.1, setWorld before result.2)) <$>
      (RegistrationNativeMldsaProgram.call accounting query).run before.server.world.world.1) = _
  simp only [RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, advance]
  rfl

private theorem normalized (before : RegistrationNativeExperiment.State n KemSK source)
    (accounting : RegistrationNativeMldsaCapability.Accounting) (query : RegistrationNativeMldsaCapability.Request source) :
    Prod.map id project <$>
      transform ((RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call accounting query)).run before) =
        (fun result => (result.1, project before)) <$>
          (liftM ((Spec source).query (.inr query)) : OracleComp (Spec source) (RegistrationNativeMldsaCapability.Reply query × Nat)) := by
  change Prod.map id project <$>
    transform ((fun result => (result.1, setWorld before result.2)) <$>
      (RegistrationNativeMldsaProgram.call accounting query).run before.server.world.world.1) = _
  simp only [RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp,
    transform, simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaCountMap.translation,
    Functor.map_map, Prod.map, id_eq, advance]
  rfl

/-- Every named ML operation satisfies both source continuation laws inside the complete native World lens. -/
theorem call (accounting : RegistrationNativeMldsaCapability.Accounting)
    (query : RegistrationNativeMldsaCapability.Request source) :
    Correct (project (n := n) (KemSK := KemSK))
      (RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call accounting query)) := by
  constructor
  · intro before
    rw [original, original, RegistrationNativeMldsaMainView.idempotent]
  · intro before
    rw [normalized, original, RegistrationNativeMldsaMainView.idempotent]
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountNative.call
