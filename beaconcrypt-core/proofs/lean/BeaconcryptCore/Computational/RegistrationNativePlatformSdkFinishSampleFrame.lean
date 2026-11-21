-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformSdkFinishSampling (sample)
variable {n : Nat} {KemSK A B : Type}

 theorem map (observe : A → B) (work : ProbComp A) (before : Backend n KemSK) :
    (sample (observe <$>work)).run before = Prod.map observe id <$> (sample work).run before := by
  change (fun result : B × PqxdhRecordLiftWorld.State n => (result.1,{before with world:=result.2})) <$>
    (PqxdhRecordLiftWorld.sampled (observe <$>work)).run before.world =
    Prod.map observe id <$> ((fun result : A × PqxdhRecordLiftWorld.State n => (result.1,{before with world:=result.2})) <$>
      (PqxdhRecordLiftWorld.sampled work).run before.world)
  rw [RegistrationAgreementSampledState.sampled_map,Functor.map_map,Functor.map_map]
  rfl

 theorem frame (work : ProbComp A) (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (result : A × Backend n KemSK) (supported : result∈support ((sample work).run before)) :
    result.2.pool=before.pool ∧result.2.auxiliary=before.auxiliary ∧worldBackend result.2.world=result.2.world := by
  change result∈support ((fun inner : A × PqxdhRecordLiftWorld.State n => (inner.1,{before with world:=inner.2})) <$>
    (PqxdhRecordLiftWorld.sampled work).run before.world) at supported
  rw [support_map] at supported
  obtain ⟨middle,called,returned⟩:=supported
  subst result
  refine ⟨rfl,rfl,?_⟩
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp] at called
  rw [support_map] at called
  obtain ⟨raw,_reached,same⟩:=called
  subst middle
  have owners : before.world.owners=[] := (congrArg PqxdhRecordLiftWorld.State.owners canonical).symm
  have admin : Function.update before.world.primitive.1.effects .administrative 0=before.world.primitive.1.effects :=
    congrArg (fun world=>world.primitive.1.effects) canonical
  simp only [worldBackend,admin]
  rw [owners]

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame.frame
