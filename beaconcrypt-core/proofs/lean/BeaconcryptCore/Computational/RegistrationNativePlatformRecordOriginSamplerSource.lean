-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
/-! The actual whole record source splits at its reduction-owned physical sampler while preserving the complete encoded native client and actual reached private state. The cursor/control are rebound only after their equality is derived from sampler syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordOriginSamplerSource
open PqxdhServerAuthExperiment (Codec)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open PqxdhRecordLiftProtocol (ServiceSpec)
variable {n : Nat} {Reader Response Private A E Value : Type}
variable (service : QueryImpl (ServiceSpec n) (StateT Private ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation service codec route

private theorem program_source (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value)) (before : Private) :
    (simulateQ service (RegistrationNativeRecordOriginProgram.program codec route work)).run before=
    (fun result=>((RegistrationNativeRecordPackage.encode result.1.1.1,result.1.2),result.2)) <$>
      CborRawRecordOriginFlatten.interpret service codec route work
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl before := by
  simp only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
    CborRecordWorldClient.client,PqxdhRecordLiftProtocol.schedule,CborRawRecordOriginFlatten.interpret,
    simulateQ_map,StateT.run_map,Functor.map_map]

/-- Sampling stays inside the same physical service and the continuation resumes from its actual full private poststate. -/
theorem source (sample : ProbComp A) (next : A →OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (before : Private) :
    (simulateQ service (RegistrationNativeRecordOriginProgram.program codec route (simulateQ coinLift sample >>=next))).run before=
    (do
      let sampled←(simulateQ physical (simulateQ coinLift sample)).run
        (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,before))
      (simulateQ service (RegistrationNativeRecordOriginProgram.program codec route (next sampled.1))).run sampled.2.2.2) := by
  rw [program_source,CborRawRecordOriginFlatten.interpret_bind,map_bind,
    RegistrationNativePlatformLorIdealPhysical.program_source,bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro sampled called
  have exactSample : (sampled.1.1.1,(sampled.1.1.2,(sampled.1.2,sampled.2)))∈support
      ((simulateQ physical (simulateQ coinLift sample)).run
        (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,before))) := by
    rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map]
    exact ⟨sampled,called,rfl⟩
  have frame:=RegistrationNativePlatformRecordPartnerSampler.frame service codec route sample
    (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,before)) _ exactSample
  change sampled.1.1.2=CborRecordWorldClient.initial ∧sampled.1.2=PqxdhRecordLiftProtocol.initialControl at frame
  rw [program_source,frame.1,frame.2]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordOriginSamplerSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordOriginSamplerSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordOriginSamplerSource.source
