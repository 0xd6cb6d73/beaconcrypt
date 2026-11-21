-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld
/-! The literal shell, protocol control and reached private record interpreter form one persistent World dictionary. Its adaptive program equality is only exact state reassociation and applies to any real or ideal record service, retaining all refused calls and failed histories. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Reader Response Secret A : Type}
abbrev State (n : Nat) (Secret : Type) := CborRecordWorldClient.Shell × (PqxdhRecordLiftProtocol.Control n × Secret)
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
noncomputable def implementation : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT (State n Secret) ProbComp) :=
  fun query before => (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
    CborRawRecordOriginFlatten.interpret service codec route ((PqxdhRecordLiftInterface.WorldSpec n).query query) before.1 before.2.1 before.2.2

private theorem query_run (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) (before : State n Secret) :
    (implementation service codec route query).run before =
      (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
        CborRawRecordOriginFlatten.interpret service codec route ((PqxdhRecordLiftInterface.WorldSpec n).query query) before.1 before.2.1 before.2.2 := rfl

theorem program_source (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A) (before : State n Secret) :
    (simulateQ (implementation service codec route) work).run before =
      (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
        CborRawRecordOriginFlatten.interpret service codec route work before.1 before.2.1 before.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,CborRawRecordOriginFlatten.interpret_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,query_run,
      CborRawRecordOriginFlatten.interpret_bind,bind_map_left,map_bind]
    apply bind_congr
    rintro ⟨⟨⟨reply,shell⟩,control⟩,secret⟩
    exact ih reply (shell,(control,secret))
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical.program_source
