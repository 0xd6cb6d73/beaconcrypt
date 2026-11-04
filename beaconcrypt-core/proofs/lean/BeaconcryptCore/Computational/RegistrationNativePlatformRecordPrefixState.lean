-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceReachedView
/-! An explicit sampler prefix keeps the public cursor and Protocol control fixed while retaining the actual private coin state. Its accounting is separate from the native runtime budget. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Secret Reader Response A : Type}

def coins (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) :
    QueryImpl unifSpec (StateT Secret ProbComp) := fun query => do
  let _ ← service (.charge .coin)
  service (.coin query)

/-- Every prefix coin is interpreted on the actual private state without changing public control. -/
theorem sample (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : ProbComp A) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    CborRawRecordOriginFlatten.interpret service codec route (simulateQ PqxdhRecordLiftInterface.coinLift work) shell control secret =
      (fun result => (((result.1,shell),control),result.2)) <$> (simulateQ (coins service) work).run secret := by
  induction work using OracleComp.inductionOn generalizing secret with
  | pure value => simp only [simulateQ_pure,CborRawRecordOriginFlatten.interpret_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,CborRawRecordOriginFlatten.interpret_bind]
    have leaf : CborRawRecordOriginFlatten.interpret service codec route (PqxdhRecordLiftInterface.coinLift query) shell control secret =
        (fun result => (((result.1,shell),control),result.2)) <$> (coins service query).run secret := by
      have shellLeaf : (CborRecordWorldClient.handler (n := n) (.inr (.inl (.inl query)))).run shell =
          (fun value => (value,shell)) <$> ((PqxdhRecordLiftInterface.WorldSpec n).query (.inr (.inl (.inl query))) : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (unifSpec.Range query)) := rfl
      have protocolLeaf : (PqxdhRecordLiftProtocol.handler codec.frameRead route (.inr (.inl (.inl query)))).run control =
          (do let _ ← ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.charge .coin) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Unit)
              let value ← ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.coin query) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) (unifSpec.Range query))
              pure (value,control)) := rfl
      simp only [PqxdhRecordLiftInterface.coinLift,CborRawRecordOriginFlatten.interpret,simulateQ_spec_query,
        shellLeaf,simulateQ_map,StateT.run_map,protocolLeaf,simulateQ_bind,
        StateT.run_bind,map_bind,bind_pure_comp,Functor.map_map,coins]
    rw [leaf]
    simp only [bind_map_left,StateT.run_bind,map_bind]
    apply bind_congr
    intro result
    exact ih result.1 result.2
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefixState.sample
