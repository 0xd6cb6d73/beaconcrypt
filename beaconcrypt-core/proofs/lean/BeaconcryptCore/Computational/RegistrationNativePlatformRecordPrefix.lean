-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordAccounting
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBills
/-! Reduction-owned sampling is an explicit World prefix. Its separately charged coins are removed only by the named accounting view when comparing original record events; actual record callbacks and their failed produced frames remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open PqxdhRecordLiftWorld (State)
open RegistrationNativePlatformPublicWorldObservation (recordView)
open RegistrationNativeG3MetricWorld (mask)
variable {n : Nat} {I KemSK Reader Response A B E Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The independent sampler changes only the explicitly erased accounting fields. -/
theorem sample_source (sample : ProbComp A) (before : State n) :
    Prod.map id mask <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
      (simulateQ coinLift sample)).run before = (fun value => (value,mask before)) <$> sample := by
  have same : simulateQ (CborRecordWorldSimulation.guarded (n := n) setup codec route) (simulateQ coinLift sample) =
      simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin sample) := by
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
  rw [same]
  exact RegistrationNativeG3MetricWorld.sampled_source sample before

/-- A complete original record observation keeps the same reduction sampler and actual continuation, despite its extra accounting charge. -/
theorem observed_source (sample : ProbComp A) (next : A → OracleComp (WorldSpec n) B) (before : State n) :
    (fun result => (result.1,recordView result.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route) ((simulateQ coinLift sample) >>= next)).run before =
      (sample >>= fun value => (fun result => (result.1,recordView result.2)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route) (next value)).run before) := by
  let continuation := fun (result : A × State n) =>
    (fun answer => (answer.1,recordView answer.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route) (next result.1)).run result.2
  have sampled := congrArg (fun distribution => distribution >>= continuation) (sample_source setup codec route sample before)
  simp only [bind_map_left, continuation, Prod.map_def,id_eq] at sampled
  simp only [simulateQ_bind,StateT.run_bind,map_bind]
  calc _ = (do let result ← (simulateQ (CborRecordWorldSimulation.guarded setup codec route) (simulateQ coinLift sample)).run before
               (fun answer => (answer.1,recordView answer.2)) <$>
                 (simulateQ (CborRecordWorldSimulation.guarded setup codec route) (next result.1)).run (mask result.2)) := by
             apply bind_congr
             intro result
             exact RegistrationNativePlatformG3RecordAccounting.program_input setup codec route _ result.2
       _ = _ := by
         rw [sampled]
         apply bind_congr
         intro value
         exact (RegistrationNativePlatformG3RecordAccounting.program_input setup codec route _ before).symm

/-- The all-real original result/produced/raw event is one complete client containing the reduction's actual sampling prefix. -/
theorem real_source (sample : ProbComp A)
    (next : A → OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (observe : RegistrationNativeEntropyRun.Outcome E Value →
      List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool) :
    (fun result => observe result.result result.produced result.raw) <$>
      RegistrationNativeRecordViewCrypto.real setup codec route ((simulateQ coinLift sample) >>= next) =
      (sample >>= fun value => (fun result => observe result.result result.produced result.raw) <$>
        RegistrationNativeRecordViewCrypto.real setup codec route (next value)) := by
  rw [RegistrationNativePlatformRecordPackageSource.real_source]
  have source := congrArg (Functor.map (fun result => observe result.1 result.2.2.1 result.2.2.2))
    (observed_source setup codec route sample next PqxdhRecordLiftWorld.initial)
  simpa only [Functor.map_map,map_bind,recordView,RegistrationNativePlatformRecordPackageSource.real_source] using source
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.sample_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPrefix.real_source
