-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection
open PqxdhDeploymentInterface (FullSpec FreshBounds)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformOriginFreeFullTrace (Inner State)
noncomputable local instance (p : Prop) : Decidable p:=Classical.propDecidable p
variable {n : Nat} {Platform Failure Reader Response Private View : Type}
def forget (before : (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private) :
    PqxdhDeploymentSecrecy.Ledger × (Inner n Platform × Private) := (before.1.1.1,(before.1.1.2,before.2))
variable (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : FreshBounds)
    (service : QueryImpl (ServiceSpec n) (StateT Private ProbComp)) (observe : State n Platform→View)
local notation "front"=>RegistrationNativeObservedStageTrace.handler observe
  (RegistrationNativePlatformOriginFreeFullTrace.frontend env reserve crypto codec route serverKeyId bounds)
local notation "closed"=>QueryImpl.Stateful.link front service
local notation "target"=>RegistrationNativePlatformGatedRecordFlat.full service env reserve crypto codec route serverKeyId bounds
/-- Dropping only the public-source analysis journal reassociates every actual callback with the same gated native/full-ledger callback and reached private state. -/
theorem query (request : FullSpec.Domain)
    (before : (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private) :
    Prod.map id forget <$> (closed request).run before=(target request).run (forget before) := by
  have projected:=congrArg (Functor.map (Prod.map id forget))
    (RegistrationNativePlatformOriginFreeFullTrace.observed_program env reserve crypto codec route serverKeyId bounds service
      observe (FullSpec.query request) (forget before,before.1.2))
  simp only [simulateQ_spec_query,Functor.map_map] at projected
  simp only [RegistrationNativeObservedStageTrace.handler,StateT.run,Functor.map_map,Prod.map,id_eq,
    RegistrationNativePlatformOriginFreeFullTrace.observedAssociate,RegistrationNativePlatformOriginFreeFullTrace.journalAssociate,
    RegistrationNativePlatformOriginFreeFullTrace.associate,forget] at projected
  change id <$> (target request).run (forget before)=Prod.map id forget <$> (closed request).run before at projected
  rw [id_map] at projected
  exact projected.symm
/-- The actual full source path is preserved while dropping only the private callback journal. -/
theorem path {before after : (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private}
    {calls : List (RegistrationNativeStageTrace.Call FullSpec ((State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private))}
    (actual : RegistrationNativeStageTrace.Path closed before calls after) :
    RegistrationNativeStageTrace.Path target (forget before)
      (calls.map (RegistrationNativeObservedStageTrace.mapCall forget)) (forget after) :=
  RegistrationNativePlatformOriginCallbackChronology.project_path closed target forget
    (query env reserve crypto codec route serverKeyId bounds service observe) actual
/-- Every bounded-statistic execution supplies one complete gated native source chronology whose counted filter is exactly the bounded journal. -/
theorem tracked {A : Type} (counted : FullSpec.Domain→Prop) (work : OracleComp FullSpec A)
    (before : (State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) × Private)
    (result : RegistrationNativePlatformOriginCallbackTrace.Result FullSpec _ A)
    (supported : result∈support (RegistrationNativePlatformOriginCallbackTrace.track counted closed work before)) :
    ∃calls,RegistrationNativeStageTrace.Path closed before calls result.2.2 ∧
      RegistrationNativeStageTrace.Path target (forget before)
        (calls.map (RegistrationNativeObservedStageTrace.mapCall forget)) (forget result.2.2) ∧
      calls.filter (fun current=>decide (counted current.query))=result.1 := by
  obtain ⟨calls,actual,filtered⟩:=RegistrationNativePlatformOriginCallbackChronology.path counted closed work before result supported
  exact ⟨calls,actual,path env reserve crypto codec route serverKeyId bounds service observe actual,filtered⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginTrackedProjection.tracked
