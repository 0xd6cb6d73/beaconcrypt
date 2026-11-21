-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendPath
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalPath (Path Prefix cutAt)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {Platform Failure A : Type}
variable (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) A)
    (beforeP : Platform) (tag : PqxdhDeploymentInterface.FrameTag)

def source : OracleComp (ServiceSpec n) A := do
  let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
  let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
  continued reserve after beforeP tag reply

/-- The literal envelope's own execution path exposes its same lookup, seal reply, and completed publication/reserve suffix. -/
theorem split (before : CtxPrivate n) (past : List (Label n)) (result : Result n A)
    (path : Path service (source reserve pending after beforeP tag) before past result) :
    ∃ (looked : Unit × CtxPrivate n) (sealed : Option RawCtxSourceSend.Encrypted × CtxPrivate n) (later : List (Cut n A)),
      looked∈support ((service (.lookup pending.material)).run before) ∧
      sealed∈support ((service (.sealing pending)).run looked.2) ∧
      Path service (continued reserve after beforeP tag sealed.1) sealed.2 (past++[pending.material]) (later,result.2) ∧
      result.1=⟨pending,continued reserve after beforeP tag,looked.2,past⟩::later := by
  obtain ⟨looked,lookupCalled,afterLookup,sealPath,sameLookup⟩ :=
    PqxdhRecordFactsOriginOrdinalPath.path_query service (.lookup pending.material) _ before past result path
  simp only [cutAt,PqxdhRecordLiftWorldProvenance.sealingCoordinates,List.nil_append,List.append_nil] at sealPath sameLookup
  obtain ⟨sealed,sealCalled,tail,tailPath,sameTail⟩ :=
    PqxdhRecordFactsOriginOrdinalPath.path_query service (.sealing pending) _ looked.2 past afterLookup sealPath
  refine ⟨looked,sealed,tail.1,lookupCalled,sealCalled,?_,?_⟩
  · simpa only [sameLookup,sameTail,cutAt,List.singleton_append,PqxdhRecordLiftWorldProvenance.sealingCoordinates,Prod.mk.eta] using tailPath
  · simp only [sameLookup,sameTail,cutAt,List.singleton_append]

/-- The same path reaches the actual envelope seal before its optional reply, without selecting a different supported macro execution. -/
theorem reached (before : CtxPrivate n) (past : List (Label n)) (result : Result n A)
    (path : Path service (source reserve pending after beforeP tag) before past result) :
    ∃looked,
      Prefix service (source reserve pending after beforeP tag) before past
        (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>= continued reserve after beforeP tag)
        looked.2 past [] ∧
      looked∈support ((service (.lookup pending.material)).run before) := by
  obtain ⟨looked,lookupCalled,afterLookup,sealPath,sameLookup⟩ :=
    PqxdhRecordFactsOriginOrdinalPath.path_query service (.lookup pending.material) _ before past result path
  refine ⟨looked,?_,lookupCalled⟩
  simpa only [source,cutAt,PqxdhRecordLiftWorldProvenance.sealingCoordinates,List.nil_append,List.append_nil] using
    (Prefix.step (service:=service) (Prefix.initial (initial:=source reserve pending after beforeP tag) (start:=before) (past0:=past)) lookupCalled)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath.split


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginEnvelopePath.reached
