-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
/-! The actual free full frontend and its observed macro journal retain the same original stateful reserve tails. No observation or callback outcome changes source sealing syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FullSpec FreshBounds)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformOriginSourceTails (HasTails)
open RegistrationNativePlatformOriginFreeFullTrace (State frontend)
variable {n : Nat} {Platform Failure Reader Response A View : Type}
variable (env : Environment n Platform) (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : FreshBounds)
local notation "front" => frontend env reserve crypto codec route serverKeyId bounds

/-- The complete actual ledger/source frontend has the genuine post-seal reserve tails at every initial state. -/
theorem unobserved (work : OracleComp FullSpec A) (before : State n Platform) :
    HasTails Platform Failure ((simulateQ front work).run before) := by
  rw [RegistrationNativePlatformOriginFreeFullTrace.frontend_source]
  exact RegistrationNativePlatformOriginSourceTails.map _ _
    (RegistrationNativePlatformOriginNativeTails.program env reserve codec route _ _ _ _)

/-- Recording the same actual full callback snapshots preserves every original reserve continuation. -/
theorem query (observe : State n Platform → View) (request : FullSpec.Domain)
    (before : State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    HasTails Platform Failure ((RegistrationNativeObservedStageTrace.handler observe front request).run before) := by
  change HasTails Platform Failure ((fun result=>(result.1,(result.2,before.2++[⟨request,observe before.1,result.1,observe result.2⟩]))) <$>
    (front request).run before.1)
  apply RegistrationNativePlatformOriginSourceTails.map
  simpa only [simulateQ_spec_query] using unobserved env reserve crypto codec route serverKeyId bounds (FullSpec.query request) before.1

/-- Every adaptive observed full run retains the genuine original post-seal tails, without a whole-program source premise. -/
theorem program (observe : State n Platform → View) (work : OracleComp FullSpec A)
    (before : State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    HasTails Platform Failure ((simulateQ (RegistrationNativeObservedStageTrace.handler observe front) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure];trivial
  | query_bind request next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact RegistrationNativePlatformOriginSourceTails.bind _ _
      (query env reserve crypto codec route serverKeyId bounds observe request before)
      (fun result=>ih result.1 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.unobserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.unobserved
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginObservedTails.program
