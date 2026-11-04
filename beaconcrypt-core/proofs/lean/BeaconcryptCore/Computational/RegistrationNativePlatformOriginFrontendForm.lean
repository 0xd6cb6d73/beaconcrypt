-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginFreeFullTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm
open PqxdhDeploymentInterface (FullSpec FreshBounds)
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformOriginSourceSendSyntax (Form)
open RegistrationNativePlatformOriginFreeFullTrace (frontend State fullJoin)
variable {n : Nat} {Platform Failure Reader Response View : Type}

/-- The original billed sending predicate is exactly one of the four source send-producing callback constructors, without a success premise. -/
theorem sending (query : FullSpec.Domain) (counted : RegistrationNativePlatformOriginSendCallbackBudget.Sending query) :
    RegistrationNativePlatformOriginLedgerSendSyntax.Sending query := by
  rcases query with (coin|command)|command
  · simp [RegistrationNativePlatformOriginSendCallbackBudget.Sending,PqxdhDeploymentInterface.queryClass] at counted
  · cases command
    all_goals first
      | exact .server _ _
      | exact .beacon _ _
      | simp [RegistrationNativePlatformOriginSendCallbackBudget.Sending,PqxdhDeploymentInterface.queryClass] at counted
  · cases command
    all_goals first
      | exact .test _ _ _
      | exact .fresh _ _

variable (env : Environment n Platform) (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : FreshBounds)

/-- The literal actual free frontend has the same refused/public reply and source normal form after complete ledger/platform/control reassociation. -/
theorem query (request : FullSpec.Domain) (counted : RegistrationNativePlatformOriginSendCallbackBudget.Sending request)
    (before : State n Platform) :
    Form reserve (fun result=>RegistrationNativePlatformOriginLedgerSendSyntax.reply request result.1)
      ((frontend env reserve crypto codec route serverKeyId bounds request).run before) := by
  have source:=RegistrationNativePlatformOriginFreeFullTrace.frontend_source env reserve crypto codec route serverKeyId bounds
    (FullSpec.query request) before
  simp only [simulateQ_spec_query] at source
  rw [source]
  exact (RegistrationNativePlatformOriginSourceSendSyntax.ledger env reserve codec route crypto serverKeyId bounds request
    (sending request counted) before.1 before.2.1.1 before.2.1.2 before.2.2).map fullJoin _ (fun _=>rfl)

/-- Appending the actual projected callback journal preserves that same optional reply and complete source normal form. -/
theorem observed (observe : State n Platform → View) (request : FullSpec.Domain)
    (counted : RegistrationNativePlatformOriginSendCallbackBudget.Sending request)
    (before : State n Platform × List (RegistrationNativeStageTrace.Call FullSpec View)) :
    Form reserve (fun result=>RegistrationNativePlatformOriginLedgerSendSyntax.reply request result.1)
      ((RegistrationNativeObservedStageTrace.handler observe (frontend env reserve crypto codec route serverKeyId bounds) request).run before) := by
  change Form reserve _ ((fun result=>(result.1,(result.2,before.2++[⟨request,observe before.1,result.1,observe result.2⟩]))) <$>
    (frontend env reserve crypto codec route serverKeyId bounds request).run before.1)
  exact (query env reserve crypto codec route serverKeyId bounds request counted before.1).map _ _ (fun _=>rfl)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.sending' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.sending

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFrontendForm.observed
