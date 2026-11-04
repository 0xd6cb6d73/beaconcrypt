-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
/-! The selected concrete SDK dictionaries have proved normal Rust return, while optional rejection and allocation refusal remain ordinary returned values. A normal step obtains its public reply from the actual returned SDK value. Private objects and their full material/backend relation are threaded without exposing the common receipt to the client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open RegistrationNativePlatformExtractedSdkAdaptive (Step)
variable {N Reply I A : Type} {spec : OracleSpec I}

/-- Concrete constructors derive these two local properties from source progress and exact returned-value representation. They are not whole-client or security correspondence premises. -/
structure TotalStep (Private : N  → Type) (model : ProbComp (Reply ×N)) where
  step : Step Private model
  observe : step.sourceType  → Reply
  normal : ∀packet,packet∈support step.sample  → ∃returned,step.sourceReply packet=.ok returned
  reply : ∀packet,packet∈support step.sample  → ∀returned,step.sourceReply packet=.ok returned  → observe returned=(step.native packet).1

noncomputable def returned {Private : N  → Type} {model : ProbComp (Reply ×N)}
    (call : TotalStep Private model) (packet : {value //value∈support call.step.sample}) : call.step.sourceType :=
  Classical.choose (call.normal packet.val packet.property)

theorem returned_exact {Private : N  → Type} {model : ProbComp (Reply ×N)}
    (call : TotalStep Private model) (packet : {value //value∈support call.step.sample}) :
    call.step.sourceReply packet.val=.ok (returned call packet) :=
  Classical.choose_spec (call.normal packet.val packet.property)

noncomputable def store {Private : N  → Type} {model : ProbComp (Reply ×N)}
    (call : TotalStep Private model) (packet : {value //value∈support call.step.sample}) :
    Private (call.step.native packet.val).2 := by
  have stored := call.step.store packet.val packet.property
  rw [returned_exact call packet] at stored
  exact stored

abbrev State (Private : N  → Type) := Sigma Private
def project (Private : N  → Type) (state : State Private) : N := state.1

/-- Sampling the actual common SDK receipt and selecting only its actual returned public value. Unsupported source failure is not given a replacement object. -/
noncomputable def handler (Private : N  → Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current  → TotalStep Private ((model query).run current)) :
    QueryImpl spec (StateT (State Private) ProbComp) := fun query before =>
  let call := calls query before.1 before.2
  (fun packet =>(call.observe (returned call packet),
    (⟨(call.step.native packet.val).2,store call packet⟩ : State Private))) <$>
      PFunctor.FreeM.attachSupp call.step.sample

theorem query (Private : N  → Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current  → TotalStep Private ((model query).run current))
    (selected : spec.Domain) (before : State Private) :
    Prod.map id (project Private) <$> ((handler Private model calls selected).run before)=
      (model selected).run (project Private before) := by
  let call := calls selected before.1 before.2
  change Prod.map id (project Private) <$>
    ((fun packet =>(call.observe (returned call packet),
      (⟨(call.step.native packet.val).2,store call packet⟩ : State Private))) <$>
        PFunctor.FreeM.attachSupp call.step.sample)=_
  simp only [Functor.map_map,Prod.map,id_eq,project]
  have publicReply (packet : {value //value∈support call.step.sample}) :
      call.observe (returned call packet)=(call.step.native packet.val).1 :=
    call.reply packet.val packet.property (returned call packet) (returned_exact call packet)
  simp only [publicReply,Prod.mk.eta]
  have erased := congrArg (fun work =>call.step.native <$> work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  have same : (fun packet =>call.step.native packet.val) <$> PFunctor.FreeM.attachSupp call.step.sample=
      call.step.native <$>call.step.sample := by
    simpa only [Functor.map_map,Function.comp_def] using erased
  exact same.trans call.step.native_exact

/-- The full adaptive public client receives only the actual SDK public replies. This exact joint law, rather than two one-sided bad-event containments, supports centered LR transport. -/
theorem program (Private : N  → Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current  → TotalStep Private ((model query).run current))
    (work : OracleComp spec A) (before : State Private) :
    Prod.map id (project Private) <$> (simulateQ (handler Private model calls) work).run before=
      (simulateQ model work).run (project Private before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project Private) (query Private model calls) work before

theorem event (Private : N  → Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current  → TotalStep Private ((model query).run current))
    (work : OracleComp spec A) (before : State Private) (decision : A ×N  → Bool) :
    (fun result =>decision (result.1,project Private result.2)) <$>
      (simulateQ (handler Private model calls) work).run before=
    decision <$> (simulateQ model work).run (project Private before) := by
  rw [←program Private model calls work before,Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.returned_exact' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.returned_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic.event
