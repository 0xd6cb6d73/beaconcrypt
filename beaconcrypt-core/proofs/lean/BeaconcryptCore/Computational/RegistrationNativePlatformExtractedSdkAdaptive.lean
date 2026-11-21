-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle
/-! A support-certified SDK call carries its actual source result and material-preserving private index. Only the public oracle reply selects the next command. A source error stops source execution and records its exact native/platform snapshot; an analysis-only native continuation may still finish the original public client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
variable {N Reply Source A I : Type} {spec : OracleSpec I}

def pack {Platform : Type} (result : (A ×N) ×Platform) : A ×(N ×Platform) :=
  (result.1.1,(result.1.2,result.2))

/-- The private index contains the actual returned SDK objects/RNG/tokens and their material relation. Native includes the entire persistent platform state. -/
structure Step (Private : N →Type) (model : ProbComp (Reply ×N)) where
  Packet : Type
  sample : ProbComp Packet
  sourceType : Type
  sourceReply : Packet →RustM sourceType
  sourceState : Packet →N
  sourceCall : ProbComp (RustM sourceType ×N)
  source_exact : (fun packet=>(sourceReply packet,sourceState packet)) <$> sample = sourceCall
  native : Packet →Reply ×N
  native_exact : native <$> sample = model
  store : ∀packet,packet∈support sample → match sourceReply packet with
    | .ok _=>Private (native packet).2
    | .fail _ | .div=>PUnit

inductive Status (Private : N →Type) (current : N) where
  | live (objects : Private current)
  | failed (error : Aeneas.Std.Error) (stoppedAt : N)
  | diverged (stoppedAt : N)
abbrev State (Private : N →Type) := Sigma (Status Private)

def project (Private : N →Type) (state : State Private) : N := state.1

def advanceWith (Private : N →Type) (current snapshot : N) (sourceResult : RustM Source) :
    (match sourceResult with | .ok _=>Private current | .fail _ | .div=>PUnit) →State Private :=
  match sourceResult with
  | .ok _=>fun stored=>⟨current,.live stored⟩
  | .fail error=>fun _=>⟨current,.failed error snapshot⟩
  | .div=>fun _=>⟨current,.diverged snapshot⟩
def advance {Private : N →Type} {model : ProbComp (Reply ×N)}
    (step : Step Private model) (packet : {value // value∈support step.sample}) : State Private :=
  advanceWith Private (step.native packet.val).2 (step.sourceState packet.val) (step.sourceReply packet.val)
    (step.store packet.val packet.property)

/-- Attaching a support certificate does not condition or reject any call outcome. -/
theorem attached_erase (work : ProbComp A) : Subtype.val <$> PFunctor.FreeM.attachSupp work =work :=
  PFunctor.FreeM.map_attachSupp work

/-- Every selected active call has the actual source SDK marginal, retaining its complete returned object or error. -/
theorem source_continuation {Private : N →Type} {model : ProbComp (Reply ×N)}
    (step : Step Private model) (next : RustM step.sourceType ×N →ProbComp A) :
    (PFunctor.FreeM.attachSupp step.sample >>=fun packet=>next (step.sourceReply packet.val,step.sourceState packet.val))=
      (step.sourceCall >>=next) := by
  rw [←step.source_exact,bind_map_left]
  have erased:=congrArg (fun work=>work >>=fun packet=>next (step.sourceReply packet,step.sourceState packet)) (attached_erase step.sample)
  simpa only [bind_map_left] using erased

def handler (Private : N →Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current →Step Private ((model query).run current)) :
    QueryImpl spec (StateT (State Private) ProbComp) :=fun query state=>
  match state with
  | ⟨current,.live objects⟩=>
      let step:=calls query current objects
      (fun packet=>((step.native packet.val).1,advance step packet)) <$>
        PFunctor.FreeM.attachSupp step.sample
  | ⟨current,.failed error stoppedAt⟩=>
      (fun result=>(result.1,⟨result.2,.failed error stoppedAt⟩)) <$> (model query).run current
  | ⟨current,.diverged stoppedAt⟩=>
      (fun result=>(result.1,⟨result.2,.diverged stoppedAt⟩)) <$> (model query).run current

theorem advanceWith_project (Private : N →Type) (current snapshot : N) (sourceResult : RustM Source)
    (stored : match sourceResult with | .ok _=>Private current | .fail _ | .div=>PUnit) :
    project Private (advanceWith Private current snapshot sourceResult stored)=current := by
  cases sourceResult <;> rfl

theorem advance_project {Private : N →Type} {model : ProbComp (Reply ×N)}
    (step : Step Private model) (packet : {value // value∈support step.sample}) :
    project Private (advance step packet)=(step.native packet.val).2 := by
  exact advanceWith_project Private _ _ _ _

/-- Source failures invoke no further SDK call. The native ghost retains its original next public query and exact complete marginal. -/
theorem query (Private : N →Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current →Step Private ((model query).run current))
    (selected : spec.Domain) (before : State Private) :
    Prod.map id (project Private) <$> ((handler Private model calls selected).run before)=
      (model selected).run (project Private before) := by
  rcases before with ⟨current,status⟩
  cases status with
  | live objects=>
      let step:=calls selected current objects
      change Prod.map id (project Private) <$> ((fun packet=>((step.native packet.val).1,advance step packet)) <$>
        PFunctor.FreeM.attachSupp step.sample)=_
      simp only [Functor.map_map,Prod.map, id_eq,advance_project,Prod.mk.eta]
      change (fun packet=>step.native packet.val) <$> PFunctor.FreeM.attachSupp step.sample = (model selected).run current
      have erased:=congrArg (fun work=>step.native <$> work) (attached_erase step.sample)
      have same : (fun packet=>step.native packet.val) <$> PFunctor.FreeM.attachSupp step.sample = step.native <$> step.sample := by
        simpa only [Functor.map_map,Function.comp_def] using erased
      exact same.trans step.native_exact
  | failed error stoppedAt | diverged stoppedAt=>
      simp only [handler,StateT.run,Functor.map_map,Prod.map,id_eq,project]
      exact id_map _

/-- Adaptive induction exposes only the original public query reply to the client continuation. Actual source objects remain in the private state index. -/
theorem program (Private : N →Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current →Step Private ((model query).run current))
    (work : OracleComp spec A) (before : State Private) :
    Prod.map id (project Private) <$> (simulateQ (handler Private model calls) work).run before=
      (simulateQ model work).run (project Private before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project Private) (query Private model calls) work before

def sourceReturned (Private : N →Type) (result : A ×State Private) : Prop :=
  match result.2.2 with | .live _=>True | _=>False

def sourceEvent (Private : N →Type) (event : A ×N →Bool) (result : A ×State Private) : Bool :=
  match result.2.2 with | .live _=>event (result.1,result.2.1) | _=>false

/-- A nonreturning source contributes no public security event; its exact failure-time native/platform snapshot remains in Status. -/
theorem event_bound (Private : N →Type) (model : QueryImpl spec (StateT N ProbComp))
    (calls : ∀query current,Private current →Step Private ((model query).run current))
    (work : OracleComp spec A) (before : State Private) (event : A ×N →Bool) :
    𝒟[sourceEvent Private event <$> (simulateQ (handler Private model calls) work).run before] {true}≤
      𝒟[event <$> (simulateQ model work).run (project Private before)] {true} := by
  rw [←program Private model calls work before]
  simp only [Functor.map_map,←prEvent_eq_evalDist_singleton _ true]
  apply prEvent_mono
  rintro ⟨value,⟨current,status⟩⟩ succeeded
  cases status with
  | live objects=>exact succeeded
  | failed error stoppedAt | diverged stoppedAt=>simp only [sourceEvent,Bool.false_eq_true] at succeeded
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.attached_erase' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.attached_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.source_continuation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.source_continuation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.advance_project' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.advance_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.event_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.advanceWith_project' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive.advanceWith_project
