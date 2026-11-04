-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! Erase a supported SDK common run to actual source execution. Each concrete constructor must derive its source operation and deterministic actual returned-object update; a native marginal alone does not establish this theorem's source diagram. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {N S I A : Type} {spec : OracleSpec I}
variable (Private : N →Type) (model : QueryImpl spec (StateT N ProbComp))
variable (calls : ∀query current,Private current →TotalStep Private ((model query).run current))

/-- This generic certificate is built internally by the selected concrete SDK dispatcher. Its source program executes actual extracted bodies; its update retains only actual returned objects, source observations and physical primitive/platform state. -/
structure Diagram where
  physical : RegistrationNativePlatformExtractedSdkPublic.State Private →S
  source : QueryImpl spec (StateT S ProbComp)
  update : ∀selected (before : RegistrationNativePlatformExtractedSdkPublic.State Private),
    RustM (calls selected before.1 before.2).step.sourceType ×N →spec.Range selected ×S
  operation : ∀selected before,
    (update selected before) <$> (calls selected before.1 before.2).step.sourceCall=
      (source selected).run (physical before)
  retained : ∀selected (before : RegistrationNativePlatformExtractedSdkPublic.State Private)
    (packet : {value //value∈support (calls selected before.1 before.2).step.sample}),
    let call := calls selected before.1 before.2
    (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
      physical ⟨(call.step.native packet.val).2,RegistrationNativePlatformExtractedSdkPublic.store call packet⟩)=
    update selected before (call.step.sourceReply packet.val,call.step.sourceState packet.val)

theorem query (diagram : Diagram Private model calls (S:=S))
    (selected : spec.Domain) (before : RegistrationNativePlatformExtractedSdkPublic.State Private) :
    Prod.map id diagram.physical <$>
      ((RegistrationNativePlatformExtractedSdkPublic.handler Private model calls selected).run before)=
      (diagram.source selected).run (diagram.physical before) := by
  let call := calls selected before.1 before.2
  calc
    _ = (fun packet : {value //value∈support call.step.sample} =>
        diagram.update selected before (call.step.sourceReply packet.val,call.step.sourceState packet.val)) <$>
          PFunctor.FreeM.attachSupp call.step.sample := by
      change Prod.map id diagram.physical <$>
        ((fun packet =>(call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
          (⟨(call.step.native packet.val).2,RegistrationNativePlatformExtractedSdkPublic.store call packet⟩ :
            RegistrationNativePlatformExtractedSdkPublic.State Private))) <$>
          PFunctor.FreeM.attachSupp call.step.sample)=_
      rw [Functor.map_map]
      apply congrArg (fun observe =>observe <$>PFunctor.FreeM.attachSupp call.step.sample)
      funext packet
      exact diagram.retained selected before packet
    _ = diagram.update selected before <$>call.step.sourceCall := by
      rw [←call.step.source_exact,Functor.map_map]
      have equation := congrArg
        (fun work => (fun packet =>diagram.update selected before (call.step.sourceReply packet,call.step.sourceState packet)) <$>work)
        (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
      simp only [Functor.map_map] at equation
      exact equation
    _ = _ := diagram.operation selected before

/-- This adaptive induction uses the actual source marginal and actual returned-object update on every call, including refusal and None outcomes. -/
theorem program (diagram : Diagram Private model calls (S:=S))
    (work : OracleComp spec A) (before : RegistrationNativePlatformExtractedSdkPublic.State Private) :
    Prod.map id diagram.physical <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before=
      (simulateQ diagram.source work).run (diagram.physical before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ diagram.physical (query Private model calls diagram) work before

theorem event (diagram : Diagram Private model calls (S:=S))
    (work : OracleComp spec A) (before : RegistrationNativePlatformExtractedSdkPublic.State Private)
    (decision : A ×S →Bool) :
    (fun result =>decision (result.1,diagram.physical result.2)) <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before=
    decision <$> (simulateQ diagram.source work).run (diagram.physical before) := by
  rw [←program Private model calls diagram work before,Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkSourceErasure.event
