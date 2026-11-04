-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
/-! A stage observer augments the same concrete call packet. Erasing only its log recovers the original adaptive returned objects and platform state. This local assembly helper imposes no change to the native dictionary or the public source runtime. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {N Reply Log I Value :Type} {spec :OracleSpec I}
variable {Private :N→Type} {model :ProbComp (Reply×N)}

structure Augmentation (call :TotalStep Private model) (Log :Type) where
  sample :ProbComp (call.step.Packet×Log)
  erase :Prod.fst <$>sample=call.step.sample

def project (call :TotalStep Private model) (augmented :Augmentation call Log)
    (packet :{value //value∈support augmented.sample}) :{value //value∈support call.step.sample} :=by
  refine ⟨packet.val.1,?_⟩
  rw [←augmented.erase,support_map]
  exact ⟨packet.val,packet.property,rfl⟩

noncomputable def answer (call :TotalStep Private model)
    (packet :{value //value∈support call.step.sample}) :Reply×RegistrationNativePlatformExtractedSdkPublic.State Private :=
  (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
    ⟨(call.step.native packet.val).2,RegistrationNativePlatformExtractedSdkPublic.store call packet⟩)

theorem project_sample (call :TotalStep Private model) (augmented :Augmentation call Log) :
    project call augmented <$>PFunctor.FreeM.attachSupp augmented.sample=PFunctor.FreeM.attachSupp call.step.sample :=by
  apply (map_inj_right (f:=Subtype.val) (fun equality=>Subtype.val_injective equality)).mp
  rw [PFunctor.FreeM.map_attachSupp,Functor.map_map]
  have erased:=congrArg (fun computation=>Prod.fst <$>computation) (PFunctor.FreeM.map_attachSupp augmented.sample)
  simp only [Functor.map_map] at erased
  exact erased.trans augmented.erase

noncomputable def unchanged (call :TotalStep Private model) (prior :Log) :Augmentation call Log where
  sample:=(fun packet=>(packet,prior)) <$>call.step.sample
  erase:=by rw [Functor.map_map];exact LawfulFunctor.id_map _

theorem unchanged_log (call :TotalStep Private model) (prior :Log)
    (packet :{value //value∈support (unchanged call prior).sample}) :packet.val.2=prior :=by
  have supported:=packet.property
  change packet.val∈support ((fun value=>(value,prior)) <$>call.step.sample) at supported
  rw [support_map] at supported
  obtain ⟨_,_,same⟩:=supported
  exact congrArg Prod.snd same.symm

variable (Private :N→Type) (model :QueryImpl spec (StateT N ProbComp))
variable (calls :∀query current,Private current→TotalStep Private ((model query).run current))
variable (augment :∀query (before :RegistrationNativePlatformExtractedSdkPublic.State Private),
  Log→Augmentation (calls query before.1 before.2) Log)

noncomputable def handler :QueryImpl spec (StateT (RegistrationNativePlatformExtractedSdkPublic.State Private×Log) ProbComp) :=fun query before=>
  let call:=calls query before.1.1 before.1.2
  let augmented:=augment query before.1 before.2
  (fun packet=>
    let result:=answer call (project call augmented packet)
    (result.1,(result.2,packet.val.2))) <$>PFunctor.FreeM.attachSupp augmented.sample

theorem query_erase (query :spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private×Log) :
    Prod.map id Prod.fst <$> (handler Private model calls augment query).run before=
      (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls query).run before.1 :=by
  unfold handler RegistrationNativePlatformExtractedSdkPublic.handler
  simp only [StateT.run,Functor.map_map,Prod.map_def,id_eq]
  change (fun packet=>answer (calls query before.1.1 before.1.2)
    (project _ (augment query before.1 before.2) packet)) <$>
      PFunctor.FreeM.attachSupp (augment query before.1 before.2).sample=
    answer (calls query before.1.1 before.1.2) <$>PFunctor.FreeM.attachSupp (calls query before.1.1 before.1.2).step.sample
  rw [←project_sample _ (augment query before.1 before.2),Functor.map_map]

theorem query_unchanged (query :spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private×Log) :
    (handler Private model calls (fun selected current prior=>unchanged (calls selected current.1 current.2) prior) query).run before=
      (fun result=>(result.1,(result.2,before.2))) <$>
        (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls query).run before.1 :=by
  dsimp only [handler,RegistrationNativePlatformExtractedSdkPublic.handler,StateT.run]
  rw [←project_sample (calls query before.1.1 before.1.2) (unchanged _ before.2),Functor.map_map,Functor.map_map]
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp (unchanged (calls query before.1.1 before.1.2) before.2).sample)
  funext packet
  rw [unchanged_log]
  rfl

theorem program_erase (work :OracleComp spec Value) (before :RegistrationNativePlatformExtractedSdkPublic.State Private×Log) :
    Prod.map id Prod.fst <$> (simulateQ (handler Private model calls augment) work).run before=
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (query_erase Private model calls augment) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.project_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.project_sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.query_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.query_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.query_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime.program_erase
