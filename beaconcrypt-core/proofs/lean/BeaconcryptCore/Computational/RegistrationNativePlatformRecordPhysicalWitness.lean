-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionTargets
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPhysicalWitness
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Entry Budget Handle)
open RegistrationNativePlatformRecordSessionTargets (Kind Witness claimedHandle)
variable {n : Nat} {Reader Response E Value : Type}
def Physical (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (kind : Kind) (view : PqxdhRecordLiftIdeal.View n E Value) (priorList : List Entry) (entry : Entry) : Prop :=
  match kind with
  | .origin _ => PqxdhRecordLiftIdeal.ForgedAt codec route view.slots priorList entry
  | _ => PqxdhRecordLiftIdeal.CrossAccept codec route view
/-- Each original broad witness on its actual hidden claimed handle is either the physical record failure or a same-slot public partner mismatch. The final public transcript and the before-receive publication prefix are unchanged. -/
theorem witness (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64) (budget : Budget)
    (route : RawCtxServerRouting.SenderDecoder) (kind : Kind) (target : Fin budget.accept × Fin budget.capacity)
    (view : PqxdhRecordLiftIdeal.View n E Value) (value : Value × PqxdhDeploymentSecrecy.Ledger × E)
    (present : value∈view.result) (priorList : List Entry) (entry : Entry) (later : List Entry)
    (splitLedger : value.2.1.transcript=priorList++entry::later)
    (original : Witness crypto codec serverKeyId budget route kind target value.2.1.transcript priorList entry)
    (handle : Handle) (claimed : claimedHandle route kind entry=some handle) (hidden : (view.slots handle).isSome) :
    Physical codec route kind view priorList entry ∨
      RegistrationNativePlatformRecordPartnerEvents.Mismatch budget target value.2.1.transcript view.slots := by
  have member : entry∈value.2.1.transcript := by
    rw [splitLedger]
    exact List.mem_append_right _ List.mem_cons_self
  cases kind with
  | origin direction =>
    obtain ⟨receiver,raw,opened,current,frame,received,routed,_direction,_designated,decoded,unpublished⟩:=original
    have same : current=handle := by
      simpa only [claimedHandle,PqxdhDeploymentHeadlineEvents.receivedHandle,received,Option.bind_some,routed,Option.some.injEq] using claimed
    subst current
    obtain ⟨slot,slotAt⟩:=Option.isSome_iff_exists.mp hidden
    exact RegistrationNativePlatformRecordPartnerEvents.origin_or_mismatch codec route budget target _ priorList entry receiver raw opened handle frame view.slots slot
      received routed slotAt decoded unpublished
  | receiver =>
    obtain ⟨receiver,raw,opened,keyId,sender,frame,received,routed,decoded,published,_designated,unrelated⟩:=original
    have same : Handle.peer keyId=handle := by
      simpa only [claimedHandle,PqxdhDeploymentHeadlineEvents.receivedHandle,received,Option.bind_some,routed,Option.some.injEq] using claimed
    subst handle
    exact RegistrationNativePlatformRecordPartnerEvents.cross_or_mismatch codec route budget target view value present entry member receiver raw opened
      (.peer keyId) sender frame received routed decoded published (Or.inl hidden) unrelated
  | sender =>
    obtain ⟨owner,encrypted,frame,published,decoded,_designated,other,otherAt,receiver,raw,opened,receiving,received,routed,readFrame,unrelated⟩:=original
    have same : Handle.owner owner=handle := by
      simpa only [claimedHandle,PqxdhDeploymentHeadlineEvents.publishedHandle,published,Option.map_some,Option.some.injEq] using claimed
    subst handle
    have sent : PqxdhRecordLiftIdeal.PublishedBefore codec value.2.1.transcript (.owner owner) frame :=
      ⟨encrypted,List.mem_filterMap.mpr ⟨entry,member,published⟩,decoded⟩
    exact RegistrationNativePlatformRecordPartnerEvents.cross_or_mismatch codec route budget target view value present other otherAt receiver raw opened
      receiving (.owner owner) frame received routed readFrame sent (Or.inr hidden) unrelated
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPhysicalWitness
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPhysicalWitness.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPhysicalWitness.witness
