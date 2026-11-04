-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSessionEvents
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents
open PqxdhDeploymentInterface (Handle Entry Budget)
open PqxdhServerAuthExperiment (Codec)
open PqxdhRecordLiftIdeal (Partners Counterpart PublishedBefore ForgedAt CrossAccept)
variable {n : Nat} {Reader Response E X : Type}

/-- An original public partner mismatch on two opposite-role handles at the same computed hidden slot. No private slot converse is used. -/
def Mismatch (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (transcript : List Entry)
    (slots : Handle → Option (PqxdhRecordLiftInterface.Slot n)) : Prop :=
  ∃first second,Partners slots first second ∧¬RegistrationNativeSessionEvents.CEPartners budget target transcript first second

/-- Correct successful-session public partnership gives exactly the same public counterpart lookup. -/
theorem counterpart (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (transcript : List Entry)
    (first second : Handle) (partnered : RegistrationNativeSessionEvents.CEPartners budget target transcript first second) :
    RegistrationNativeSessionEvents.cpart budget target transcript first=some second := by
  rcases partnered with ⟨rfl,peer⟩|⟨rfl,peer⟩
  · exact peer.symm
  · obtain ⟨keyId,_found,same⟩ :=Option.map_eq_some_iff.mp peer.symm
    subst first
    rfl

/-- A public nonpartner returned the same accepted frame either crosses physical slots or witnesses the same-slot public mismatch. The returned frame may occur anywhere in the final transcript. -/
theorem cross_or_mismatch (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
    (view : PqxdhRecordLiftIdeal.View n E X) (value : X × PqxdhDeploymentSecrecy.Ledger × E)
    (present : value∈view.result) (entry : Entry) (member : entry∈value.2.1.transcript)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (first second : Handle) (frame : RawCtxReceive.DecodedFrame)
    (received : entry.received=some (receiver,raw,.Some decrypted))
    (routed : PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some first)
    (decoded : codec.frameRead raw=some frame)
    (published : PublishedBefore codec value.2.1.transcript second frame)
    (hidden : (view.slots first).isSome ∨(view.slots second).isSome)
    (unrelated : ¬RegistrationNativeSessionEvents.CEPartners budget target value.2.1.transcript first second) :
    CrossAccept codec route view ∨Mismatch budget target value.2.1.transcript view.slots := by
  classical
  by_cases physical : Partners view.slots first second
  · exact Or.inr ⟨first,second,physical,unrelated⟩
  · exact Or.inl ⟨value,present,entry,member,receiver,raw,decrypted,first,second,frame,
      received,routed,decoded,published,hidden,physical⟩

/-- An original hidden-handle public origin failure is a physical unpublished receive or a same-slot public mismatch. Failed history is retained and no earlier public publication is inferred from production. -/
theorem origin_or_mismatch (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
    (transcript before : List Entry) (entry : Entry)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (handle : Handle) (frame : RawCtxReceive.DecodedFrame)
    (slots : Handle → Option (PqxdhRecordLiftInterface.Slot n)) (slot : PqxdhRecordLiftInterface.Slot n)
    (received : entry.received=some (receiver,raw,.Some decrypted))
    (routed : PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle)
    (hidden : slots handle=some slot) (decoded : codec.frameRead raw=some frame)
    (unpublished : ∀other,RegistrationNativeSessionEvents.cpart budget target transcript handle=some other →
      ¬PublishedBefore codec before other frame) :
    ForgedAt codec route slots before entry ∨Mismatch budget target transcript slots := by
  classical
  by_cases absent : ∀other,Counterpart slots slot handle other →¬PublishedBefore codec before other frame
  · exact Or.inl ⟨receiver,raw,decrypted,handle,slot,frame,received,routed,hidden,decoded,absent⟩
  · push Not at absent
    obtain ⟨other,opposite,published⟩ :=absent
    refine Or.inr ⟨handle,other,⟨slot,hidden,opposite⟩,?_⟩
    intro partnered
    exact unpublished other (counterpart budget target transcript handle other partnered) published
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.counterpart' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.counterpart


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.cross_or_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.cross_or_mismatch


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.origin_or_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents.origin_or_mismatch
