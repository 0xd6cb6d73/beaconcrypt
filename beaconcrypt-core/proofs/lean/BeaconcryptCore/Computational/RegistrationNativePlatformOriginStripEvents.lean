-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents
open RegistrationNativeEntropyTrace (strip stripEntry)
open PqxdhDeploymentInterface (Entry)
variable {n : Nat} {Reader Response : Type}
private theorem entry_received (original decoded : Entry) (same : stripEntry original=some decoded) :
    original.received=decoded.received := by
  have projected:=congrArg List.head? (RegistrationNativeEntropyTrace.projection_strip
    Entry.received (fun _ _ _=>rfl) [original])
  simp only [strip,List.filterMap_cons,same,List.filterMap_nil] at projected
  cases first : original.received <;> cases second : decoded.received
  all_goals simp only [first,second,List.head?_cons,List.head?_nil] at projected ⊢
  all_goals exact projected.symm
/-- A forged receive in the restored ledger has its exact original occurrence and original chronological publication prefix. -/
theorem forged (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (slots : PqxdhDeploymentInterface.Handle→Option (PqxdhRecordLiftInterface.Slot n))
    (transcript before : List Entry) (entry : Entry) (after : List Entry)
    (split : strip transcript=before++entry::after)
    (bad : PqxdhRecordLiftIdeal.ForgedAt codec route slots before entry) :
    ∃leading original later,transcript=leading++original::later ∧strip leading=before ∧
      original.received=entry.received ∧PqxdhRecordLiftIdeal.ForgedAt codec route slots leading original := by
  obtain ⟨left,rest,full,leftMap,restMap⟩:=List.filterMap_eq_append_iff.mp split
  obtain ⟨skipped,original,tail,restFull,skippedNone,selected,_tailMap⟩:=List.filterMap_eq_cons_iff.mp restMap
  have sourceSplit : transcript=(left++skipped)++original::tail := by
    rw [full,restFull,List.append_assoc]
  have empty : strip skipped=[]:=List.filterMap_eq_nil_iff.mpr skippedNone
  have beforeMap : strip (left++skipped)=before := by
    rw [RegistrationNativeEntropyTrace.strip_append,empty,List.append_nil]
    exact leftMap
  have received:=entry_received original entry selected
  refine ⟨left++skipped,original,tail,sourceSplit,beforeMap,received,?_⟩
  obtain ⟨receiver,raw,opened,handle,slot,frame,returned,routed,hidden,decoded,unpublished⟩:=bad
  refine ⟨receiver,raw,opened,handle,slot,frame,received.trans returned,routed,hidden,decoded,?_⟩
  intro other counterpart published
  apply unpublished other counterpart
  rw [←beforeMap]
  exact (RegistrationNativeRecordOriginTrace.published_strip codec (left++skipped) other frame).mpr published
/-- Every actual accepted record remains an exact received record after metadata and HMAC restoration. -/
theorem received (transcript : List Entry) (entry : Entry) (member : entry∈transcript)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (returned : entry.received=some (receiver,raw,.Some opened)) :
    ∃decoded∈strip transcript,decoded.received=some (receiver,raw,.Some opened) := by
  apply List.mem_filterMap.mp
  rw [RegistrationNativeEntropyTrace.projection_strip Entry.received (fun _ _ _=>rfl)]
  exact List.mem_filterMap.mpr ⟨entry,member,returned⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents.forged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents.forged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents.received' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStripEvents.received
