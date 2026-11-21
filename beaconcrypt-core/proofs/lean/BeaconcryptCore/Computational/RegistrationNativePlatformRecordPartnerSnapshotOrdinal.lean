-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace
import BeaconcryptCore.Computational.RegistrationNativeInstallOrdinals
/-! The same ordered installation witnesses identify the public handle at each native descriptor ordinal. Existing exact source message counts rule out missing descriptors; successful session and raw attempt coordinates are never identified. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal
open PqxdhRecordLiftInterface (Role)
open PqxdhDeploymentInterface (Handle)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePlatformRecordPartnerSlotTraceCore (Witness Ordered install event)
variable {n : Nat}

def receiptHandles (role : Role) (snapshot : RegistrationNativePlatformRecordSlotGhost.State n) : List Handle :=
  snapshot.installs.filterMap fun receipt=>if receipt.role=role then some receipt.handle else none

def handles (role : Role) (entries : List (Witness n)) : List Handle :=
  entries.filterMap fun entry=>if entry.receipt.role=role then some entry.receipt.handle else none

def messages (role : Role) (entries : List (Witness n)) : List Message :=
  entries.filterMap fun entry=>if entry.receipt.role=role then entry.message else none

def Complete (role : Role) (entries : List (Witness n)) : Prop :=
  ∀entry∈entries,entry.receipt.role=role → entry.message.isSome=true

/-- The successful opaque receipts and complete native descriptor trace have the same role-filtered ordered projections. -/
theorem ordered (role : Role) (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (trace : RegistrationNativeG2Trace.State) (entries : List (Witness n)) (valid : Ordered ghost trace entries) :
    receiptHandles role ghost.snapshot=handles role entries ∧
      RegistrationNativeInstallOrdinals.messages role trace.events=messages role entries := by
  constructor
  · rw [receiptHandles,valid.1,List.filterMap_map]
    rfl
  · have projected := congrArg (List.filterMap (fun item : Role × Message=>if item.1=role then some item.2 else none)) valid.2
    rw [List.filterMap_filterMap,List.filterMap_filterMap] at projected
    have first : (fun a=> (install a).bind (fun item : Role × Message=>if item.1=role then some item.2 else none)) =
        (fun current=>match current with | .install installed message=>if installed=role then some message else none | _=>none) := by
      funext current
      cases current <;> rfl
    have last : (fun a : Witness n=> (event a).bind (fun item : Role × Message=>if item.1=role then some item.2 else none)) =
        (fun entry : Witness n=>if entry.receipt.role=role then entry.message else none) := by
      funext entry
      cases described : entry.message <;> by_cases same : entry.receipt.role=role <;> simp [event,described,same]
    rw [first,last] at projected
    exact projected

private theorem length_le (role : Role) (entries : List (Witness n)) : (messages role entries).length≤(handles role entries).length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      by_cases same : head.receipt.role=role
      · cases described : head.message <;>
          simp only [messages,handles,List.filterMap_cons,same,ite_true,described,List.length_cons] at ih ⊢ <;> omega
      · simpa only [messages,handles,List.filterMap_cons,same,ite_false] using ih

/-- Exact original source counts exclude an unrecorded descriptor at any successful receipt of that role. -/
theorem complete_of_lengths (role : Role) (entries : List (Witness n))
    (same : (messages role entries).length=(handles role entries).length) : Complete role entries := by
  induction entries with
  | nil => intro entry absent; cases absent
  | cons head tail ih =>
      intro entry member selected
      by_cases typed : head.receipt.role=role
      · cases described : head.message with
        | none =>
            have bounded := length_le role tail
            simp only [messages,handles,List.filterMap_cons,typed,ite_true,described,List.length_cons] at same
            change (messages role tail).length=(handles role tail).length+1 at same
            omega
        | some message =>
            have rest : (messages role tail).length=(handles role tail).length := by
              simpa only [messages,handles,List.filterMap_cons,typed,ite_true,described,List.length_cons,Nat.add_right_cancel_iff] using same
            rcases List.mem_cons.mp member with rfl|later
            · exact Option.isSome_iff_exists.mpr ⟨message,described⟩
            · exact ih rest entry later selected
      · have rest : (messages role tail).length=(handles role tail).length := by
          simpa only [messages,handles,List.filterMap_cons,typed,ite_false] using same
        rcases List.mem_cons.mp member with rfl|later
        · exact False.elim (typed selected)
        · exact ih rest entry later selected

private theorem complete_lengths (role : Role) (entries : List (Witness n)) (complete : Complete role entries) :
    (messages role entries).length=(handles role entries).length := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      have rest : Complete role tail := fun entry member typed=>complete entry (List.mem_cons_of_mem _ member) typed
      have counted := ih rest
      by_cases typed : head.receipt.role=role
      · obtain ⟨message,described⟩ := Option.isSome_iff_exists.mp (complete head (List.mem_cons_self) typed)
        simpa only [messages,handles,List.filterMap_cons,typed,ite_true,described,List.length_cons] using congrArg Nat.succ counted
      · simpa only [messages,handles,List.filterMap_cons,typed,ite_false] using counted

/-- An actual successful receipt names its own native descriptor and public handle at one shared role ordinal. -/
theorem from_witness (role : Role) (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State)
    (transcript : List RegistrationNativeInterface.Entry) (entries past later : List (Witness n)) (entry : Witness n)
    (valid : Ordered ghost trace entries)
    (publicHandles : receiptHandles role ghost.snapshot=RegistrationNativeInstallOrdinals.handles role transcript)
    (counts : RegistrationNativeInstallOrdinals.Counts role trace.events transcript)
    (split : entries=past++entry::later) (typed : entry.receipt.role=role) (message : Message) (named : entry.message=some message) :
    ∃ ordinal,RegistrationNativeInstallOrdinals.At role trace.events transcript ordinal message entry.receipt.handle := by
  obtain ⟨handleSource,messageSource⟩ := ordered role ghost trace entries valid
  have exactHandles : RegistrationNativeInstallOrdinals.handles role transcript=handles role entries := publicHandles.symm.trans handleSource
  have equalLengths : (messages role entries).length=(handles role entries).length := by
    rw [←messageSource,←exactHandles]
    exact counts
  have complete := complete_of_lengths role entries equalLengths
  have beforeComplete : Complete role past := by
    intro previous member selected
    apply complete previous _ selected
    rw [split]
    exact List.mem_append_left _ member
  have prefixCount := complete_lengths role past beforeComplete
  refine ⟨(handles role past).length,?_,?_⟩
  · rw [messageSource]
    conv_lhs => rw [split,messages,List.filterMap_append,List.filterMap_cons]
    simp only [typed,ite_true,named]
    change (messages role past++message::messages role later)[(handles role past).length]?=some message
    rw [←prefixCount]
    simp only [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]
  · rw [exactHandles]
    conv_lhs => rw [split,handles,List.filterMap_append,List.filterMap_cons]
    simp only [typed,ite_true]
    change (handles role past++entry.receipt.handle::handles role later)[(handles role past).length]?=some entry.receipt.handle
    simp only [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.ordered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.ordered

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.complete_of_lengths' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.complete_of_lengths

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.from_witness' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal.from_witness
