-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
/-! One successful installation has one opaque slot receipt and its exact optional current descriptor. Filtering present descriptors recovers precisely the ordinary G2 installation chronology, without assuming that arbitrary known installations have a current descriptor. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformPublicRecordSlots (snapshotUpdate pendingUpdate)
open RegistrationNativePlatformRecordSlotGhost (Receipt)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG2Trace (Event)
open PqxdhRecordLiftInterface (Role)
variable {n : Nat} {KemSK : Type}

structure Witness (n : Nat) where
  receipt : Receipt n
  message : Option Message

def event (entry : Witness n) : Option (Role × Message) := entry.message.map (fun message=>(entry.receipt.role,message))

def install : Event → Option (Role × Message)
  | .install role message => some (role,message)
  | _ => none

def note (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State) : Option (Witness n) :=
  match query with
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId _ _)))))) =>
      if @Eq Bool reply true then some ⟨⟨.server,.peer keyId,ghost.pending⟩,trace.current⟩ else none
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner _ _)))))) =>
      if @Eq Bool reply true then some ⟨⟨.beacon,.owner owner,ghost.pending⟩,trace.current⟩ else none
  | _ => none

def Ordered (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State)
    (entries : List (Witness n)) : Prop :=
  ghost.snapshot.installs=entries.map Witness.receipt ∧ trace.events.filterMap install=entries.filterMap event

/-- The opaque and descriptor observers append exactly the same successful call, preserving role, handle and order. -/
theorem lists (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State) :
    (RegistrationNativePlatformPublicRecordSlots.step query reply ghost).snapshot.installs =
      ghost.snapshot.installs ++ ((note query reply ghost trace).map Witness.receipt).toList ∧
    (RegistrationNativeG2Trace.finish query reply (RegistrationNativeG2Trace.begin query trace)).events.filterMap install =
      trace.events.filterMap install ++ ((note query reply ghost trace).bind event).toList := by
  rcases query with (prepare|(demand|(publication|environment))|((other|key)|(pool|key)))|record
  · simp only [RegistrationNativePlatformPublicRecordSlots.step,snapshotUpdate,note,
      RegistrationNativeG2Trace.begin,RegistrationNativeG2Trace.finish,List.filterMap_append,
      List.filterMap_cons,install,List.filterMap_nil,List.append_nil,Option.map_none,Option.toList_none,Option.bind_none]
    trivial
  · simp only [RegistrationNativePlatformPublicRecordSlots.step,snapshotUpdate,note,
      RegistrationNativeG2Trace.begin,RegistrationNativeG2Trace.finish,List.filterMap_append,
      List.filterMap_cons,install,List.filterMap_nil,List.append_nil,Option.map_none,Option.toList_none,Option.bind_none]
    trivial
  · exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩
  · rcases environment with coin|capability
    · exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩
    · cases capability with
      | installServer keyId binding kernel | installBeacon owner binding kernel =>
          cases reply <;> cases current : trace.current <;>
            simp [RegistrationNativePlatformPublicRecordSlots.step,snapshotUpdate,note,
              RegistrationNativeG2Trace.begin,RegistrationNativeG2Trace.finish,RegistrationNativeG2Trace.installed,
              RegistrationNativeG2Trace.attempt,current,install,event]
          all_goals rfl
      | _ => exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩
  · exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩
  · simp only [RegistrationNativePlatformPublicRecordSlots.step,snapshotUpdate,note,
      RegistrationNativeG2Trace.begin,RegistrationNativeG2Trace.finish,List.filterMap_append,
      List.filterMap_cons,install,List.filterMap_nil,List.append_nil,Option.map_none,Option.toList_none,Option.bind_none]
    trivial
  · exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩
  · simp only [RegistrationNativePlatformPublicRecordSlots.step,snapshotUpdate,note,
      RegistrationNativeG2Trace.begin,RegistrationNativeG2Trace.finish,List.filterMap_append,
      List.filterMap_cons,install,List.filterMap_nil,List.append_nil,Option.map_none,Option.toList_none,Option.bind_none]
    trivial
  · exact ⟨(List.append_nil _).symm,(List.append_nil _).symm⟩

/-- A single shared query extends the ordered witness list by precisely its own successful receipt. -/
theorem ordered_step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State)
    (entries : List (Witness n)) (before : Ordered ghost trace entries) :
    Ordered (RegistrationNativePlatformPublicRecordSlots.step query reply ghost)
      (RegistrationNativeG2Trace.finish query reply (RegistrationNativeG2Trace.begin query trace))
      (entries ++ (note query reply ghost trace).toList) := by
  have added := lists query reply ghost trace
  unfold Ordered
  rw [List.map_append,List.filterMap_append,←before.1,←before.2]
  cases actual : note query reply ghost trace with
  | none => simpa only [actual,Option.map_none,Option.bind_none,Option.toList_none,List.map_nil,List.filterMap_nil] using added
  | some entry =>
      cases described : event entry <;>
        simpa only [actual,Option.map_some,Option.bind_some,Option.toList_some,List.map_cons,List.map_nil,
          List.filterMap_cons,List.filterMap_nil,described,Option.toList_none] using added

/-- Cold observers begin with the empty common successful-install chronology. -/
theorem ordered_initial : Ordered (RegistrationNativePlatformPublicRecordSlots.initial (n := n)) RegistrationNativeG2Trace.initial [] := by
  trivial

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.lists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.lists

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_initial
