-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInterface
/-! Pure original-entry bookkeeping for append-allocated successful accept handles. The actual Native interpreter must derive Growth from its real session state; it is a private inductive receipt, not a new public premise or trace field. The empty trace admits any initial session count. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger
open RegistrationNativeInterface (Entry)

def success : Entry → Option (Pqxdh.Bytes × Nat)
  | ⟨.inl (.inr (.accept raw)), some handle⟩ => some (raw, handle)
  | _ => none

def Growth (entry : Entry) (before after : Nat) : Prop :=
  match success entry with
  | none => after = before
  | some (_, handle) => handle = before ∧ after = before + 1

def Below (transcript : List Entry) (count : Nat) : Prop :=
  ∀ entry ∈ transcript, ∀ raw handle, success entry = some (raw, handle) → handle < count

def Unique (transcript : List Entry) : Prop :=
  ∀ left ∈ transcript, ∀ right ∈ transcript, ∀ raw other handle,
    success left = some (raw, handle) → success right = some (other, handle) → raw = other

def Holds (transcript : List Entry) (count : Nat) : Prop := Below transcript count ∧ Unique transcript

theorem empty (count : Nat) : Holds [] count := by
  constructor
  · intro entry member
    cases member
  · intro entry member
    cases member

theorem same (entry : Entry) (count : Nat) (absent : success entry = none) : Growth entry count count := by
  simp only [Growth, absent]

private theorem monotone (entry : Entry) (before after : Nat) (growth : Growth entry before after) : before ≤ after := by
  cases selected : success entry with
  | none =>
    simp only [Growth, selected] at growth
    omega
  | some pair =>
    simp only [Growth, selected] at growth
    omega

private theorem allocated (entry : Entry) (before after : Nat) (growth : Growth entry before after)
    (raw : Pqxdh.Bytes) (handle : Nat) (selected : success entry = some (raw, handle)) :
    handle = before ∧ after = before + 1 := by
  simpa only [Growth, selected] using growth

/-- Appending the reached entry preserves all earlier handle bounds and the original raw-packet uniqueness. -/
theorem append (transcript : List Entry) (entry : Entry) (before after : Nat)
    (prior : Holds transcript before) (growth : Growth entry before after) :
    Holds (transcript ++ [entry]) after := by
  have increasing := monotone entry before after growth
  constructor
  · intro observed member raw handle selected
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact (prior.1 observed earlier raw handle selected).trans_le increasing
    · obtain ⟨rfl, rfl⟩ := allocated observed before after growth raw handle selected
      omega
  · intro left leftMember right rightMember raw other handle leftSuccess rightSuccess
    simp only [List.mem_append, List.mem_singleton] at leftMember rightMember
    rcases leftMember with leftEarlier | rfl
    · rcases rightMember with rightEarlier | rfl
      · exact prior.2 left leftEarlier right rightEarlier raw other handle leftSuccess rightSuccess
      · have bounded := prior.1 left leftEarlier raw handle leftSuccess
        have fresh := (allocated right before after growth other handle rightSuccess).1
        omega
    · rcases rightMember with rightEarlier | rfl
      · have bounded := prior.1 right rightEarlier other handle rightSuccess
        have fresh := (allocated left before after growth raw handle leftSuccess).1
        omega
      · exact congrArg Prod.fst (Option.some.inj (leftSuccess.symm.trans rightSuccess))

/-- The inductive internal receipt exposes exactly the raw-packet equality needed by public matching. -/
theorem unique_raw (transcript : List Entry) (count : Nat) (valid : Holds transcript count)
    (left : Entry) (leftMember : left ∈ transcript) (right : Entry) (rightMember : right ∈ transcript)
    (raw other : Pqxdh.Bytes) (handle : Nat)
    (leftSuccess : success left = some (raw, handle)) (rightSuccess : success right = some (other, handle)) :
    raw = other := valid.2 left leftMember right rightMember raw other handle leftSuccess rightSuccess

end BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.same

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.unique_raw' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger.unique_raw
