-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEvents

/-! A decodable accept's ordinal identifies its unique original transcript position. Failed authentication replies count at the same position; session handles do not enter the ordinal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal
open RegistrationNativeInterface (Entry)
open RegistrationNativeEvents (parsedAccept parsedAcceptCount)
open RegistrationNativeWire (Wire)

/-- Two counted entries at the same counted prefix ordinal occupy the same complete list position. -/
theorem counted_unique {Item : Type} (predicate : Item → Bool)
    (before : List Item) (entry : Item) (after : List Item)
    (otherBefore : List Item) (otherEntry : Item) (otherAfter : List Item)
    (same : before ++ entry :: after = otherBefore ++ otherEntry :: otherAfter)
    (counted : (before.filter predicate).length = (otherBefore.filter predicate).length)
    (admitted : predicate entry = true) (otherAdmitted : predicate otherEntry = true) :
    before = otherBefore ∧ entry = otherEntry ∧ after = otherAfter := by
  induction before generalizing otherBefore with
  | nil =>
      cases otherBefore with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at same
          exact ⟨rfl, same.1, same.2⟩
      | cons first rest =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
          rw [← same.1, List.filter_cons_of_pos admitted] at counted
          simp only [List.filter_nil, List.length_nil, List.length_cons] at counted
          omega
  | cons first rest ih =>
      cases otherBefore with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
          rw [same.1, List.filter_cons_of_pos otherAdmitted] at counted
          simp only [List.filter_nil, List.length_nil, List.length_cons] at counted
          omega
      | cons otherFirst otherRest =>
          simp only [List.cons_append, List.cons.injEq] at same
          obtain ⟨rfl, tail⟩ := same
          have counts : (rest.filter predicate).length = (otherRest.filter predicate).length := by
            cases selected : predicate first <;> simp only [List.filter_cons, selected,
              Bool.false_eq_true, ite_false, ite_true, List.length_cons] at counted <;> omega
          obtain ⟨rfl, rfl, rfl⟩ := ih otherRest tail counts
          exact ⟨rfl, rfl, rfl⟩

/-- The same parsed-accept ordinal identifies the exact raw packet and reply in the original native ledger. -/
theorem accept_unique (wire : Wire)
    (before : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat) (after : List Entry)
    (otherBefore : List Entry) (otherRaw : Pqxdh.Bytes) (otherReply : Option Nat) (otherAfter : List Entry)
    (same : before ++ Entry.mk (.inl (.inr (.accept raw))) reply :: after =
      otherBefore ++ Entry.mk (.inl (.inr (.accept otherRaw))) otherReply :: otherAfter)
    (counted : parsedAcceptCount wire before = parsedAcceptCount wire otherBefore)
    (decoded : (RegistrationNativeWire.readInit wire raw).isSome)
    (otherDecoded : (RegistrationNativeWire.readInit wire otherRaw).isSome) :
    before = otherBefore ∧ raw = otherRaw ∧ reply = otherReply ∧ after = otherAfter := by
  obtain ⟨prefixEq, entryEq, suffixEq⟩ := counted_unique (parsedAccept wire) before _ after otherBefore _ otherAfter
    same counted decoded otherDecoded
  have queryEq := congrArg Entry.query entryEq
  simp only [Sum.inl.injEq, Sum.inr.injEq,
    RegistrationNativeInterface.Command.accept.injEq] at queryEq
  subst otherRaw
  cases entryEq
  exact ⟨prefixEq, rfl, rfl, suffixEq⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal.counted_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal.counted_unique
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal.accept_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedOrdinal.accept_unique
