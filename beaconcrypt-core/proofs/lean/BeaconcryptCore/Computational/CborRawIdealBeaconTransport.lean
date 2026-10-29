-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealBeaconTrace

/-! Constructive transport from actual raw transcript witnesses to the canonical shadow. Successful raw builds identify their original complete response; late successful finishes identify the exact delegated tagged input and preserve the accept ordinal of their prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealBeaconTransport
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentIdealProvenance (BuiltIn)
open PqxdhDeploymentIdealBeacon (LateFinish)
open PqxdhDeploymentIdealParams (Target)
open CborRawIdealBeaconTrace (EntryRel Related changed)

/-- A raw successful build carries the envelope-stripped response of that exact delegated session. -/
theorem entry_build (raw canonical : Entry) (related : EntryRel raw canonical) (session : Nat)
    (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (found : raw = (⟨.inl (.inr (.build session payload)), some response⟩ : Entry)) :
    ∃ delegatedPayload original, canonical = (⟨.inl (.inr (.build session delegatedPayload)), some original⟩ : Entry) ∧
      CborPublicClient.strip original = response := by
  cases related with
  | same entry ordinary =>
      rw [found] at ordinary
      cases ordinary
  | build index rawPayload delegatedPayload reply =>
      cases reply with
      | none => cases found
      | some original =>
          cases found
          exact ⟨delegatedPayload, original, rfl, rfl⟩
  | finish => cases congrArg Entry.query found

/-- Every actual raw successful build has a successful shadow build at the same session. -/
theorem built (raw canonical : List Entry) (related : Related raw canonical) (session : Nat)
    (response : PqxdhServerRegistrationPublication.Response) (found : BuiltIn raw session response) :
    ∃ original, BuiltIn canonical session original ∧ CborPublicClient.strip original = response := by
  obtain ⟨payload, member⟩ := found
  induction related with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | member
      · obtain ⟨delegatedPayload, original, delegated, stripped⟩ := entry_build _ _ head session payload response same.symm
        exact ⟨original, ⟨delegatedPayload, List.mem_cons.mpr (Or.inl delegated.symm)⟩, stripped⟩
      · obtain ⟨original, found, stripped⟩ := ih member
        obtain ⟨delegatedPayload, present⟩ := found
        exact ⟨original, ⟨delegatedPayload, List.mem_cons.mpr (Or.inr present)⟩, stripped⟩

/-- A raw successful finish records exactly the same optional reply after its public sender tag. -/
theorem entry_finish (raw canonical : Entry) (related : EntryRel raw canonical) (owner : Nat)
    (bytes reply : Pqxdh.Bytes)
    (found : raw = (⟨.inl (.inr (.finish owner bytes)), some reply⟩ : Entry)) :
    ∃ sender, canonical = (⟨.inl (.inr (.finish owner (CborTaggedCodec.tag sender bytes))), some reply⟩ : Entry) := by
  cases related with
  | same entry ordinary =>
      rw [found] at ordinary
      cases ordinary
  | build => cases congrArg Entry.query found
  | finish owner raw sender answer =>
      cases found
      exact ⟨sender, rfl⟩

/-- Splitting an actual raw transcript splits its shadow at the same public entry boundary. -/
theorem split (raw canonical : List Entry) (related : Related raw canonical) (before after : List Entry)
    (decomposed : raw = before ++ after) :
    ∃ canonicalBefore canonicalAfter, canonical = canonicalBefore ++ canonicalAfter ∧
      Related before canonicalBefore ∧ Related after canonicalAfter := by
  induction before generalizing raw canonical with
  | nil =>
      simp only [List.nil_append] at decomposed
      subst decomposed
      exact ⟨[], canonical, rfl, .nil, related⟩
  | cons entry before ih =>
      subst decomposed
      cases related with
      | cons head tail =>
          obtain ⟨canonicalBefore, canonicalAfter, same, aligned, suffix⟩ := ih _ _ tail rfl
          exact ⟨_ :: canonicalBefore, canonicalAfter, by rw [same]; rfl, .cons head aligned, suffix⟩

/-- The actual late-finish prefix has the same number of accept attempts after delegation. -/
theorem late_finish {count : Nat} (target : Target count) (raw canonical : List Entry)
    (related : Related raw canonical) (bytes : Pqxdh.Bytes) (late : LateFinish target raw bytes) :
    ∃ sender, LateFinish target canonical (CborTaggedCodec.tag sender bytes) := by
  obtain ⟨before, reply, after, same, clock⟩ := late
  obtain ⟨canonicalBefore, canonicalAfter, decomposed, aligned, suffix⟩ := split raw canonical related before _ same
  cases suffix with
  | @cons _ delegated _ delegatedTail head tail =>
      obtain ⟨sender, tagged⟩ := entry_finish _ _ head target.kem.val bytes reply rfl
      refine ⟨sender, canonicalBefore, reply, delegatedTail, ?_, ?_⟩
      · rw [decomposed, tagged]
      · rw [← CborRawIdealProvenanceTrace.acceptCount_eq before canonicalBefore
          (CborRawIdealBeaconTrace.shape before canonicalBefore aligned)]
        exact clock

end BeaconcryptCore.Computational.CborRawIdealBeaconTransport

/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTransport.entry_build' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTransport.entry_build
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTransport.built' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTransport.built
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTransport.entry_finish' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTransport.entry_finish
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTransport.split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTransport.split
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTransport.late_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTransport.late_finish
