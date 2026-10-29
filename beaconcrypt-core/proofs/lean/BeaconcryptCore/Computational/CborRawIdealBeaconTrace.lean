-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawEnvironment
import BeaconcryptCore.Computational.CborRawIdealProvenanceTrace
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon

/-! A public shadow transcript records exactly the delegated source registration calls. It changes only admitted build payloads and response envelopes, and finish-input tags. Accept and bundle bytes, successful sessions, assigned IDs and every record/secrecy reply retain their actual values. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealBeaconTrace
open PqxdhDeploymentInterface (Entry)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)
open CborRawPublicState (Public)

def changed : Entry → Bool
  | ⟨.inl (.inr (.build _ _)), _⟩ | ⟨.inl (.inr (.finish _ _)), _⟩ => true
  | _ => false

inductive EntryRel : Entry → Entry → Prop where
  | same (entry : Entry) (ordinary : changed entry = false) : EntryRel entry entry
  | build (session : Nat) (rawPayload delegatedPayload : Option Pqxdh.Bytes)
      (reply : Option PqxdhServerRegistrationPublication.Response) :
      EntryRel ⟨.inl (.inr (.build session rawPayload)), reply.map CborPublicClient.strip⟩
        ⟨.inl (.inr (.build session delegatedPayload)), reply⟩
  | finish (owner : Nat) (raw : Pqxdh.Bytes) (sender : Std.U64) (reply : Option Pqxdh.Bytes) :
      EntryRel ⟨.inl (.inr (.finish owner raw)), reply⟩
        ⟨.inl (.inr (.finish owner (CborTaggedCodec.tag sender raw))), reply⟩

abbrev Related := List.Forall₂ EntryRel

/-- The actual public adapter produces one related delegated entry, with no assumption about a successful reply. -/
theorem entry_relation (state : Public) (query : EnvQuery)
    (reply : EnvSpec.Range (CborRawEnvironment.request state query)) :
    EntryRel ⟨.inl (.inr query.val), CborRawEnvironment.reply state query reply⟩
      ⟨.inl (.inr (CborRawEnvironment.request state query).val), reply⟩ := by
  rcases query with ⟨command, valid⟩
  cases command with
  | build session payload => exact .build _ _ _ _
  | finish owner raw => exact .finish _ _ _ _
  | _ => exact .same _ rfl

theorem entry_shape (raw canonical : Entry) (related : EntryRel raw canonical) :
    CborRawIdealProvenanceTrace.entryShape raw = CborRawIdealProvenanceTrace.entryShape canonical := by
  cases related with
  | same => rfl
  | build session rawPayload delegatedPayload reply => cases reply <;> rfl
  | finish => rfl

theorem shape (raw canonical : List Entry) (related : Related raw canonical) :
    CborRawIdealProvenanceTrace.shape raw = CborRawIdealProvenanceTrace.shape canonical := by
  induction related with
  | nil => rfl
  | cons entry rest ih =>
      simp only [CborRawIdealProvenanceTrace.shape, List.filterMap_cons, entry_shape _ _ entry] at ih ⊢
      rw [ih]

theorem append (raw canonical : List Entry) (related : Related raw canonical) (entry delegated : Entry)
    (step : EntryRel entry delegated) : Related (raw ++ [entry]) (canonical ++ [delegated]) := by
  induction related with
  | nil => exact .cons step .nil
  | cons head tail ih => exact .cons head ih

/-- Accept attempts and their complete optional replies are identical in both public representations. -/
theorem entry_accept (raw canonical : Entry) (related : EntryRel raw canonical)
    (bytes : Pqxdh.Bytes) (reply : Option Nat) :
    raw = (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) ↔
      canonical = (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) := by
  cases related with
  | same => rfl
  | build => simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and]
  | finish => simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and]

/-- Bundle publication bytes are identical in both public representations. -/
theorem entry_bundle (raw canonical : Entry) (related : EntryRel raw canonical)
    (owner : Nat) (reply : Option Pqxdh.Bytes) :
    raw = (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) ↔
      canonical = (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) := by
  cases related with
  | same => rfl
  | build => simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and]
  | finish => simp only [Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and]

theorem mem_accept (raw canonical : List Entry) (related : Related raw canonical)
    (bytes : Pqxdh.Bytes) (reply : Option Nat) :
    (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) ∈ raw ↔
      (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) ∈ canonical := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, eq_comm, entry_accept _ _ head bytes reply, ih]

theorem mem_bundle (raw canonical : List Entry) (related : Related raw canonical)
    (owner : Nat) (reply : Option Pqxdh.Bytes) :
    (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) ∈ raw ↔
      (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) ∈ canonical := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, eq_comm, entry_bundle _ _ head owner reply, ih]

end BeaconcryptCore.Computational.CborRawIdealBeaconTrace

/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_relation
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_shape
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.shape
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.append
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_accept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_accept
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_bundle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.entry_bundle
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.mem_accept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.mem_accept
/-- info: 'BeaconcryptCore.Computational.CborRawIdealBeaconTrace.mem_bundle' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealBeaconTrace.mem_bundle
