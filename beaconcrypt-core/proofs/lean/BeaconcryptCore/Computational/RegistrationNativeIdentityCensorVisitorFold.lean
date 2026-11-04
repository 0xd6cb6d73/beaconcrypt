-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal
/-! A public before-accept journal fold survives exactly its chronological nonpublishing prefix and counts every decoded accept attempt. No source support is converted into a probability claim here; distribution transport is supplied separately by VisitorJournal.source. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityCensorVisitorJournal (fold)
variable {S T : Type}
abbrev count (calls : List (Call TypedSpec S)) : Nat := RegistrationNativeIdentityUnissuedCutTrace.count calls

private theorem cost_eq (query : TypedSpec.Domain) :
    RegistrationNativeIdentityUnissuedCutCounter.cost query =
      if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0 := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

private theorem attempt_none (accept cursor : Nat) (query : TypedSpec.Domain)
    (room : cursor+(if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)≤accept) :
    RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor=none := by
  cases query with
  | inl coin => rfl
  | inr command => cases command with
    | accept packet =>
        simp only [RegistrationNativeIdentityCensorPublicClient.IsAccept,ite_true] at room
        simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,show cursor≠accept by omega,ite_false]
    | _ => rfl

/-- Projecting actual private snapshots changes no original public acceptance ordinal. -/
theorem count_map (observe : S → T) (calls : List (Call TypedSpec S)) :
    count (calls.map (RegistrationNativeObservedStageTrace.mapCall observe))=count calls :=
  RegistrationNativeIdentityUnissuedProjection.count_map observe calls

/-- The fold's cursor is the original journal's raw decoded-accept-attempt ordinal, including rejected callbacks. -/
theorem count_original (calls : List (Call TypedSpec S)) :
    count calls=RegistrationNativeRegistrationJournalCoverage.count RegistrationNativeRegistrationJournalCoverage.IsAccept calls :=
  RegistrationNativeIdentityUnissuedProjection.count_original calls

/-- An exact nonpublishing prefix before the chosen public ordinal advances only that original all-attempt cursor. -/
theorem advance_prefix (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept cursor : Nat) (leading trailing : List (Call TypedSpec S))
    (room : cursor+count leading≤accept)
    (quiet : ∀ call∈leading,published call.query call.reply call.after=false) :
    fold target published accept cursor (leading++trailing)=fold target published accept (cursor+count leading) trailing := by
  induction leading generalizing cursor with
  | nil => simp only [count,RegistrationNativeIdentityUnissuedCutTrace.count,List.map_nil,List.sum_nil,Nat.add_zero,List.nil_append]
  | cons call rest ih =>
      have counted : count (call::rest)=RegistrationNativeIdentityUnissuedCutCounter.cost call.query+count rest := rfl
      rw [counted,cost_eq] at room
      have missing := attempt_none accept cursor call.query (by omega)
      simp only [List.cons_append,fold,missing,quiet call List.mem_cons_self,Bool.false_eq_true,ite_false]
      have later := ih (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept call.query then 1 else 0)
        (by omega) (fun item member => quiet item (List.mem_cons_of_mem _ member))
      simpa only [counted,cost_eq,Nat.add_assoc] using later

/-- The same chosen call returns its own before-state target and literal submitted packet after every original earlier public stop has been ruled out. -/
theorem survives (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept cursor : Nat) (leading trailing : List (Call TypedSpec S)) (call : Call TypedSpec S)
    (packet : beaconcrypt_core.registration.InitPacket) (message : Pqxdh.Bytes)
    (ordinal : cursor+count leading=accept)
    (quiet : ∀ previous∈leading,published previous.query previous.reply previous.after=false)
    (queryEq : call.query=.inr (.accept packet)) (selected : target call.before=some message) :
    fold target published accept cursor (leading++call::trailing)=some (message,packet) := by
  rw [advance_prefix target published accept cursor leading (call::trailing) ordinal.le quiet,ordinal]
  rcases call with ⟨query,before,reply,after⟩
  dsimp only at queryEq selected
  subst query
  simp only [fold,RegistrationNativeIdentityCensorAdaptivePostselection.attempt,ite_true,selected,Option.map_some]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.count_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.count_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.count_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.count_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.advance_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.advance_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorFold.survives
