-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFiniteCover
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents
/-! The original causal Unissued witness selects a literal original field at its same projected chronological before-signing log. No before-cut identity lookup or private stopping predicate is introduced. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (mapCall)
variable {S T : Type}

/-- Snapshot projection preserves every public accept ordinal. -/
theorem count_map (observe : S → T) (calls : List (Call TypedSpec S)) :
    RegistrationNativeIdentityUnissuedCutTrace.count (calls.map (mapCall observe)) =
      RegistrationNativeIdentityUnissuedCutTrace.count calls := by
  simp only [RegistrationNativeIdentityUnissuedCutTrace.count,List.map_map]
  rfl

/-- The cutoff ordinal is exactly the original journal's decoded-accept attempt ordinal. -/
theorem count_original (calls : List (Call TypedSpec S)) :
    RegistrationNativeIdentityUnissuedCutTrace.count calls =
      RegistrationNativeRegistrationJournalCoverage.count RegistrationNativeRegistrationJournalCoverage.IsAccept calls := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
      cases query : call.query with
      | inl coin => simp_all [RegistrationNativeIdentityUnissuedCutTrace.count,
          RegistrationNativeIdentityUnissuedCutCounter.cost,RegistrationNativeRegistrationJournalCoverage.count,
          RegistrationNativeRegistrationJournalCoverage.IsAccept]
      | inr command =>
          cases command <;> simp_all [RegistrationNativeIdentityUnissuedCutTrace.count,
            RegistrationNativeIdentityUnissuedCutCounter.cost,RegistrationNativeRegistrationJournalCoverage.count,
            RegistrationNativeRegistrationJournalCoverage.IsAccept]
          omega

private theorem marked_query (call : Call TypedSpec S) (packet : beaconcrypt_core.registration.InitPacket)
    (session : Nat) (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply = some (.accept packet (some session))) :
    call.query = .inr (.accept packet) := by
  rcases call with ⟨query,before,reply,after⟩
  cases query with
  | inl coin => cases marked
  | inr command => cases command <;> simp_all [RegistrationNativeRawRegistrationJournal.typedMark]

/-- Projection keeps the exact original submitted packet and its chronological before-state at the same accept attempt ordinal. -/
theorem at_projected (observe : S → T) (leading trailing : List (Call TypedSpec S))
    (call : Call TypedSpec S) (packet : beaconcrypt_core.registration.InitPacket)
    (queryEq : call.query = .inr (.accept packet)) :
    (RegistrationNativeIdentityUnissuedCutTrace.accepted
      ((leading ++ call :: trailing).map (mapCall observe)))[RegistrationNativeIdentityUnissuedCutTrace.count leading]? =
      some (packet,observe call.before) := by
  rcases call with ⟨query,before,reply,after⟩
  dsimp only at queryEq
  subst query
  rw [List.map_append,List.map_cons,←count_map observe leading]
  exact RegistrationNativeIdentityUnissuedCutTrace.accepted_at
    (leading.map (mapCall observe)) (trailing.map (mapCall observe)) packet (observe before) (observe after) reply

variable {n count : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole)

/-- An original causal Unissued witness uses its own field, final generated identity and original before-signing history after snapshot projection. The handle may have been created later and public keys may alias. -/
theorem attempt (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (budget : PqxdhDeploymentInterface.Budget)
    (calls : List (Call TypedSpec (Whole n KemSK Platform source)))
    (final : Whole n KemSK Platform source)
    (selected : RegistrationNativePlatformIdentityCtxCausalAttempt.Attempt joint wire budget calls final)
    (unissued : RegistrationNativePlatformIdentityCtxFiniteCover.Unissued selected)
    (keys : Fin count → PqxdhJointIdentity.PublicIdentity) (identity : Fin count)
    (handleEq : identity.val = selected.finalOwner.identity.handle)
    (publicEq : (keys identity).ed25519 = selected.finalOwner.identity.publicIdentity.ed25519)
    (coherent : RegistrationNativeIdentityUnissuedObserved.Coherent selected.call.before) :
    ∃ tag : Fin 3, RegistrationNativeIdentityUnissuedEvents.At joint keys identity
      (RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal selected).val tag
      ((),(final.1,calls.map (mapCall Prod.fst))) := by
  obtain ⟨forgery,member,valid,fresh⟩ := unissued
  have observed : RegistrationNativePlatformIdentityCtxFirstBundleCut.messages selected.finalOwner.identity.handle selected.call.before =
      RegistrationNativeIdentityUnissuedEvents.observedMessages identity.val selected.call.before.1.2 := by
    rw [handleEq]
    exact RegistrationNativeIdentityUnissuedObserved.messages_eq _ _ coherent
  rw [observed] at fresh
  rw [←publicEq] at valid
  obtain ⟨tag,field⟩ := RegistrationNativeIdentityUnissuedEvents.field_cover joint keys identity selected.packet selected.call.before.1 forgery member valid fresh
  refine ⟨tag,selected.packet,selected.call.before.1,?_,field⟩
  change (RegistrationNativeIdentityUnissuedCutTrace.accepted (calls.map (mapCall Prod.fst)))[RegistrationNativeRegistrationJournalCoverage.count RegistrationNativeRegistrationJournalCoverage.IsAccept selected.leading]? = _
  have captured := at_projected Prod.fst selected.leading selected.trailing selected.call selected.packet (marked_query _ _ _ selected.marked)
  simpa only [←selected.split,count_original] using captured

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.count_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.count_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.count_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.count_original
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.at_projected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.at_projected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection.attempt
