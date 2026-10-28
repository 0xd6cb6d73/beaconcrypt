-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds

/-! Concrete one-step facts needed by adaptive publication suppression. A failed real bundle rolls back every physical native coordinate while retaining its real private signing observations. Selection reconstruction reads the same actual prepared audit, including every missing and inactive call position. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentPublicationHistoryRebase (replaceHistory)
open PqxdhDeploymentPublicationSelectionFacts (fromAudit targetAt)
open PqxdhDeploymentPublicationSecurityTransport (bundleTransport queryTransport)
open PqxdhDeploymentPublicationAuditBounds (Valid)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

private theorem set_same {Value : Type} (values : List Value) (index : Nat) (value : Value)
    (found : values[index]? = some value) : values.set index value = values := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      rfl
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      exact congrArg (List.cons head) (ih index found)

private theorem trace_failure_owner (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec index owner pool))
    (failed : result.1.1 = none) : result.1.2 = owner := by
  rcases PqxdhDeploymentSigningHistory.trace_cases setup codec index owner pool result supported with same |
    ⟨_, _, _, rejected | ⟨_, published, _, _, _⟩⟩
  · rw [same]
  · exact congrArg Prod.snd rejected
  · rw [failed] at published
    cases published

/-- A failed actual bundle preserves every physical native field. Its only possible private change is the retained identity signing transcript. -/
theorem bundle_failure_rollback (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) (failed : result.1 = none) :
    replaceHistory [] result.2.1 = replaceHistory [] state.1 := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    have original : returned.1 ∈ support (PqxdhRegistrationJointBundle.trace setup codec entry.identityIndex
        entry.owner state.1.pool.1) := by
      rw [← trace_source setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2, support_map]
      exact ⟨returned, member, rfl⟩
    have sameOwner := trace_failure_owner setup codec entry.identityIndex entry.owner state.1.pool.1 returned.1 original failed
    have sameSeeds := PqxdhRegistrationJointServerSchedule.bundle_seeds setup codec entry.identityIndex entry.owner
      state.1.pool.1 returned.1 original
    change (⟨((⟨returned.1.2.seeds, []⟩ : PqxdhDynamicIdentityPool.SourceState), state.1.pool.2),
      state.1.shared, state.1.owners.set address { entry with owner := returned.1.1.2 }⟩ :
      PqxdhRegistrationJointSchedule.State KemSK) = _
    rw [sameOwner, sameSeeds,
      show ({ entry with owner := entry.owner } : PqxdhRegistrationJointOwnership.Entry KemSK) = entry from rfl,
      set_same state.1.owners address entry found]
    rfl

private theorem short_list_option (tuples : List Phase1KeyTuple) (bounded : tuples.length ≤ 1) :
    ∃ keys : Option Phase1KeyTuple, tuples = keys.toList := by
  cases tuples with
  | nil => exact ⟨none, rfl⟩
  | cons first tail =>
    cases tail with
    | nil => exact ⟨some first, rfl⟩
    | cons second rest => simp only [List.length_cons] at bounded; omega

/-- Each actual public bundle records zero or one tuple under its complete call position and actual reply. -/
theorem bundle_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    ∃ (index : Nat) (keys : Option Phase1KeyTuple),
      result.2.2 = state.2.record address index result.1 keys.toList := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨0, none, rfl⟩
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, same⟩ := supported
    subst result
    obtain ⟨tuples, bounded, recorded⟩ := PqxdhDeploymentPublicationAuditBounds.trace_record setup codec address
      entry.identityIndex entry.owner state.1.pool.1 state.2 returned member
    obtain ⟨keys, sameKeys⟩ := short_list_option tuples bounded
    exact ⟨entry.identityIndex, keys, sameKeys ▸ recorded⟩

private theorem bundleTransport_selection (state : State KemSK)
    (replacement : PqxdhDeploymentPublicationHistoryRebase.History)
    (selection : PqxdhDeploymentPublicationSuppression.Selection) (result : Option Pqxdh.Bytes × State KemSK) :
    (bundleTransport state replacement selection result).2.2 =
      selection.next (targetAt result.2.2.occurrences state.2.nextBundle) := by
  unfold bundleTransport
  dsimp only
  split <;> rfl

/-- The modified bundle's literal selection state is exactly reconstructed from the real chronological audit, on every supported branch. -/
theorem bundle_selection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (valid : Valid state.2) (replacement : PqxdhDeploymentPublicationHistoryRebase.History)
    (ordinal : Nat) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    (bundleTransport state replacement (fromAudit ordinal state.2) result).2.2 = fromAudit ordinal result.2.2 := by
  rw [bundleTransport_selection]
  obtain ⟨index, keys, recorded⟩ := bundle_record setup codec address state result supported
  rw [recorded, PqxdhDeploymentPublicationSelectionFacts.targetAt_record state.2 state.2.nextBundle address index
    result.1 keys valid.1]
  simp only [ite_true]
  exact PqxdhDeploymentPublicationSelectionFacts.fromAudit_record state.2 ordinal address index result.1 keys valid.1

/-- Every actual source query leaves the transport's selected capability equal to the same audit-derived countdown. -/
theorem query_selection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (valid : Valid state.2) (replacement : PqxdhDeploymentPublicationHistoryRebase.History)
    (ordinal : Nat) (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) :
    (queryTransport query state replacement (fromAudit ordinal state.2) result).2.2 = fromAudit ordinal result.2.2 := by
  rcases query with (coin | request) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    rfl
  · cases request
    case bundle address => exact bundle_selection setup codec address state valid replacement ordinal result supported
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      rfl
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    rfl

/-- The real audited source reply retains every prior identity observation and only appends current-query observations. -/
theorem query_history_extension (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) :
    ∃ delta, result.2.1.pool.1.transcript = state.1.pool.1.transcript ++ delta := by
  have original : (result.1, result.2.1) ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state.1) := by
    rw [← query_source setup codec checks seed serverIndex query state, support_map]
    exact ⟨result, supported, rfl⟩
  exact PqxdhDeploymentPublicationHistoryRebase.source_query_extension setup codec checks seed serverIndex query state.1
    (result.1, result.2.1) original

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_failure_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_failure_rollback

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.bundle_selection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.query_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.query_selection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.query_history_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStepFacts.query_history_extension
