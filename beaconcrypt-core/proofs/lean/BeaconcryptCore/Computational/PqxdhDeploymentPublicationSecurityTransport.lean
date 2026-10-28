-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionSchedule
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionHistory

/-! Shared-draw local transports for real and publication-suppressed bundle operations. A replacement identity history retains its complete earlier prefix; only the current nonsuppressed signing block is appended. No earlier query is retroactively removed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDynamicIdentityPool (SourceState)
open PqxdhDeploymentPublicationSuppression (Selection Target)
open PqxdhDeploymentPublicationSuppressionTrace (Audit)
open PqxdhDeploymentPublicationSelectionFacts (targetAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

abbrev IdentityHistory := List PqxdhDynamicIdentityPool.Observation

def poolWithHistory (history : IdentityHistory) (state : SourceState) : SourceState :=
  { state with transcript := history }

def rebasePool (before : SourceState) (history : IdentityHistory) (after : SourceState) : SourceState :=
  poolWithHistory (history ++ after.transcript.drop before.transcript.length) after

/-- Replacing an old signing-history prefix keeps the whole actual bundle result and appends exactly its real current-call observations. -/
theorem bundle_after_rebase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : SourceState) (history : IdentityHistory) :
    PqxdhRegistrationJointBundle.after setup codec index owner generated (poolWithHistory history pool) =
      (fun result => (result.1, rebasePool pool history result.2))
        (PqxdhRegistrationJointBundle.after setup codec index owner generated pool) := by
  unfold PqxdhRegistrationJointBundle.after
  cases prepared : PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => simp [rebasePool, poolWithHistory]
  | some prepared =>
      dsimp only
      split <;>
        simp [rebasePool, poolWithHistory, PqxdhJointPhase1SourceWriter.signedState,
          PqxdhJointPhase1SourceWriter.recordSign, PqxdhDynamicIdentityPool.record, List.append_assoc]

/-- The prepared public target is exactly the one-time message of the tuple that the real source audit appends. -/
theorem current_issued (setup : Setup baseSpec KemSK) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes) :
    PqxdhDeploymentPublicationSuppression.nativeCurrent setup index owner generated =
      ((PqxdhBeaconPhase1Publication.prepare owner generated).map (PqxdhRegistrationJointAttemptTrace.keys setup)).map
        (fun keys => (⟨index, keys.oneTime⟩ : Target)) := by
  simp only [PqxdhDeploymentPublicationSuppression.nativeCurrent, PqxdhDeploymentPublicationSuppression.current,
    PqxdhRegistrationJointAttemptTrace.keys, Option.map_map, Function.comp_def, PqxdhRegistrationSchedule.projection]

/-- Even a rejected writer retains the exact prepared public target in the private actual occurrence audit. -/
theorem recorded_current (setup : Setup baseSpec KemSK) (index address : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes) (audit : Audit)
    (reply : Option Pqxdh.Bytes) (past : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle) :
    targetAt (audit.record address index reply
      (PqxdhRegistrationJointAttemptTrace.issued setup owner generated)).occurrences audit.nextBundle =
      PqxdhDeploymentPublicationSuppression.nativeCurrent setup index owner generated := by
  rw [PqxdhRegistrationJointAttemptTrace.issued,
    PqxdhDeploymentPublicationSelectionFacts.targetAt_record audit audit.nextBundle address index reply _ past,
    current_issued]
  simp only [ite_true]

/-- Transport one realized actual signing attempt to the modified interpreter. The current block is skipped as a whole when selected, otherwise its exact delta appends to the untouched earlier target history. -/
def localTransport (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : SourceState)
    (history : IdentityHistory) (selection : Selection) (prepared : Option Target)
    (result : PqxdhDeploymentPublicationSuppression.NativeResult KemSK) :
    PqxdhDeploymentPublicationSuppression.NativeResult KemSK × Selection :=
  let next := selection.next prepared
  if next.blocks prepared then (((none, owner), poolWithHistory history pool), next)
  else ((result.1, rebasePool pool history result.2), next)

/-- The local transport is the literal modified source operation, including its exact earlier oracle-query history. -/
theorem after_transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : SourceState) (history : IdentityHistory) (selection : Selection) :
    localTransport owner pool history selection
      (PqxdhDeploymentPublicationSuppression.nativeCurrent setup index owner generated)
      (PqxdhRegistrationJointBundle.after setup codec index owner generated pool) =
      PqxdhDeploymentPublicationSuppression.after setup codec index owner generated (poolWithHistory history pool)
        selection := by
  simp only [localTransport, PqxdhDeploymentPublicationSuppression.after, bundle_after_rebase]

/-- The actual one-time draw, prepared public tuple and every real optional writer result provide the full marginal of the executable suppressed bundle. -/
theorem trace_transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : SourceState) (history : IdentityHistory)
    (selection : Selection) (audit : Audit)
    (past : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle) :
    (fun result => localTransport owner pool history selection
        (targetAt result.2.occurrences audit.nextBundle) result.1) <$>
      PqxdhDeploymentPublicationSuppressionTrace.trace setup codec address index owner pool audit =
      PqxdhDeploymentPublicationSuppression.trace setup codec index owner (poolWithHistory history pool) selection := by
  rw [PqxdhDeploymentPublicationSuppressionTrace.trace_after]
  cases phase : owner.beacon.phase
  case fresh =>
    simp only [PqxdhDeploymentPublicationSuppression.trace, phase, Functor.map_map]
    congr 1
    funext scalar
    rw [recorded_current setup index address owner (some scalar) audit _ past]
    exact after_transport setup codec index owner (some scalar) pool history selection
  case freshWithCoins =>
    simp only [PqxdhDeploymentPublicationSuppression.trace, phase, map_pure]
    congr 1
    rw [recorded_current setup index address owner none audit _ past]
    exact after_transport setup codec index owner none pool history selection
  all_goals
    have unprepared : PqxdhBeaconPhase1Publication.prepare owner none = none := by
      simp [PqxdhBeaconPhase1Publication.prepare, phase]
    have absent := PqxdhDeploymentPublicationSelectionFacts.targetAt_future audit.occurrences audit.nextBundle
      audit.nextBundle past le_rfl
    simp only [PqxdhDeploymentPublicationSuppression.trace, phase, map_pure,
      Audit.record, List.map_nil, List.append_nil, localTransport, absent,
      PqxdhDeploymentPublicationSuppression.Selection.blocks, Bool.false_eq_true, ite_false,
      PqxdhDeploymentPublicationSuppression.after, PqxdhDeploymentPublicationSuppression.nativeCurrent,
      PqxdhDeploymentPublicationSuppression.current, unprepared, Option.map_none,
      PqxdhRegistrationJointBundle.after, rebasePool, poolWithHistory, List.drop_length, List.append_nil]

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

/-- Transport an actual whole scheduler bundle outcome, preserving its actual draw and all nonsuppressed state changes. -/
def bundleTransport (before : PqxdhDeploymentPublicationSuppressionTrace.State KemSK)
    (replacement : IdentityHistory) (selection : Selection)
    (outcome : Option Pqxdh.Bytes × PqxdhDeploymentPublicationSuppressionTrace.State KemSK) :
    Option Pqxdh.Bytes × PqxdhDeploymentPublicationSuppressionSchedule.State KemSK :=
  let prepared := targetAt outcome.2.2.occurrences before.2.nextBundle
  let next := selection.next prepared
  if next.blocks prepared then
    (none, (PqxdhDeploymentPublicationHistoryRebase.replaceHistory replacement before.1, next))
  else (outcome.1,
    (PqxdhDeploymentPublicationHistoryRebase.rebase before.1.pool.1.transcript replacement outcome.2.1, next))

/-- The full audited real bundle maps exactly to the actual source-backed modified bundle, for arbitrary earlier target histories and every real optional writer branch. -/
theorem bundle_transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : PqxdhDeploymentPublicationSuppressionTrace.State KemSK) (replacement : IdentityHistory)
    (selection : Selection)
    (past : ∀ occurrence ∈ state.2.occurrences, occurrence.ordinal < state.2.nextBundle) :
    bundleTransport state replacement selection <$>
      (PqxdhDeploymentPublicationSuppressionTrace.bundle setup codec address).run state =
      (PqxdhDeploymentPublicationSuppressionSchedule.bundle setup codec address).run
        (PqxdhDeploymentPublicationHistoryRebase.replaceHistory replacement state.1, selection) := by
  cases found : state.1.owners[address]? with
  | none =>
      have absent := PqxdhDeploymentPublicationSelectionFacts.targetAt_future state.2.occurrences state.2.nextBundle
        state.2.nextBundle past le_rfl
      simp [PqxdhDeploymentPublicationSuppressionTrace.bundle, PqxdhDeploymentPublicationSuppressionSchedule.bundle,
        PqxdhDeploymentPublicationHistoryRebase.replaceHistory, StateT.run, found, bundleTransport,
        Audit.record, absent, Selection.blocks, PqxdhDeploymentPublicationHistoryRebase.rebase]
  | some entry =>
      simp only [PqxdhDeploymentPublicationSuppressionTrace.bundle,
        PqxdhDeploymentPublicationSuppressionSchedule.bundle, StateT.run,
        PqxdhDeploymentPublicationHistoryRebase.replaceHistory, found, Functor.map_map]
      change _ = (fun result : PqxdhDeploymentPublicationSuppression.NativeResult KemSK × Selection =>
        (result.1.1.1, ((⟨(result.1.2, state.1.pool.2), state.1.shared,
          state.1.owners.set address { entry with owner := result.1.1.2 }⟩ : PqxdhRegistrationJointSchedule.State KemSK), result.2))) <$>
        PqxdhDeploymentPublicationSuppression.trace setup codec entry.identityIndex entry.owner
          (poolWithHistory replacement state.1.pool.1) selection
      rw [← trace_transport setup codec address entry.identityIndex entry.owner state.1.pool.1 replacement selection
        state.2 past]
      simp only [Functor.map_map]
      congr 1
      funext outcome
      simp only [bundleTransport, localTransport]
      split
      · simp only [poolWithHistory]
        rw [show ({ entry with owner := entry.owner } : PqxdhRegistrationJointOwnership.Entry KemSK) = entry from rfl,
          set_same state.1.owners address entry found]
        rfl
      · rfl

/-- The full real reply and poststate determine the actual modified step. Only selected bundle replies are replaced by failure; every other callback appends its exact real suffix after the retained target prefix. -/
def queryTransport (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (before : PqxdhDeploymentPublicationSuppressionTrace.State KemSK) (replacement : IdentityHistory)
    (selection : Selection)
    (outcome : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
      PqxdhDeploymentPublicationSuppressionTrace.State KemSK) :
    (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
      PqxdhDeploymentPublicationSuppressionSchedule.State KemSK :=
  match query with
  | .inl (.inr (.bundle _)) => bundleTransport before replacement selection outcome
  | _ => (outcome.1,
      (PqxdhDeploymentPublicationHistoryRebase.rebase before.1.pool.1.transcript replacement outcome.2.1, selection))

theorem queryTransport_nonbundle (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)))
    (before : PqxdhDeploymentPublicationSuppressionTrace.State KemSK) (replacement : IdentityHistory)
    (selection : Selection) :
    queryTransport query before replacement selection = fun outcome =>
      (outcome.1, (PqxdhDeploymentPublicationHistoryRebase.rebase before.1.pool.1.transcript replacement outcome.2.1,
        selection)) := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case bundle address => exact False.elim (notBundle address rfl)
    all_goals rfl
  · rfl

private theorem nonbundle_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notBundle : ∀ address, query ≠ .inl (.inr (.bundle address))) :
    PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query =
      PqxdhDeploymentPublicationSuppressionTrace.onSource
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query) := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case bundle address => exact False.elim (notBundle address rfl)
    all_goals rfl
  · rfl

/-- The complete per-query modified marginal is supplied by the actual source interpreter, including all identities, KEM operations, Server DH annotations and source continuations. No codec or cryptographic law is assumed. -/
theorem query_transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhDeploymentPublicationSuppressionTrace.State KemSK) (replacement : IdentityHistory)
    (selection : Selection)
    (past : ∀ occurrence ∈ state.2.occurrences, occurrence.ordinal < state.2.nextBundle) :
    queryTransport query state replacement selection <$>
      (PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run state =
      (PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks seed index query).run
        (PqxdhDeploymentPublicationHistoryRebase.replaceHistory replacement state.1, selection) := by
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    exact bundle_transport setup codec address state replacement selection past
  · have notBundle : ∀ address, query ≠ .inl (.inr (.bundle address)) :=
      fun address equal => bundled ⟨address, equal⟩
    rw [queryTransport_nonbundle query notBundle,
      nonbundle_real setup codec checks seed index query notBundle,
      PqxdhDeploymentPublicationSuppressionHistory.nonbundle_source setup codec checks seed index query notBundle]
    have changed := congrArg (Functor.map (fun result :
      (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK =>
        (result.1, (result.2, selection))))
      (PqxdhDeploymentPublicationHistoryRebase.source_query_rebase setup codec checks seed index query replacement state.1)
    simpa only [PqxdhDeploymentPublicationSuppressionTrace.onSource,
      PqxdhDeploymentPublicationSuppressionSchedule.onSource, StateT.run, Functor.map_map] using changed

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.bundle_after_rebase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.bundle_after_rebase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.current_issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.current_issued

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.recorded_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.recorded_current

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.after_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.after_transport

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.trace_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.trace_transport

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.bundle_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.bundle_transport

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.queryTransport_nonbundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.queryTransport_nonbundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.query_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport.query_transport
