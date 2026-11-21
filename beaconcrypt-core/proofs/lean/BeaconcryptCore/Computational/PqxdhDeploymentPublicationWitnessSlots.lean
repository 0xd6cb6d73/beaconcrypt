-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAudit
import BeaconcryptCore.Computational.PqxdhDeploymentSigningHistory

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhRegistrationJointOwnership (Entry)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- Every recorded occurrence still names an actual final owner at its original address and private identity slot. -/
def Linked (state : State KemSK) : Prop :=
  ∀ occurrence ∈ state.2.occurrences, ∃ entry,
    state.1.owners[occurrence.ownerAddress]? = some entry ∧ entry.identityIndex = occurrence.identityIndex

private theorem set_slot (owners : List (Entry KemSK)) (address called : Nat) (entry old : Entry KemSK)
    (found : owners[called]? = some entry) (oldFound : owners[address]? = some old)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    ∃ current, (owners.set called { entry with owner := owner })[address]? = some current ∧
      current.identityIndex = old.identityIndex := by
  by_cases same : called = address
  · subst called
    have equal : entry = old := Option.some.inj (found.symm.trans oldFound)
    subst old
    exact ⟨{ entry with owner := owner }, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, rfl⟩
  · exact ⟨old, by rw [List.getElem?_set_ne same]; exact oldFound, rfl⟩

/-- Source commands append new owner addresses or update only an existing owner's role; they never reuse an existing address's identity slot. -/
theorem query_slot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (address : Nat) (entry : Entry KemSK)
    (found : state.owners[address]? = some entry)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state)) :
    ∃ current, result.2.owners[address]? = some current ∧ current.identityIndex = entry.identityIndex := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case create pin keyId =>
      simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create,
        StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨material, _, rfl⟩ := supported
      refine ⟨entry, ?_, rfl⟩
      rw [PqxdhRegistrationJointSchedule.created,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
      exact found
    case bundle called =>
      cases calledFound : state.owners[called]? with
      | none =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle,
          StateT.run, calledFound, mem_support_pure_iff] at supported
        subst result
        exact ⟨entry, found, rfl⟩
      | some calledEntry =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle,
          StateT.run, calledFound, support_map, Set.mem_image] at supported
        obtain ⟨returned, _, rfl⟩ := supported
        exact set_slot state.owners address called calledEntry entry calledFound found returned.1.1.2
    case finish called raw =>
      cases calledFound : state.owners[called]? with
      | none =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish,
          StateT.run, calledFound, mem_support_pure_iff] at supported
        subst result
        exact ⟨entry, found, rfl⟩
      | some calledEntry =>
        simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
          PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish,
          StateT.run, calledFound, support_map, Set.mem_image] at supported
        obtain ⟨returned, _, rfl⟩ := supported
        exact set_slot state.owners address called calledEntry entry calledFound found returned.1.2
    all_goals
      exact ⟨entry, by rw [(PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl
        state result supported).owners]; exact found, rfl⟩
  all_goals
    exact ⟨entry, by rw [(PqxdhDeploymentSigningHistory.quiet_step setup codec checks seed serverIndex _ rfl
      state result supported).owners]; exact found, rfl⟩

private theorem record_linked (state : State KemSK) (after : PqxdhRegistrationJointSchedule.State KemSK)
    (held : Linked state) (address index : Nat) (reply : Option Pqxdh.Bytes)
    (tuples : List PqxdhEd25519EufCma.Phase1KeyTuple)
    (kept : ∀ (oldAddress : Nat) (oldEntry : Entry KemSK), state.1.owners[oldAddress]? = some oldEntry →
      ∃ current, after.owners[oldAddress]? = some current ∧ current.identityIndex = oldEntry.identityIndex)
    (current : ∃ entry, after.owners[address]? = some entry ∧ entry.identityIndex = index) :
    Linked (after, state.2.record address index reply tuples) := by
  intro occurrence member
  rcases List.mem_append.mp member with old | added
  · obtain ⟨oldEntry, found, sameIndex⟩ := held occurrence old
    obtain ⟨newEntry, newFound, same⟩ := kept _ oldEntry found
    exact ⟨newEntry, newFound, same.trans sameIndex⟩
  · obtain ⟨keys, _, rfl⟩ := List.mem_map.mp added
    exact current

private theorem after_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) (held : Linked state) (entry : Entry KemSK)
    (found : state.1.owners[address]? = some entry) (generated : Option PqxdhJointGapDh.ScalarBytes) :
    let returned := PqxdhRegistrationJointBundle.after setup codec entry.identityIndex entry.owner generated state.1.pool.1
    Linked (⟨(returned.2, state.1.pool.2), state.1.shared,
      state.1.owners.set address { entry with owner := returned.1.2 },
      Function.update state.1.inits address
        (PqxdhRegistrationJointBundle.afterLog setup codec entry.owner generated (state.1.inits address))⟩,
      state.2.record address entry.identityIndex returned.1.1
        (PqxdhRegistrationJointAttemptTrace.issued setup entry.owner generated)) := by
  apply record_linked state _ held address entry.identityIndex
  · intro oldAddress oldEntry oldFound
    exact set_slot state.1.owners oldAddress address entry oldEntry found oldFound _
  · exact ⟨{ entry with owner := _ }, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, rfl⟩

/-- Every actual prepared trace records the source owner lookup that is reinstalled at the same public address. -/
theorem trace_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) (held : Linked state) (entry : Entry KemSK)
    (found : state.1.owners[address]? = some entry)
    (result : (PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × Audit) ×
      Option PqxdhEd25519EufCma.Phase1Candidate)
    (supported : result ∈ support (traceLogged setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2
      (state.1.inits address))) :
    Linked (⟨(result.1.1.2, state.1.pool.2), state.1.shared,
      state.1.owners.set address { entry with owner := result.1.1.1.2 },
      Function.update state.1.inits address result.2⟩, result.1.2) := by
  simp only [traceLogged] at supported
  cases phase : entry.owner.beacon.phase <;> simp only [phase] at supported
  case fresh =>
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after_linked setup codec address state held entry found (some scalar)
  all_goals
    simp only [mem_support_pure_iff] at supported
    subst result
    first
    | exact after_linked setup codec address state held entry found none
    | simpa only [PqxdhRegistrationJointBundle.after, PqxdhRegistrationJointBundle.afterLog,
        PqxdhBeaconPhase1Publication.prepare,
        PqxdhRegistrationJointAttemptTrace.issued, phase, Option.map_none, Option.toList_none] using
        after_linked setup codec address state held entry found none

/-- Missing, inactive, failed and successful bundle calls keep every previous occurrence's actual slot/address receipt. -/
theorem bundle_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (state : State KemSK) (held : Linked state) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) : Linked result.2 := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, mem_support_pure_iff] at supported
    subst result
    simpa only [Linked, Audit.record, List.map_nil, List.append_nil] using held
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, rfl⟩ := supported
    exact trace_linked setup codec address state held entry found returned member

/-- Every source command preserves the concrete occurrence/address relation, using only actual owner append and role-update semantics. -/
theorem query_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (held : Linked state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed serverIndex query).run state)) : Linked result.2 := by
  by_cases bundled : ∃ address, query = .inl (.inr (.bundle address))
  · obtain ⟨address, rfl⟩ := bundled
    exact bundle_linked setup codec address state held result supported
  · have same : handler setup codec checks seed serverIndex query =
        onSource (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query) := by
      rcases query with (coin | request) | read
      · rfl
      · cases request
        case bundle address => exact False.elim (bundled ⟨address, rfl⟩)
        all_goals rfl
      · rfl
    rw [same] at supported
    simp only [onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, rfl⟩ := supported
    intro occurrence present
    obtain ⟨old, oldFound, oldIndex⟩ := held occurrence present
    obtain ⟨current, found, indexSame⟩ := query_slot setup codec checks seed serverIndex query state.1
      occurrence.ownerAddress old oldFound returned member
    exact ⟨current, found, indexSame.trans oldIndex⟩

/-- The complete adaptive source program retains the actual address and identity slot of every historical occurrence. -/
theorem program_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (held : Linked state) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed serverIndex) program).run state)) :
    Linked result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ Linked
    (fun query current previous reached member => query_linked setup codec checks seed serverIndex query current
      previous reached member) program state held result supported

/-- The actual initialized audit derives address/slot coherence from its empty chronological audit, with no caller relation premise. -/
theorem initialized_linked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) : Linked outcome.2.2 := by
  simp only [PqxdhDeploymentPublicationSecurityAudit.initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, _, continued⟩ := supported
  · simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨executed, member, equal⟩ := continued
    have same : outcome = (PqxdhRegistrationJointServerBirth.encode created, executed.1, executed.2) :=
      (Option.some.inj (congrArg Prod.fst equal)).symm
    rw [same]
    exact program_linked setup codec checks created.seed created.server.server.metadata.identityIndex program _
      (by intro occurrence present; cases present) executed member

/-- In the actual full deployment execution, matching identity slots identify the same public owner address. This uses the already derived source distinctness invariant and allows arbitrary failed bundle calls. -/
theorem actual_address (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (address : Nat) (entry : Entry KemSK) (found : outcome.2.2.1.owners[address]? = some entry)
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences)
    (sameIndex : occurrence.identityIndex = entry.identityIndex) : occurrence.ownerAddress = address := by
  obtain ⟨current, currentFound, currentIndex⟩ := initialized_linked setup codec checks ensureInit none _ runtime
    outcome after supported occurrence member
  have original : (some (PqxdhDeploymentPublicationSecurityAudit.erase outcome), after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhDeploymentPublicationSecurityAudit.source, support_map]
    exact ⟨(some outcome, after), supported, rfl⟩
  have signed := PqxdhDeploymentSigningHistory.signed_source setup codec checks route ensureInit bounds mode adversary
    runtime _ original (PqxdhDeploymentPublicationSecurityAudit.erase outcome) rfl
  exact signed.distinct occurrence.ownerAddress address current entry currentFound found (currentIndex.trans sameIndex)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.query_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.query_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.trace_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.trace_linked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.bundle_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.bundle_linked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.query_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.query_linked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.program_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.program_linked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.initialized_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.initialized_linked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.actual_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots.actual_address
