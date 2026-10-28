-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditHistoryInitialized
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAuditBounds
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessSlots
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditUnique

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentPublicationAuditHistory (keysAt)
open PqxdhRegistrationJointIssuedAttempts (history)
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- The selected capability is a service creation slot and canonical one-time public message; it contains no private identity seed. -/
def matchesMessage (index : Nat) (oneTime : X25519PublicKey) (occurrence : Occurrence) : Bool :=
  decide (occurrence.identityIndex = index ∧ occurrence.keys.oneTime = oneTime)

/-- A tuple in a source slot's chronological history has an actual global prepared-call occurrence. -/
theorem mem_keysAt (index : Nat) (audit : Audit) (keys : Phase1KeyTuple) :
    keys ∈ keysAt index audit ↔ ∃ occurrence ∈ audit.occurrences,
      occurrence.identityIndex = index ∧ occurrence.keys = keys := by
  simp only [keysAt, List.mem_filterMap]
  constructor
  · rintro ⟨occurrence, member, matched⟩
    split at matched
    · exact ⟨occurrence, member, ‹occurrence.identityIndex = index›, Option.some.inj matched⟩
    · cases matched
  · rintro ⟨occurrence, member, sameIndex, sameKeys⟩
    exact ⟨occurrence, member, by simp only [sameIndex, ite_true, sameKeys]⟩

/-- An actual issued tuple has a bounded earliest public bundle ordinal matching its canonical one-time message. Missing and inactive public calls remain counted in that ordinal. -/
theorem actual_earliest_issued (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (index : Nat) (keys : Phase1KeyTuple) (issued : keys ∈ keysAt index outcome.2.2.2) :
    ∃ (selected : Fin budget.bundle) (occurrence : Occurrence), occurrence ∈ outcome.2.2.2.occurrences ∧
      occurrence.ordinal = selected.val ∧ matchesMessage index keys.oneTime occurrence = true ∧
      ∀ previous ∈ outcome.2.2.2.occurrences, previous.ordinal < selected.val →
        matchesMessage index keys.oneTime previous = false := by
  obtain ⟨occurrence, member, sameIndex, sameKeys⟩ := (mem_keysAt index outcome.2.2.2 keys).mp issued
  exact PqxdhDeploymentPublicationSecurityAudit.actual_earliest setup codec checks route ensureInit bounds mode adversary
    budget respects runtime outcome after supported (matchesMessage index keys.oneTime)
    ⟨occurrence, member, by simp [matchesMessage, sameIndex, sameKeys]⟩

/-- Before the earliest matching global occurrence, the selected canonical one-time message is absent from every audited signing prefix. -/
theorem earliest_unissued (audit before : Audit) (index ordinal : Nat) (oneTime : X25519PublicKey)
    (earliest : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < ordinal →
      matchesMessage index oneTime occurrence = false)
    (beforePrefix : ∀ occurrence ∈ before.occurrences,
      occurrence ∈ audit.occurrences ∧ occurrence.ordinal < ordinal) :
    oneTimeMessage oneTime ∉ history (keysAt index before) := by
  intro present
  obtain ⟨keys, issued, sameKey⟩ := (PqxdhRegistrationJointIssuedAttempts.oneTime_member oneTime _).mp present
  obtain ⟨occurrence, member, sameIndex, sameKeys⟩ := (mem_keysAt index before keys).mp issued
  have blocked := earliest occurrence (beforePrefix occurrence member).1 (beforePrefix occurrence member).2
  have matched : matchesMessage index oneTime occurrence = true := by
    simp only [matchesMessage, decide_eq_true_eq]
    exact ⟨sameIndex, sameKeys ▸ sameKey.symm⟩
  rw [matched] at blocked
  cases blocked

/-- Literal signing/audit equality transfers earliest-occurrence freshness into the actual original private source history. -/
theorem earliest_source_fresh (audit before : Audit) (index ordinal : Nat) (oneTime : X25519PublicKey)
    (pool : PqxdhDynamicIdentityPool.SourceState)
    (exactHistory : messagesAt index pool.transcript = history (keysAt index before))
    (earliest : ∀ occurrence ∈ audit.occurrences, occurrence.ordinal < ordinal →
      matchesMessage index oneTime occurrence = false)
    (beforePrefix : ∀ occurrence ∈ before.occurrences,
      occurrence ∈ audit.occurrences ∧ occurrence.ordinal < ordinal) :
    oneTimeMessage oneTime ∉ messagesAt index pool.transcript := by
  rw [exactHistory]
  exact earliest_unissued audit before index ordinal oneTime earliest beforePrefix

/-- The full actual constructor ledger gives every service slot immutable prekey and KEM fields, including an unused slot with an empty attempt list. -/
theorem actual_fixed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) (index : Nat) :
    ∃ prekey pqKey, PqxdhRegistrationJointIssuedAttempts.Fixed prekey pqKey (keysAt index outcome.2.2.2) := by
  obtain ⟨ledger, valid, exactAttempts⟩ :=
    PqxdhDeploymentPublicationAuditHistoryInitialized.constructor_witness setup codec checks ensureInit supplied
      program runtime outcome after supported
  rw [← exactAttempts index]
  cases recorded : ledger index with
  | none =>
    refine ⟨List.Vector.replicate 32 0, List.Vector.replicate 1184 0, ?_⟩
    simp only [PqxdhRegistrationJointAttemptInvariant.attempts, recorded, Option.map_none, Option.getD_none]
    intro keys member
    cases member
  | some receipt =>
    refine ⟨receipt.prekey, receipt.pqKey, ?_⟩
    simpa only [PqxdhRegistrationJointAttemptInvariant.attempts, recorded, Option.map_some, Option.getD_some] using
      valid.fixed index receipt recorded

/-- An accepted tuple in an actual audited source run either was attempted at that exact service slot or has an unissued original attached field. No successful-publication or failed-call exclusion is used. -/
theorem actual_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      ((PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (index : Nat) (candidate : Phase1Candidate) (identity : Ed25519PublicKey) (decoded : Phase1KeyTuple)
    (accepted : acceptPhase1Candidate setup.joint.verify candidate = some (identity, decoded)) :
    decoded ∈ keysAt index outcome.2.2.2 ∨
      PqxdhRegistrationJointAttemptOrigin.Unissued outcome.2.2.1 index candidate := by
  classical
  by_cases issued : decoded ∈ keysAt index outcome.2.2.2
  · exact Or.inl issued
  · right
    obtain ⟨prekey, pqKey, fixed⟩ := actual_fixed setup codec checks ensureInit supplied program runtime outcome after
      supported index
    have exactHistory := PqxdhDeploymentPublicationAuditHistoryInitialized.initialized_history setup codec checks
      ensureInit supplied program runtime outcome after supported index
    by_contra noField
    apply issued
    apply PqxdhRegistrationJointIssuedAttempts.accepted_origin setup.joint identity candidate decoded _ prekey pqKey fixed accepted
    intro field member
    have all : ∀ field ∈ PqxdhJointPhase1Reports.candidateFields candidate,
        field.message ∈ messagesAt index outcome.2.2.1.pool.1.transcript := by
      simpa only [PqxdhRegistrationJointAttemptOrigin.Unissued, not_exists, not_and, not_not] using noField
    rw [← exactHistory]
    exact all field member

/-- Every attempt at the selected owner and one-time message returned no bundle. A successful occurrence would be that owner's unique actual published tuple, contradicting the accepted tuple's publication mismatch. -/
theorem actual_matching_failed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : outcome.2.2.1.owners[address]? = some entry) (decoded : Phase1KeyTuple)
    (issued : decoded ∈ keysAt entry.identityIndex outcome.2.2.2)
    (unpublished : PqxdhDeploymentPublishedTuple.publishedTuple codec outcome.2.1.1.2.transcript address ≠ some decoded)
    (occurrence : Occurrence) (member : occurrence ∈ outcome.2.2.2.occurrences)
    (matching : matchesMessage entry.identityIndex decoded.oneTime occurrence = true) : occurrence.reply = none := by
  have pair : occurrence.identityIndex = entry.identityIndex ∧ occurrence.keys.oneTime = decoded.oneTime :=
    decide_eq_true_eq.mp matching
  obtain ⟨prekey, pqKey, fixed⟩ := actual_fixed setup codec checks ensureInit none _ runtime outcome after supported
    entry.identityIndex
  have occurrenceIn : occurrence.keys ∈ keysAt entry.identityIndex outcome.2.2.2 :=
    (mem_keysAt _ _ _).mpr ⟨occurrence, member, pair.1, rfl⟩
  have sameKeys := PqxdhDeploymentPublicationFacts.fixed_tuple_eq prekey pqKey _ fixed occurrence.keys decoded
    occurrenceIn issued pair.2
  have sameAddress := PqxdhDeploymentPublicationWitnessSlots.actual_address setup codec checks route ensureInit
    bounds mode adversary runtime outcome after supported address entry found occurrence member pair.1
  cases reply : occurrence.reply with
  | none => rfl
  | some bytes =>
    have published := PqxdhDeploymentPublicationSecurityAudit.actual_occurrence_publishedTuple setup codec checks
      phase1 route ensureInit bounds mode adversary runtime outcome after supported occurrence member bytes reply
    rw [sameAddress, sameKeys] at published
    exact False.elim (unpublished published)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.mem_keysAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.mem_keysAt

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_earliest_issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_earliest_issued

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.earliest_unissued' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.earliest_unissued

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.earliest_source_fresh' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.earliest_source_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_matching_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness.actual_matching_failed
