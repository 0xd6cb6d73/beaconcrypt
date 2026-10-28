-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySelection

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppression (Target)
open PqxdhDeploymentPublicationSuppressionTrace (Occurrence)
open PqxdhDeploymentPublicationWitness
open PqxdhDeploymentPublicationSecuritySelection
open PqxdhDeploymentPublicationSelectionFacts (occurrenceTarget)
open PqxdhDeploymentPublishedTuple (OwnerForgery PublishedForgery ownerIdentities publishedTuple)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- Equality of the public selected capability is exactly equality of its source slot and canonical one-time message. -/
theorem occurrenceTarget_eq (index : Nat) (oneTime : X25519PublicKey) (occurrence : Occurrence) :
    occurrenceTarget occurrence = (⟨index, oneTime⟩ : Target) ↔ matchesMessage index oneTime occurrence = true := by
  simp only [occurrenceTarget, Target.mk.injEq, matchesMessage, decide_eq_true_eq]

/-- The raw candidate of a real successful accept verifies under its actual native owner's generated private-service slot. -/
theorem actual_owner_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (address : Nat) (forgery : OwnerForgery setup.source.crypto codec outcome.2.1.1.2.transcript
      (ownerIdentities setup (PqxdhRegistrationJointSchedule.source outcome.2.2.1)) address) :
    ∃ entry candidate decoded, outcome.2.2.1.owners[address]? = some entry ∧
      AcceptedAt setup codec outcome.2.1.1.2.transcript outcome.2.2.1 entry.identityIndex candidate decoded ∧
      publishedTuple codec outcome.2.1.1.2.transcript address ≠ some decoded := by
  obtain ⟨raw, session, member, candidate, identity, decoded, parsed, accepted, identityFound, unpublished⟩ := forgery
  simp only [ownerIdentities, PqxdhRegistrationJointSchedule.source, List.map_map, List.getElem?_map,
    Option.map_eq_some_iff] at identityFound
  obtain ⟨entry, found, identitySame⟩ := identityFound
  change (setup.joint.publicKeys entry.owner.beacon.identity).ed25519 = identity at identitySame
  have original : (some (PqxdhDeploymentPublicationSecurityAudit.erase outcome), after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhDeploymentPublicationSecurityAudit.source, support_map]
    exact ⟨(some outcome, after), supported, rfl⟩
  have signed := PqxdhDeploymentSigningHistory.signed_source setup codec checks route ensureInit bounds mode adversary
    runtime _ original (PqxdhDeploymentPublicationSecurityAudit.erase outcome) rfl
  have seedFound : outcome.2.2.1.pool.1.seeds[entry.identityIndex]? = some entry.owner.beacon.identity :=
    (signed.owned entry (List.mem_of_getElem? found)).1
  have detached : acceptPhase1Candidate setup.joint.verify candidate =
      some ((setup.joint.publicKeys entry.owner.beacon.identity).ed25519, decoded) := by
    rw [← PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
      (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)]
    rw [identitySame]
    exact accepted
  refine ⟨entry, candidate, decoded, found, ⟨?_, ?_⟩, unpublished⟩
  · exact List.mem_filterMap.mpr ⟨_, member, parsed⟩
  · exact ⟨setup.joint.publicKeys entry.owner.beacon.identity,
      by simp only [PqxdhDynamicIdentityReports.sourceKeys, seedFound, Option.map_some], detached⟩

/-- An already-issued unpublished accepted tuple supplies the concrete bounded first-call selection and forces every matching real publication to be absent. -/
theorem actual_goodTarget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK
      (PqxdhDeploymentPublicationSecurityExecution.Result X))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : (some outcome, after) ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : outcome.2.2.1.owners[address]? = some entry) (decoded : Phase1KeyTuple)
    (issued : decoded ∈ PqxdhDeploymentPublicationAuditHistory.keysAt entry.identityIndex outcome.2.2.2)
    (unpublished : publishedTuple codec outcome.2.1.1.2.transcript address ≠ some decoded) :
    ∃ selected : Fin budget.bundle, GoodTarget selected.val outcome.2.2.2 ⟨entry.identityIndex, decoded.oneTime⟩ := by
  obtain ⟨selected, occurrence, member, ordinal, matching, earliest⟩ := actual_earliest_issued setup codec checks route
    ensureInit bounds mode adversary budget respects runtime outcome after supported entry.identityIndex decoded issued
  refine ⟨selected, occurrence, member, ordinal,
    (occurrenceTarget_eq _ _ _).mpr matching, ?_, ?_⟩
  · intro previous previousIn before same
    have matched := (occurrenceTarget_eq entry.identityIndex decoded.oneTime previous).mp same
    rw [earliest previous previousIn before] at matched
    cases matched
  · intro other otherIn same
    exact actual_matching_failed setup codec checks phase1 route ensureInit bounds mode adversary runtime outcome
      after supported address entry found decoded issued unpublished other otherIn ((occurrenceTarget_eq _ _ _).mp same)

/-- Every unrestricted actual CE publication failure is either an ordinary unissued-field event or one bounded concrete global selection. The event containment is derived from the real constructor, every failed attempt, and actual unique publication. -/
theorem actual_cover (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) (runtime : A)
    (reached : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X)
    (supported : reached ∈ support
      (PqxdhDeploymentPublicationSecurityAudit.actual setup codec checks route ensureInit bounds mode adversary runtime))
    (event : PqxdhDeploymentPublicationSecurityEvents.GameEvent setup codec
      (PqxdhDeploymentPublicationSecurityAudit.deployment reached)) :
    OrdinaryEvent setup codec reached ∨ ∃ selected : Fin budget.bundle, SelectedEvent setup codec selected.val reached := by
  rcases reached with ⟨(_ | outcome), after⟩
  · obtain ⟨created, output, final, impossible, _⟩ := event
    cases impossible
  · have forged : PublishedForgery setup.source.crypto codec outcome.2.1.1.2.transcript
        (ownerIdentities setup (PqxdhRegistrationJointSchedule.source outcome.2.2.1)) := by
      obtain ⟨created, output, final, same, forged⟩ := event
      have stateSame : final = (outcome.2.1.1.2,
          PqxdhDeploymentCompile.merge outcome.2.1.2 (PqxdhRegistrationJointSchedule.source outcome.2.2.1)) :=
        (congrArg (fun value => value.2.2) (Option.some.inj same)).symm
      rw [stateSame, PqxdhDeploymentPublishedTuple.identities_merge] at forged
      exact forged
    obtain ⟨address, forgery⟩ := (PqxdhDeploymentPublishedTuple.published_owner _ _ _ _).mp forged
    obtain ⟨entry, candidate, decoded, found, accepted, unpublished⟩ := actual_owner_accepted setup codec checks
      shortRejects route ensureInit bounds mode adversary runtime outcome after supported address forgery
    obtain ⟨publicKey, _, verified⟩ := accepted.2
    rcases actual_origin setup codec checks ensureInit none _ runtime outcome after supported entry.identityIndex
      candidate publicKey.ed25519 decoded verified with issued | unissued
    · obtain ⟨selected, good⟩ := actual_goodTarget setup codec checks phase1 route ensureInit bounds mode adversary
        budget respects runtime outcome after supported address entry found decoded issued unpublished
      exact Or.inr ⟨selected, outcome.1, outcome.2.1, outcome.2.2, rfl,
        ⟨entry.identityIndex, decoded.oneTime⟩, good, candidate, decoded, accepted, rfl⟩
    · exact Or.inl ⟨outcome.1, outcome.2.1, outcome.2.2, rfl, entry.identityIndex, candidate, decoded, accepted, unissued⟩

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.occurrenceTarget_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.occurrenceTarget_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_owner_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_owner_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_goodTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_goodTarget

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents.actual_cover
