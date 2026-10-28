-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityAuditBounds
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSelectionFacts

/-! Final-transcript events for the unrestricted publication reduction. An ordinary event has an original unissued field. The other event selects the first global bundle call issuing an unpublished one-time message; every matching real call failed. These are analysis events on the original complete run, rather than assumptions on the deployment. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySelection
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppression (Target)
open PqxdhDeploymentPublicationSuppressionTrace (Audit)
open PqxdhDeploymentPublicationSelectionFacts (occurrenceTarget)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The selected global call is the first occurrence of its private slot and one-time key, and none of its occurrences publishes a bundle. -/
def GoodTarget (ordinal : Nat) (audit : Audit) (target : Target) : Prop :=
  ∃ occurrence ∈ audit.occurrences,
    occurrence.ordinal = ordinal ∧ occurrenceTarget occurrence = target ∧
    (∀ prior ∈ audit.occurrences, prior.ordinal < ordinal → occurrenceTarget prior ≠ target) ∧
    (∀ other ∈ audit.occurrences, occurrenceTarget other = target → other.reply = none)

/-- A literal successful acceptance candidate belongs to the actual generated identity at this exact private source slot. -/
def AcceptedAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (native : PqxdhRegistrationJointSchedule.State KemSK)
    (index : Nat) (candidate : Phase1Candidate) (decoded : Phase1KeyTuple) : Prop :=
  candidate ∈ PqxdhDeploymentProvenance.acceptedCandidates codec transcript ∧
    ∃ publicKey, PqxdhDynamicIdentityReports.sourceKeys setup.joint native.pool.1.seeds index = some publicKey ∧
      acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded)

/-- The accepted candidate carries exactly the one-time field whose signing block is suppressed. -/
def ChosenCandidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (native : PqxdhRegistrationJointSchedule.State KemSK)
    (target : Target) : Prop :=
  ∃ candidate decoded, AcceptedAt setup codec transcript native target.identityIndex candidate decoded ∧
    decoded.oneTime = target.oneTime

/-- An actual acceptance has an original valid field absent from the complete real signing history. -/
def OrdinaryEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X) : Prop :=
  ∃ created result state, outcome.1 = some (created, result, state) ∧
    ∃ index candidate decoded, AcceptedAt setup codec result.1.2.transcript state.1 index candidate decoded ∧
      PqxdhRegistrationJointAttemptOrigin.Unissued state.1 index candidate

/-- A final provenance failure supplied an already-issued but never-published one-time message, selected by its first actual global bundle-call position. -/
def SelectedEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (ordinal : Nat)
    (outcome : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X) : Prop :=
  ∃ created result state, outcome.1 = some (created, result, state) ∧
    ∃ target, GoodTarget ordinal state.2 target ∧
      ChosenCandidate setup codec result.1.2.transcript state.1 target

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySelection
