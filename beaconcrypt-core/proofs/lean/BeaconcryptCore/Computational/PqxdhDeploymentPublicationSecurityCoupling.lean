-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityTransport
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySelection
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination

/-! Concrete one-sided coupling of the original deployment scheduler with the actual selected-message suppression program. Physical state is preserved on retained trajectories. The target challenger retains every earlier query and skips only complete selected future signing blocks. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentPublicationSuppression (Selection Target)
open PqxdhDeploymentPublicationSuppressionTrace (Audit)
open PqxdhDeploymentPublicationSelectionFacts (targetAt fromAudit)
open PqxdhDeploymentPublicationHistoryRebase (replaceHistory rebase)
open PqxdhDeploymentPublicationSuppressionFreshness (Fresh)
open PqxdhDeploymentPublicationSuppressionHistory (Armed)
open PqxdhDeploymentPublicationAuditBounds (Valid)
open PqxdhDeploymentPublicationSecurityTransport (queryTransport)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

abbrev RealState (KemSK : Type) := PqxdhDeploymentPublicationSuppressionTrace.State KemSK
abbrev ModifiedState (KemSK : Type) := PqxdhDeploymentPublicationSuppressionSchedule.State KemSK
abbrev Spec (KemSK : Type) := PqxdhRegistrationJointRevealSchedule.Spec KemSK

/-- Both executions retain identical private seeds, KEM state, shared protocol state and owner state. Only actual signing-query histories may differ. -/
def Physical (real modified : PqxdhRegistrationJointSchedule.State KemSK) : Prop :=
  replaceHistory [] real = replaceHistory [] modified

/-- Before selection the executions are identical. After capture the modified history has never signed the fixed selected message. -/
def Related (ordinal : Nat) (real : RealState KemSK) (modified : ModifiedState KemSK) : Prop :=
  Valid real.2 ∧ modified.2 = fromAudit ordinal real.2 ∧ Physical real.1 modified.1 ∧
    (modified.2.target = none → modified.1 = real.1) ∧
    (∀ target, modified.2.target = some target → Armed target modified)

/-- Retain a real bundle branch only when a suppressed reply was genuinely failure and the selected first message was absent before its signing block. All source draws still execute in the monitored original experiment. -/
noncomputable def allowed (ordinal : Nat) (query : (Spec KemSK).Domain) (before : RealState KemSK)
    (outcome : (Spec KemSK).Range query × RealState KemSK) : Bool := by
  classical
  exact match query with
  | .inl (.inr (.bundle _)) =>
      let prepared := targetAt outcome.2.2.occurrences before.2.nextBundle
      decide (((fromAudit ordinal before.2).next prepared).blocks prepared = true → outcome.1 = none) &&
        decide (∀ target, before.2.nextBundle = ordinal → prepared = some target → Fresh target before.1.pool.1)
  | _ => true

def transport (query : (Spec KemSK).Domain) (real : RealState KemSK) (modified : ModifiedState KemSK) :=
  queryTransport query real modified.1.pool.1.transcript modified.2

theorem physical_replace (real modified : PqxdhRegistrationJointSchedule.State KemSK)
    (physical : Physical real modified) : replaceHistory modified.pool.1.transcript real = modified := by
  have equal := congrArg (replaceHistory modified.pool.1.transcript) physical
  simpa only [Physical, replaceHistory] using equal

theorem physical_rebase (real : PqxdhRegistrationJointSchedule.State KemSK)
    (original replacement : PqxdhDeploymentPublicationHistoryRebase.History) :
    Physical real (rebase original replacement real) := rfl

/-- The initial relation has identical complete source state and no captured message. -/
theorem initial (ordinal : Nat) (native : PqxdhRegistrationJointSchedule.State KemSK) :
    Related ordinal (native, Audit.empty) (native, Selection.initial ordinal) := by
  refine ⟨PqxdhDeploymentPublicationAuditBounds.valid_empty,
    (PqxdhDeploymentPublicationSelectionFacts.fromAudit_empty ordinal).symm, rfl, fun _ => rfl, ?_⟩
  intro target captured
  simp only [Selection.initial, reduceCtorEq] at captured

/-- The actual modified interpreter supplies the full local marginal of this concrete transport. No final-event or codec assumption is required. -/
theorem marginal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified) :
    transport query real modified <$>
      (PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real =
      (PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks seed index query).run modified := by
  have same := physical_replace real.1 modified.1 related.2.2.1
  simpa only [transport, same] using
    PqxdhDeploymentPublicationSecurityTransport.query_transport setup codec checks seed index query real
      modified.1.pool.1.transcript modified.2 related.1.1

/-- Erasing the real private audit retains an actually supported original callback. -/
theorem native_supported (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (Spec KemSK).Domain) (real : RealState KemSK)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (supported : outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real)) :
    (outcome.1, outcome.2.1) ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed index query).run real.1) := by
  rw [← PqxdhDeploymentPublicationSuppressionTrace.query_source setup codec checks seed index query real,
    support_map]
  exact ⟨outcome, supported, rfl⟩

/-- Every shared-draw transport outcome is an actual complete modified callback outcome. -/
theorem modified_supported (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (Spec KemSK).Domain)
    (real : RealState KemSK) (modified : ModifiedState KemSK) (related : Related ordinal real modified)
    (outcome : (Spec KemSK).Range query × RealState KemSK)
    (supported : outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index query).run real)) :
    transport query real modified outcome ∈ support
      ((PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks seed index query).run modified) := by
  rw [← marginal setup codec checks seed index ordinal query real modified related, support_map]
  exact ⟨outcome, supported, rfl⟩

/-- A previously absent capability can be captured only by the selected prepared call. -/
theorem capture (selection : Selection) (prepared : Option Target) (target : Target)
    (absent : selection.target = none) (captured : (selection.next prepared).target = some target) :
    selection.pending = some 0 ∧ prepared = some target ∧
      (selection.next prepared).pending = none ∧ (selection.next prepared).blocks prepared = true := by
  cases pending : selection.pending with
  | none => simp [Selection.next, Selection.advance, pending, absent] at captured
  | some remaining =>
    cases remaining with
    | zero =>
        have same : prepared = some target := by
          simpa only [Selection.next, Selection.advance, pending, ite_true] using captured
        exact ⟨rfl, same, by simp [Selection.next, Selection.advance, pending],
          by simp [Selection.next, Selection.advance, pending, same, Selection.blocks]⟩
    | succ remaining => simp [Selection.next, Selection.advance, pending, absent] at captured

/-- A zero audit-derived countdown is precisely the selected global call ordinal. -/
theorem selected_ordinal (ordinal : Nat) (audit : Audit)
    (selected : (fromAudit ordinal audit).pending = some 0) : audit.nextBundle = ordinal := by
  simp only [fromAudit, PqxdhDeploymentPublicationSelectionFacts.pendingAt] at selected
  split at selected
  · simp only [Option.some.injEq] at selected
    omega
  · cases selected

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.physical_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.physical_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.physical_rebase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.physical_rebase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.initial

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.marginal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.native_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.native_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.modified_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.modified_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.capture' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.capture

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.selected_ordinal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling.selected_ordinal
