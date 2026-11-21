-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityStep
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh

/-! The actual adaptive suppressed program dominates the retained real trajectories through the concrete per-query coupling. The ordinary endpoint event concerns an actual accepted original field absent from the complete modified signing history. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityDomination
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentPublicationSelectionFacts (fromAudit)
open PqxdhDeploymentPublicationSuppression (Selection)
open PqxdhDeploymentPublicationSecurityCoupling
open PqxdhDeploymentPublicationSecurityFresh (NativeEvent chosen_fresh)
open PqxdhDeploymentPublicationSecuritySelection (ChosenCandidate)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- The terminal real audit identifies the captured public target; its raw accepted candidate is preserved in the complete result. -/
def CapturedCandidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (ordinal : Nat)
    (transcript : Result → List PqxdhDeploymentInterface.Entry) (outcome : Result × RealState KemSK) : Prop :=
  ∃ target, (fromAudit ordinal outcome.2.2).target = some target ∧
    ChosenCandidate setup codec (transcript outcome.1) outcome.2.1 target

/-- Concrete full-program domination uses actual source callbacks and the real modified source program, without a final containment or local-simulation premise. -/
theorem program (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (client : OracleComp (Spec KemSK) Result) (real : RealState KemSK) (modified : ModifiedState KemSK)
    (related : Related ordinal real modified) :
    Pr{let reached ← (PqxdhDeploymentPublicationDomination.monitoredRun
        (PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index) (allowed ordinal) client real true)}[reached.2 = true ∧ CapturedCandidate setup codec ordinal transcript reached.1] ≤
    Pr{let reached ← (simulateQ (PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks seed index)
      client).run modified}[NativeEvent setup codec transcript reached] := by
  apply PqxdhDeploymentPublicationDomination.monitored_domination
    (PqxdhDeploymentPublicationSuppressionTrace.handler setup codec checks seed index)
    (PqxdhDeploymentPublicationSuppressionSchedule.source setup codec checks seed index)
    (allowed ordinal) (Related ordinal) transport
    (marginal setup codec checks seed index ordinal)
    (PqxdhDeploymentPublicationSecurityStep.step setup codec checks seed index ordinal)
    (CapturedCandidate setup codec ordinal transcript) (NativeEvent setup codec transcript) ?_ client real modified related
  intro value source target connected happened
  obtain ⟨selected, captured, chosen⟩ := happened
  exact chosen_fresh setup codec (transcript value) ordinal source target connected selected
    ((congrArg Selection.target connected.2.1).trans captured) chosen

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityDomination

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityDomination.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityDomination.program
