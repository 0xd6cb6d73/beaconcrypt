-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPost

/-!
# The second compile lemma (CE-11b, unit U6)

CE-11b's second compile lemma `ideal_compile`: under the approved Phase 1 and Phase 2 read-back contracts, for every adversary within its budget, the probability that the decision of item 2's slot game with the compiled full game is `true` equals the probability that the event happens with the designation `g` in the ideal game of CE-11b. It is `PqxdhDeploymentIdealActive.ideal_compile_of_active` with the active branch `PqxdhDeploymentIdealPost.active_branch` at every draw of the challenger.

This is an equality of probabilities under the approved codec contracts and the adversary's budget. It charges nothing and makes no security claim by itself.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed)

section Compile
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- CE-11b's second compile lemma, under the approved Phase 1 and Phase 2 read-back contracts: the decision of item 2's slot game with the compiled full game is `true` with the probability that the event happens with the designation `g` in the ideal game (`PqxdhDeploymentIdealActive.ideal_compile_of_active` with `PqxdhDeploymentIdealPost.active_branch`). -/
theorem ideal_compile {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun outcome => decide (PqxdhDeploymentKemTransfer.happens event
          (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true} :=
  PqxdhDeploymentIdealActive.ideal_compile_of_active setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime fun p _ =>
      PqxdhDeploymentIdealPost.active_branch setup codec route checks phase1 phase2 ensureInit bounds mode adversary
        budget event claim g runtime p

end Compile

end BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile.ideal_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile.ideal_compile
