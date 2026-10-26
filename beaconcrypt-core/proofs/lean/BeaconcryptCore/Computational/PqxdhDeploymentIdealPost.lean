-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood

/-!
# The active branch (CE-11b, unit U6)

The active branch of the second compile lemma (`PqxdhDeploymentIdealActive.ActiveBranch`): on every active cut of the experiment, item 2's post-challenge phase and the CE side from the selected accept's steps after encapsulation decide `true` with the same probability. `active_branch` proves it for every draw of the challenger, under the approved Phase 1 and Phase 2 read-back contracts, from `PqxdhDeploymentIdealPostReduce.activeBranch_of_middle` with the CE side of the middle invariant `PqxdhDeploymentIdealPostGood.GoodMid` (`middleInv`, `middleStart`).

This is an equality in law under the approved codec contracts. It charges nothing and makes no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPost
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed)

section Branch
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The active branch of the second compile lemma at every draw of the challenger, under the approved Phase 1 and Phase 2 read-back contracts: `PqxdhDeploymentIdealPostReduce.activeBranch_of_middle` with the CE side of the middle invariant `PqxdhDeploymentIdealPostGood.GoodMid`. -/
theorem active_branch (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {A : Type} (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (event : Observed X → Bool) (claim : Observed X → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (p : Params KemSK budget.create) :
    PqxdhDeploymentIdealActive.ActiveBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary
      budget event claim g runtime p :=
  PqxdhDeploymentIdealPostReduce.activeBranch_of_middle setup codec route checks ensureInit bounds mode adversary budget
    event claim g runtime p (fun _ => PqxdhDeploymentIdealPostGood.GoodMid setup codec (Target.ofCE budget g))
    (fun created => PqxdhDeploymentIdealPostGood.middleInv setup codec route checks phase1 phase2 (Target.ofCE budget g) p
      created)
    (PqxdhDeploymentIdealPostGood.middleStart setup codec route checks ensureInit bounds mode adversary budget g runtime p)

end Branch

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPost

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPost.active_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPost.active_branch
