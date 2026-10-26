-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost

/-! LQ-F upstream, unit B2: the later second compile lemma (U-L2), the later form of CE-11b's `PqxdhDeploymentIdealCompile.ideal_compile`. `ideal_compile_server` proves the frozen target `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget` exactly as stated: under the approved Phase 1 and Phase 2 read-back contracts, for a run-phase adversary within its budget and every post-run adversary, the logged two-slot world of item 2 (`PqxdhDeploymentLaterServerItemTargets.laterSlotGame`) with the compiled LQ-F program `PqxdhDeploymentLaterServerCompile.compileServer` at the per-target decision accepts with the same probability as the later ideal game `PqxdhDeploymentIdealLaterGame.idealLaterGame` ends with the LQ-F event and the designation `g` (`ceDecideL`).

Proof: `PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_active` (the draws, the common prefix, the key match, the dead branches and the selected-key branch, reduced to the active branch at every draw) with the active branch `PqxdhDeploymentIdealLaterPost.active_branchL` at every draw.

Premises: exactly those of the frozen target, the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` and the run-phase budget `budget.Respects first`; no post budget is taken. This is an equality of probabilities. It charges nothing and makes no security claim by itself; LQ-F claims confidentiality only, and nothing here cites T5, theorem A2 or T8. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCompile

/-- The later second compile lemma (U-L2, `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget`): `PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_active` with `PqxdhDeploymentIdealLaterPost.active_branchL` at every draw of the challenger. -/
theorem ideal_compile_server : PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget := by
  intro ι baseSpec KemSK Reader Response A X Out setup codec route checks phase1 phase2 ensureInit bounds mode first second
    budget respects event claim g runtime
  exact PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_active setup codec route checks phase1 phase2 ensureInit
    bounds mode first second budget respects event claim g runtime fun p _ =>
      PqxdhDeploymentIdealLaterPost.active_branchL setup codec route checks phase1 phase2 ensureInit bounds mode first
        second budget event claim g runtime p

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCompile

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCompile.ideal_compile_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCompile.ideal_compile_server
