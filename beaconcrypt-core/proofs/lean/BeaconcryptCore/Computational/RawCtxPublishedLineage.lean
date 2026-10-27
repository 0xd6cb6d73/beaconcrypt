import BeaconcryptCore.Computational.RawCtxPublishedRecords
import BeaconcryptCore.Computational.RawCtxFunctionalFamily
import BeaconcryptCore.Computational.RawCtxFiniteLineageCheck

/-!
One final source observation uses the original publication-gated decision, the same fixed initial directional root and target position, and all original final reveal history. Its finite lineage is evaluated under the execution's own final retained private-table view. This definition is shared by every substitution stage. It does not infer target reach from a cursor or let the checker create a publication. The concrete source cut must still prove the earlier-prefix and resumed-checker decomposition of this same event.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPublishedLineage
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxFiniteLineageCheck
variable {M P I D K A : Type} {S B : Nat}

noncomputable def step (prior : Prior) (input : RatchetChain) : RatchetChain × RatchetMaterial :=
  RawCtxInterpretedReceive.decodeResponse (RawCtxFunctionalFamily.execute prior (RawCtxChainSend.nativeRequest input))

noncomputable def lineage (prior : Prior) (root : RatchetChain) (position : Nat) : List RatchetChain :=
  trace nativeKey (step prior) position root

noncomputable def observe (source : FixedHkdfSha512NoSaltSource) (root : RatchetChain) (position : Nat)
    (ancestors disclosed : List RatchetChain)
    (result : RawCtxAdjacentCacheNormalization.Output M P I D K A Bool S B) : ProbComp Bool := by
  classical
  exact pure (result.1.1 && decide (RawCtxLiveLineage.Fresh
    (lineage (view (productionStream source.crypto) result.2.1.2.1) root position ++ ancestors)
    disclosed result.1.2.2))

/-- The final source observation retains exactly its original decision and actual full-history value freshness at the same initial-root position. -/
theorem observed (source : FixedHkdfSha512NoSaltSource) (root : RatchetChain) (position : Nat)
    (ancestors disclosed : List RatchetChain)
    (result : RawCtxAdjacentCacheNormalization.Output M P I D K A Bool S B) :
    true ∈ support (observe source root position ancestors disclosed result) ↔
      result.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (lineage (view (productionStream source.crypto) result.2.1.2.1) root position ++ ancestors)
        disclosed result.1.2.2 := by
  classical
  simp only [observe, mem_support_pure_iff, eq_comm (a := true), Bool.and_eq_true, decide_eq_true_eq]

/-- One retained full response gives its exact next-chain coordinate, with no independence or uniformity premise. -/
theorem step_next (prior : Prior) (input : PqxdhSecretInputKdf.RootOutput) :
    (step prior (RawCtxFreshChainCut.concreteChain input)).1 =
      RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain
        (prior (RawCtxFirstParentRisk.inputAddress input))) := by
  rw [step, RawCtxFunctionalFamily.execute, RawCtxFreshChainCut.decoded_parts]
  have info : PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  simp only [RawCtxKdfRequestTable.address, RawCtxChainSend.nativeRequest, info]
  change RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain
    (prior ⟨Pqxdh.INFO_R, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain input)).toList⟩)) = _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  rfl

/-- The actual cache walk splits the same full initial-root lineage into its retained earlier inputs and remaining suffix. Only the original cached bindings are required of the fixed view. -/
theorem walk_lineage (table : RawCtxKdfRequestTable.Table) (prior : Prior)
    (agrees : ∀ address output, table address = some output → prior address = output)
    (depth remaining : Nat) (root : PqxdhSecretInputKdf.RootOutput)
    (result : List PqxdhSecretInputKdf.RootOutput × PqxdhSecretInputKdf.RootOutput)
    (walked : RawCtxCursorLineage.walk table depth root = some result) :
    lineage prior (RawCtxFreshChainCut.concreteChain root) (depth + remaining) =
      result.1.map RawCtxFreshChainCut.concreteChain ++
        lineage prior (RawCtxFreshChainCut.concreteChain result.2) remaining := by
  induction depth generalizing remaining result with
  | zero =>
    simp only [RawCtxCursorLineage.walk, Option.some.injEq] at walked
    subst result
    simp only [Nat.zero_add, List.map_nil, List.nil_append]
  | succ depth ih =>
    cases earlier : RawCtxCursorLineage.walk table depth root with
    | none => simp [RawCtxCursorLineage.walk, earlier] at walked
    | some reached =>
      cases found : table (RawCtxFirstParentRisk.inputAddress reached.2) with
      | none => simp [RawCtxCursorLineage.walk, earlier, found] at walked
      | some output =>
        have same : (reached.1 ++ [reached.2], PqxdhOrderedChainHybrids.nextChain output) = result := by
          simpa [RawCtxCursorLineage.walk, earlier, found] using walked
        subst result
        rw [show depth + 1 + remaining = depth + (remaining + 1) by omega, ih (remaining + 1) reached earlier]
        simp only [lineage, trace, step_next, agrees _ output found, List.map_append,
          List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]

/-- The same finite path remains the actual prefix under every final cache extension, including all later source requests and repeated cache hits. -/
theorem retained_lineage (fallback : Prior) (before after : RawCtxKdfRequestTable.Table)
    (extension : RawCtxCursorLineage.Extends before after)
    (depth remaining : Nat) (root : PqxdhSecretInputKdf.RootOutput)
    (result : List PqxdhSecretInputKdf.RootOutput × PqxdhSecretInputKdf.RootOutput)
    (walked : RawCtxCursorLineage.walk before depth root = some result) :
    lineage (view fallback after) (RawCtxFreshChainCut.concreteChain root) (depth + remaining) =
      result.1.map RawCtxFreshChainCut.concreteChain ++
        lineage (view fallback after) (RawCtxFreshChainCut.concreteChain result.2) remaining := by
  apply walk_lineage before (view fallback after) _ depth remaining root result walked
  intro address output known
  simp only [view, extension address output known, Option.getD_some]

/-- The retained-parent checker uses exactly this same fixed private view, including the complete parent entry. -/
theorem retained_step (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) :
    step (lookup prior entry target) = RawCtxSelectedParentTable.nativeStep prior entry target := rfl

/-- Splitting at an actual cached prefix changes neither the final blocked values nor their comparison with the complete original disclosure history. -/
theorem fresh_split (fallback : Prior) (before after : RawCtxKdfRequestTable.Table)
    (extension : RawCtxCursorLineage.Extends before after)
    (depth remaining : Nat) (root : PqxdhSecretInputKdf.RootOutput)
    (result : List PqxdhSecretInputKdf.RootOutput × PqxdhSecretInputKdf.RootOutput)
    (walked : RawCtxCursorLineage.walk before depth root = some result)
    (ancestors disclosed : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    RawCtxLiveLineage.Fresh
      (lineage (view fallback after) (RawCtxFreshChainCut.concreteChain root) (depth + remaining) ++ ancestors)
      disclosed history ↔
    RawCtxLiveLineage.Fresh
      (lineage (view fallback after) (RawCtxFreshChainCut.concreteChain result.2) remaining ++
        (result.1.map RawCtxFreshChainCut.concreteChain ++ ancestors)) disclosed history := by
  rw [retained_lineage fallback before after extension depth remaining root result walked]
  simp only [RawCtxLiveLineage.Fresh, RawCtxLiveLineage.FreshValues, List.mem_append]
  aesop

/-- The source-position model and the finite checker use the same extracted complete-response decoder. -/
theorem step_model {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (prior : Prior) (input : RatchetChain) :
    step prior input =
      ((withInterpreter cr (RawCtxFunctionalFamily.execute prior)).kdfChain input,
        (withInterpreter cr (RawCtxFunctionalFamily.execute prior)).kdfMsg input) := rfl

/-- The final blocked value is the actual material key at the original directional record position. -/
theorem material_mem {AD PT CT : Type} (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (prior : Prior) (root : RatchetChain) (position : Nat) :
    nativeKey (Ratchet.msgKeyAt (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) root position) ∈
      lineage prior root position := by
  induction position generalizing root with
  | zero => exact List.mem_cons_of_mem _ List.mem_cons_self
  | succ position ih =>
    simp only [lineage, trace]
    apply List.mem_cons_of_mem
    simpa only [lineage, Ratchet.msgKeyAt, Ratchet.chainAt, Function.iterate_succ_apply, step_model cr prior root] using ih (step prior root).1

/-- This analysis observation samples no random bytes. Its finite private-function evaluations and list work remain explicit local computation. -/
theorem observe_uniform (source : FixedHkdfSha512NoSaltSource) (root : RatchetChain) (position : Nat)
    (ancestors disclosed : List RatchetChain)
    (result : RawCtxAdjacentCacheNormalization.Output M P I D K A Bool S B) :
    (observe source root position ancestors disclosed result).IsTotalQueryBound 0 := by
  trivial

end BeaconcryptCore.Computational.RawCtxPublishedLineage

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.observed

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.step_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.step_next

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.walk_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.walk_lineage

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.retained_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.retained_lineage

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.retained_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.retained_step

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.fresh_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.fresh_split

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.step_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.step_model

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.material_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.material_mem

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedLineage.observe_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedLineage.observe_uniform
