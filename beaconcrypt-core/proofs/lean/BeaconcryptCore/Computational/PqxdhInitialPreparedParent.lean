import BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried
import BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent
import BeaconcryptCore.Computational.RawCtxSupportedSample
import BeaconcryptCore.Computational.PqxdhInitialAuditedResources

/-!
The parent sampler is the actual audited source prefix. A completed or cached branch executes the earlier original continuation and final observation before any hidden parent draw. An uncached branch retains its literal source descriptor, complete native state and chronological candidate list. Erasing only that audit reconnects both prepared games to the original full-state source execution and its cached-branch normalization.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPreparedParent
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
open PqxdhInitialNativeAuditCarried
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Pending (extra : OracleSpec ι) (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  Context extra M P I D K Result Origin S B × PqxdhInitialNativeAudit.State A N C

abbrev Output := PqxdhInitialNativeAdjacent.Output

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (observe : Output M P I D K Result Origin A N C S B → ProbComp Bool)

noncomputable def finish (stage : Nat) (cut : PqxdhInitialNativeCarried.Carried extra M P I D K Result Origin A N C S B) : ProbComp Bool :=
  PqxdhInitialNativeAdjacent.continued source writer mark sender route decode
    (PqxdhInitialNativeAudit.external pre application initial selector aux) stage cut >>= observe

noncomputable def collect (depth : Nat) (cut : Carried extra M P I D K Result Origin A N C S B) :
    ProbComp (Bool ⊕ Pending extra M P I D K Result Origin A N C S B) := by
  classical
  exact match cut with
  | .complete result state => Sum.inl <$> observe (result, state.1)
  | .pending context state =>
    if state.1.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none then pure (.inr (context, state))
    else Sum.inl <$> finish source writer pre application initial selector aux mark sender route decode observe (depth + 1) (eraseCut cut)

noncomputable def resume (stage : Nat) : Bool ⊕ Pending extra M P I D K Result Origin A N C S B → ProbComp Bool
  | .inl decision => pure decision
  | .inr (context, state) =>
    finish source writer pre application initial selector aux mark sender route decode observe stage (.pending context state.1)

/-- Completed and cached outcomes retain the exact earlier original observation; the missing branch resumes the exact saved descriptor and native state. -/
theorem collect_real (depth : Nat) (cut : Carried extra M P I D K Result Origin A N C S B) :
    (collect source writer pre application initial selector aux mark sender route decode observe depth cut >>=
      resume source writer pre application initial selector aux mark sender route decode observe (depth + 1)) =
    finish source writer pre application initial selector aux mark sender route decode observe (depth + 1) (eraseCut cut) := by
  classical
  cases cut with
  | complete result state =>
    simp [collect, resume, finish, eraseCut, PqxdhInitialNativeAdjacent.continued,
      RawCtxForwardScan.pack, RawCtxPendingMixedPrefix.finish]
  | pending context state =>
    simp only [collect]
    split <;> simp [resume, eraseCut]

open Classical in
/-- The later prepared continuation changes only an uncached cut; cached and completed decisions were already obtained from the original earlier execution. -/
theorem collect_normalized (depth : Nat) (cut : Carried extra M P I D K Result Origin A N C S B) :
    (collect source writer pre application initial selector aux mark sender route decode observe depth cut >>=
      resume source writer pre application initial selector aux mark sender route decode observe (depth + 2)) =
    if PqxdhInitialNativeRisk.Cached (eraseCut cut) then
      finish source writer pre application initial selector aux mark sender route decode observe (depth + 1) (eraseCut cut)
    else finish source writer pre application initial selector aux mark sender route decode observe (depth + 2) (eraseCut cut) := by
  classical
  cases cut with
  | complete result state =>
    simp [collect, resume, finish, eraseCut, PqxdhInitialNativeRisk.Cached,
      PqxdhInitialNativeAdjacent.continued, RawCtxForwardScan.pack, RawCtxPendingMixedPrefix.finish]
  | pending context state =>
    simp only [collect, eraseCut, PqxdhInitialNativeRisk.Cached]
    split <;> simp_all [resume]

variable (execution : Execution extra M P I D K Result Origin S B)

noncomputable def prepare (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C) :
    ProbComp (Bool ⊕ Pending extra M P I D K Result Origin A N C S B) :=
  carried source writer pre application initial selector aux mark sender route decode execution depth (depth + 1) state >>=
    collect source writer pre application initial selector aux mark sender route decode observe depth

/-- Resuming the concrete audited sampler in the earlier stage gives the exact original full-state source observation. -/
theorem prepare_real (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C) :
    (prepare source writer pre application initial selector aux mark sender route decode observe execution depth state >>=
      resume source writer pre application initial selector aux mark sender route decode observe (depth + 1)) =
    (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution
      (PqxdhInitialNativeAudit.external pre application initial selector aux) (depth + 1) state.1 >>= observe) := by
  rw [prepare, bind_assoc]
  simp only [collect_real]
  rw [← bind_map_left, carried_projection]
  simp only [finish, ← bind_assoc, PqxdhInitialNativeAdjacent.continued,
    PqxdhInitialNativeCarried.carried_finish, PqxdhInitialNativeAdjacent.run]

/-- The same concrete sampler with the later pending continuation gives exactly the original cached-branch-normalized observation. -/
theorem prepare_normalized (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C) :
    (prepare source writer pre application initial selector aux mark sender route decode observe execution depth state >>=
      resume source writer pre application initial selector aux mark sender route decode observe (depth + 2)) =
    (PqxdhInitialNativeAdjacent.normalized source writer mark sender route decode execution
      (PqxdhInitialNativeAudit.external pre application initial selector aux) depth state.1 >>= observe) := by
  classical
  rw [prepare, bind_assoc]
  simp only [collect_normalized]
  rw [PqxdhInitialNativeAdjacent.normalized,
    ← carried_projection source writer pre application initial selector aux mark sender route decode execution depth (depth + 1) state]
  simp only [bind_map_left, bind_assoc, finish, ite_bind]

/-- A prepared pending result exists exactly for its identical audited descriptor and an absent private-cache entry. -/
theorem collect_pending (depth : Nat) (cut : Carried extra M P I D K Result Origin A N C S B)
    (context : Context extra M P I D K Result Origin S B) (state : PqxdhInitialNativeAudit.State A N C) :
    Sum.inr (context, state) ∈ support (collect source writer pre application initial selector aux mark sender route decode observe depth cut) ↔
    cut = .pending context state ∧ state.1.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none := by
  classical
  cases cut with
  | complete result reached => simp [collect]
  | pending saved reached =>
    simp only [collect]
    split <;> simp_all
    all_goals grind

/-- Prepared pending support is exactly the actual audited source cut plus the checked missing-cache condition. No selected key or source history is assumed. -/
theorem supported_pending (depth : Nat) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : Context extra M P I D K Result Origin S B) :
    Sum.inr (context, reached) ∈ support
      (prepare source writer pre application initial selector aux mark sender route decode observe execution depth state) ↔
    RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer pre application initial selector aux mark sender route decode execution depth (depth + 1) state) ∧
    reached.1.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none := by
  simp only [prepare, mem_support_bind_iff, collect_pending]
  simp

/-- The concrete prepared sampler pays the original all-branch source bill and the same final observer's bill. Removing its literal resumed suffix does not transport a cost through evaluated probability equality. -/
theorem prepare_uniform (depth qPost qObserve : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (costs : PqxdhInitialParentObserverBudgets.Costs)
    (callbacks : PqxdhInitialParentObserverBudgets.ExternalUniform costs pre application initial selector aux)
    (observeBound : ∀ result, (observe result).IsTotalQueryBound qObserve)
    (state : PqxdhInitialNativeAudit.State A N C) :
    (prepare source writer pre application initial selector aux mark sender route decode observe execution depth state).IsTotalQueryBound
      (PqxdhInitialAuditedResources.uniformBudget costs qPost + qObserve) := by
  have full := PqxdhInitialNativeBudgets.source_uniform source writer (depth + 1)
    (PqxdhInitialNativeAudit.external pre application initial selector aux)
    (PqxdhInitialAuditedResources.externalBudget costs)
    (PqxdhInitialAuditedResources.local_bounds pre application initial selector aux costs callbacks)
    mark sender route decode execution qPost bounded state.1
  have totalP := isQueryBoundP_bind (full.isQueryBoundP (p := fun _ => True))
    (fun result _ => (observeBound result).isQueryBoundP (p := fun _ => True))
  have complete := (isQueryBoundP_true_iff _ _).mp totalP
  change (PqxdhInitialNativeAdjacent.run source writer mark sender route decode execution
    (PqxdhInitialNativeAudit.external pre application initial selector aux) (depth + 1) state.1 >>= observe).IsTotalQueryBound
    (PqxdhInitialAuditedResources.uniformBudget costs qPost + qObserve) at complete
  rw [← prepare_real source writer pre application initial selector aux mark sender route decode observe execution depth state] at complete
  exact complete.of_bind_left

/-- Each supported pending branch executes one actual uniform full76 predecessor draw, preserving the complete private table, cursor, log and ambient cache state. -/
theorem pending_draw (depth stage : Nat) (before : depth < stage)
    (state reached : PqxdhInitialNativeAudit.State A N C) (covered : PqxdhInitialNativeLog.Covered state.1)
    (context : Context extra M P I D K Result Origin S B)
    (supported : Sum.inr (context, reached) ∈ support
      (prepare source writer pre application initial selector aux mark sender route decode observe execution depth state)) :
    (PqxdhInitialNativeLog.handler source writer stage
      (PqxdhInitialNativeAudit.external pre application initial selector aux)
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1).run reached.1 =
    (fun output => (PqxdhInitialParentBuilderContext.reply sender route decode context.original output,
      PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) output reached.1)) <$>
        ($ᵗ PqxdhFullSecretInputKdf.FullOutput) := by
  have actual := (supported_pending source writer pre application initial selector aux mark sender route decode observe execution
    depth state reached context).mp supported
  apply PqxdhInitialNativeCarried.carried_miss source writer mark sender route decode execution depth (depth + 1) stage before
    (PqxdhInitialNativeAudit.external pre application initial selector aux) state.1 reached.1 covered context _ actual.2
  rw [← carried_projection source writer pre application initial selector aux mark sender route decode execution depth (depth + 1) state,
    support_map]
  exact ⟨.pending context reached, actual.1, rfl⟩

end BeaconcryptCore.Computational.PqxdhInitialPreparedParent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_real

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_normalized

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_real

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_normalized

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.collect_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.supported_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.supported_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.prepare_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPreparedParent.pending_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPreparedParent.pending_draw
