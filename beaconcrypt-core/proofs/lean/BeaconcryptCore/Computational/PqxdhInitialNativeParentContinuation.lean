import BeaconcryptCore.Computational.PqxdhInitialNativeRetained
import BeaconcryptCore.Computational.PqxdhInitialNativeResponse
import BeaconcryptCore.Computational.PqxdhInitialNativeAudit
import BeaconcryptCore.Computational.RawCtxRetainedParentBackend

/-!
The actual full source continuation after a selected parent response is realized by the original retained-parent native interpreter and its material-only origin-aware context. Tuple reassociation retains the shared primitive state, additional private state and root cache. The initializer remains the same earlier-root service; the new parent next-chain coordinate is not substituted into it.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation
open PqxdhOrderedChainHybrids PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialNativeLog RawCtxSelectedParentTable RawCtxSelectedParentEntry
open PqxdhInitialNativeRetained (RetainedState)
variable {ι M P I D K X Response Shared Result Origin A N C α β : Type} {extra : OracleSpec ι} {S B : Nat}

/-- This is only a reassociation of all three original ambient state components. -/
def ambient (work : Ambient A N C α) : StateT (RetainedState A N C) ProbComp α := fun state =>
  (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$> work (state.1, state.2.1) state.2.2

/-- A pure original result preserves all ambient state. -/
theorem ambient_pure (value : α) : ambient (pure value : Ambient A N C α) = pure value := rfl

/-- Reassociation keeps the complete original sequence of ambient effects. -/
theorem ambient_bind (work : Ambient A N C α) (next : α → Ambient A N C β) :
    ambient (work >>= next) = (ambient work >>= fun value => ambient (next value)) := by
  funext state
  change (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
      (work (state.1, state.2.1) state.2.2 >>= fun first => next first.1.1 first.1.2 first.2) =
      (((fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
        work (state.1, state.2.1) state.2.2) >>= fun first =>
          (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
            next first.1 (first.2.1, first.2.2.1) first.2.2.2)
  simp only [map_bind, bind_map_left]

/-- The complete original program is unchanged by the same ambient reassociation. -/
theorem ambient_program {δ : Type} {spec : OracleSpec δ}
    (impl : QueryImpl spec (Ambient A N C)) (client : OracleComp spec α) :
    simulateQ (fun query => ambient (impl query)) client = ambient (simulateQ impl client) := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ambient_bind, ih]

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : Prior) (entry : Entry) (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The actual complete retained callback is exactly the existing native parent interpreter with the unchanged original initializer, not a supplied callback equation. -/
theorem retained_handler :
    PqxdhInitialNativeRetained.retained (S := S) (B := B) source writer (lookup prior entry target)
      (PqxdhInitialNativeAudit.external pre application initial selector aux) =
      (fun query => ambient (PqxdhInitialParentPost.nativeHandler source writer prior entry target
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux query)) := by
  funext query
  cases query with
  | inl query =>
      unfold PqxdhInitialNativeRetained.retained
      rw [RawCtxRetainedParentBackend.retained_live]
      cases query with
      | inr input => rfl
      | inl pending =>
          funext state
          change (fun result => (result.1, (result.2, state.2))) <$>
            (RawCtxSelectedParentNativeCompiler.pending source writer prior entry target pending).run state.1 =
            ambient (lift (RawCtxSelectedParentNativeCompiler.pending source writer prior entry target pending)) state
          simp only [ambient, PqxdhInitialBeaconAmbient.lift, StateT.run, Functor.map_map]
  | inr query =>
      rcases query with query | (reply | (secrets | (query | query)))
      all_goals rfl

/-- Complete retained execution is the same original native parent program with all ambient effects retained. -/
theorem retained_program (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) :
    simulateQ (PqxdhInitialNativeRetained.retained source writer (lookup prior entry target)
      (PqxdhInitialNativeAudit.external pre application initial selector aux)) client =
      ambient (simulateQ (PqxdhInitialParentPost.nativeHandler source writer prior entry target
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux) client) := by
  rw [retained_handler, ambient_program]

/-- Installing the actual parent response gives exactly the retained parent entry and leaves every earlier binding in its prior view. -/
theorem updated_view (request : JointKdfAddress) (output : FullOutput) (state : State A N C) :
    view (productionStream source.crypto) (PqxdhInitialNativeResponse.updated request output state).1.1.2.1 =
      lookup (view (productionStream source.crypto) state.1.1.2.1) (fromOutput request output) (PqxdhOrderedChainHybrids.nextChain output) := by
  funext address
  exact view_recorded _ _ _ address _

/-- The earlier child stage after the actual matched parent response realizes the whole original native context, including its fixed earlier-root initializer and full ambient state. -/
theorem parent_retained (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (output : FullOutput)
    (state : State A N C)
    (matching : RawCtxSelectiveChainGame.matched state.1.1.2.2 (PqxdhInitialBuilderContext.address context.original) = true) :
    (fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original output))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) output state) =
      (ambient (simulateQ (PqxdhInitialParentPost.nativeHandler source writer
        (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput (PqxdhInitialBuilderContext.address context.original) output) (PqxdhOrderedChainHybrids.nextChain output)
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux)
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original output)))).run
          (PqxdhInitialNativeRetained.project state) := by
  have past : state.1.1.2.2.depth + 1 ≤
      (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) output state).1.1.2.2.depth := by
    simp only [PqxdhInitialNativeResponse.updated, RawCtxSelectiveChainGame.advance_depth, matching, if_true]
    exact Nat.le_refl _
  rw [PqxdhInitialNativeRetained.retained_run source writer _ _ _ _ past, updated_view]
  rw [retained_program]
  rfl

/-- The same actual parent continuation is its concrete material-only origin context, with the complete native result reconstructed after all original effects. -/
theorem parent_material (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (output : FullOutput)
    (state : State A N C)
    (matching : RawCtxSelectiveChainGame.matched state.1.1.2.2 (PqxdhInitialBuilderContext.address context.original) = true) :
    (fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original output))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) output state) =
      (ambient (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
        (RawCtxSelectedParentCalls.nativeKernel (PqxdhOrderedChainHybrids.nextChain output))) id) <$>
        simulateQ (PqxdhInitialParentPost.labelHandler source writer
          (view (productionStream source.crypto) state.1.1.2.1)
          (fromOutput (PqxdhInitialBuilderContext.address context.original) output) (PqxdhOrderedChainHybrids.nextChain output)
          pre application (fun secrets => Prod.snd <$> initial secrets) selector aux
          (RawCtxSelectedParentCalls.childResponse (view (productionStream source.crypto) state.1.1.2.1)
            (fromOutput (PqxdhInitialBuilderContext.address context.original) output) (PqxdhOrderedChainHybrids.nextChain output)))
          (PqxdhInitialOriginContext.stopped mark sender route decode context (material output)))).run
            (PqxdhInitialNativeRetained.project state) := by
  rw [parent_retained source writer pre application initial selector aux mark sender route decode context output state matching]
  exact congrArg (fun work => (ambient work).run (PqxdhInitialNativeRetained.project state))
    (PqxdhInitialOriginNativeContext.frame_cut source writer (view (productionStream source.crypto) state.1.1.2.1)
      pre application (fun secrets => Prod.snd <$> initial secrets) selector aux mark sender route decode context output)

end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.ambient_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.retained_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.retained_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.retained_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.retained_program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.updated_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.updated_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.parent_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.parent_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.parent_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation.parent_material
