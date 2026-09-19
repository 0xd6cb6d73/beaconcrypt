import BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization
import BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent
import BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw

/-!
An early selected child response is installed into the actual post-parent private table and realizes the same material-only partial observer. The original initializer and every external computation remain fixed. Parent/child address separation is explicit; no byte alias or cached child is silently excluded.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentChild
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialNativeLog PqxdhInitialNativeResponse PqxdhInitialNativeRetained
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedParentPrivatePatch RawCtxCursorLineage RawCtxSelectiveChainGame
open PqxdhInitialBeaconAmbient PqxdhInitialNativeParentRealization
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual cache with its parent and selected child responses has precisely the private patched retained lookup, preserving every other address. -/
theorem child_view (source : FixedHkdfSha512NoSaltSource) (state : State A N C)
    (address : JointKdfAddress) (parent output : FullOutput)
    (separate : targetAddress (nextChain parent) ≠ address) :
    view (productionStream source.crypto)
      ((updated address parent state).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output) =
      lookup (privatePatch (view (productionStream source.crypto) state.1.1.2.1) (nextChain parent) output)
        (fromOutput address parent) (nextChain parent) := by
  funext request
  by_cases child : request = targetAddress (nextChain parent)
  · subst request
    simp only [view, QueryCache.cacheQuery_self, Option.getD_some, lookup, fromOutput, separate, if_false, privatePatch, if_true]
  · rw [show view (productionStream source.crypto)
        ((updated address parent state).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output) request =
        view (productionStream source.crypto) (updated address parent state).1.1.2.1 request by
          simp only [view, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ output child]]
    rw [PqxdhInitialNativeParentContinuation.updated_view]
    simp only [lookup, privatePatch, if_neg child]

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : Prior)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The original complete native parent continuation with a selected child response realizes the compiled partial observer while preserving the original initializer and every ambient field. -/
theorem frame_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (parent output : FullOutput)
    (state : RetainedState A N C)
    (separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address context.original) :
    (PqxdhInitialNativeParentContinuation.ambient
      (simulateQ (PqxdhInitialParentPost.nativeHandler source writer (privatePatch prior (nextChain parent) output)
        (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (nextChain parent)
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux)
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent)))).run state =
      (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
        (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id) result.1, flat result.2)) <$>
        (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer prior
          (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) output
          pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent)))
          (nextChain parent))
          (simulateQ PqxdhInitialParentObserverCompiler.compiler
            (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run (nested state) := by
  rw [PqxdhInitialOriginNativeContext.frame_cut, child_response _ _ _ _ separate, ambient_map, ambient_flatten]
  rw [← PqxdhInitialParentPrivateObserver.compiled_source source writer prior _ output pre application initial selector aux
    (nextChain parent) _ separate]
  simp only [Functor.map_map]

/-- Installing the early child into the actual post-parent cache realizes the complete original stopped source under the partial observer; no initializer output or external state is changed. -/
theorem retained_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (parent output : FullOutput)
    (state : State A N C)
    (separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address context.original) :
    (simulateQ (retained source writer
      (view (productionStream source.crypto)
        ((updated (PqxdhInitialBuilderContext.address context.original) parent state).1.1.2.1.cacheQuery
          (targetAddress (nextChain parent)) output))
      (PqxdhInitialNativeAudit.external pre application initial selector aux))
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run (project state) =
      (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
        (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id) result.1, flat result.2)) <$>
        (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (view (productionStream source.crypto) state.1.1.2.1)
          (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) output
          pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent)))
          (nextChain parent))
          (simulateQ PqxdhInitialParentObserverCompiler.compiler
            (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run (nested (project state)) := by
  rw [child_view source state _ parent output separate, PqxdhInitialNativeParentContinuation.retained_program]
  exact frame_compiled source writer (view (productionStream source.crypto) state.1.1.2.1)
    pre application initial selector aux mark sender route decode context parent output (project state) separate

end Interpreter

end BeaconcryptCore.Computational.PqxdhInitialNativeParentChild

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.child_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.child_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.frame_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.frame_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.retained_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentChild.retained_compiled
