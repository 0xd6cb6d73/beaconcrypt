import BeaconcryptCore.Computational.PqxdhInitialNativeParentContinuation
import BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver

/-!
The concrete full native parent continuation realizes the compiled partial-alias observer, preserving the original initializer and all ambient fields. Its actual retained child response is made explicit; absence from the actual chronological cache-input log yields the fixed-source child response. Parent/child address collisions remain an explicit charged source case.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialBeaconAmbient PqxdhInitialNativeLog RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedParentPrivatePatch
open PqxdhInitialNativeRetained (RetainedState)
variable {ι M P I D K X Response Shared Result Origin A N C α : Type} {extra : OracleSpec ι} {S B : Nat}

def nested (state : RetainedState A N C) : PqxdhInitialParentObserver.State A N C := ((state.1, state.2.1), state.2.2)
def flat (state : PqxdhInitialParentObserver.State A N C) : RetainedState A N C := (state.1.1, (state.1.2, state.2))

/-- The compiled observer and native interpreter retain exactly the same ambient state under tuple reassociation. -/
theorem ambient_flatten (work : Ambient A N C α) (state : RetainedState A N C) :
    (PqxdhInitialNativeParentContinuation.ambient work).run state =
      (fun result => (result.1, flat result.2)) <$>
        (PqxdhInitialParentObserver.flatten work).run (nested state) := by
  simp only [PqxdhInitialNativeParentContinuation.ambient, PqxdhInitialParentObserver.flatten,
    StateT.run, nested, flat, Functor.map_map]

/-- A result map changes only the complete returned value, preserving every ambient field. -/
theorem ambient_map {β : Type} (f : α → β) (work : Ambient A N C α) (state : RetainedState A N C) :
    (PqxdhInitialNativeParentContinuation.ambient (f <$> work)).run state =
      (fun result => (f result.1, result.2)) <$> (PqxdhInitialNativeParentContinuation.ambient work).run state := by
  change (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
      (((f <$> work).run (state.1, state.2.1)).run state.2.2) =
      (fun result => (f result.1, result.2)) <$>
        (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
          ((work.run (state.1, state.2.1)).run state.2.2)
  simp only [StateT.run_map, Functor.map_map]

/-- Patching a lookup with the value it already returns changes no address. -/
theorem consistent_patch (prior : Prior) (target : RootOutput) :
    privatePatch prior target (prior (targetAddress target)) = prior := by
  funext address
  by_cases same : address = targetAddress target
  · subst address
    simp only [privatePatch, ite_true]
  · simp only [privatePatch, ite_eq_right same]

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : Prior) (entry : Entry) (target : RootOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The actual retained child response realizes the same compiled partial observer and original initializer. -/
theorem compiled_consistent
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra RawCtxSelectedChain.Slot I D K X Response Shared S B) Result)
    (separate : targetAddress target ≠ entry.address) :
    simulateQ (PqxdhInitialParentPrivateObserver.handler source writer prior entry (prior (targetAddress target))
      pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (simulateQ PqxdhInitialParentObserverCompiler.compiler client) =
      PqxdhInitialParentObserver.flatten (simulateQ (PqxdhInitialParentPost.labelHandler source writer prior entry target
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux
        (RawCtxSelectedParentCalls.childResponse prior entry target)) client) := by
  have response := child_response prior entry target (prior (targetAddress target)) separate
  rw [consistent_patch] at response
  rw [PqxdhInitialParentPrivateObserver.compiled_source source writer prior entry _ pre application initial selector aux target client separate,
    consistent_patch, response]

/-- The complete actual native parent frame equals its compiled partial-routing program with the actual retained child response and original initializer. -/
theorem frame_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (parent : FullOutput)
    (state : RetainedState A N C)
    (separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address context.original) :
    (PqxdhInitialNativeParentContinuation.ambient
      (simulateQ (PqxdhInitialParentPost.nativeHandler source writer prior
        (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (nextChain parent)
        pre application (fun secrets => Prod.snd <$> initial secrets) selector aux)
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent)))).run state =
      (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
        (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id) result.1, flat result.2)) <$>
        (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer prior
          (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (prior (targetAddress (nextChain parent)))
          pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent)))
          (nextChain parent))
          (simulateQ PqxdhInitialParentObserverCompiler.compiler
            (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run (nested state) := by
  rw [PqxdhInitialOriginNativeContext.frame_cut, ambient_map, ambient_flatten]
  rw [← compiled_consistent source writer prior _ _ pre application initial selector aux _ separate]
  simp only [Functor.map_map]

/-- The actual earlier child stage after its parent draw equals the compiled partial observer, with complete native result and ambient state reconstructed and the original initializer unchanged. -/
theorem source_compiled (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (parent : FullOutput)
    (state : State A N C)
    (matching : RawCtxSelectiveChainGame.matched state.1.1.2.2 (PqxdhInitialBuilderContext.address context.original) = true)
    (separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address context.original) :
    (fun result => (result.1, PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
          (PqxdhInitialNativeResponse.updated (PqxdhInitialBuilderContext.address context.original) parent state) =
      (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
        (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id) result.1, flat result.2)) <$>
        (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer
          (view (productionStream source.crypto) state.1.1.2.1)
          (fromOutput (PqxdhInitialBuilderContext.address context.original) parent)
          (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent)))
          pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent)))
          (nextChain parent))
          (simulateQ PqxdhInitialParentObserverCompiler.compiler
            (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run
              (nested (PqxdhInitialNativeRetained.project state)) := by
  exact (PqxdhInitialNativeParentContinuation.parent_retained source writer pre application initial selector aux
    mark sender route decode context parent state matching).trans
      (frame_compiled source writer (view (productionStream source.crypto) state.1.1.2.1)
        pre application initial selector aux mark sender route decode context parent
        (PqxdhInitialNativeRetained.project state) separate)

/-- An input absent from the original executed-input log is absent from the actual prior cache and therefore keeps the fixed real source response. -/
theorem unlisted_source (state : State A N C) (covered : Covered state)
    (address : JointKdfAddress) (unlisted : address ∉ state.1.2) :
    view (productionStream source.crypto) state.1.1.2.1 address = productionStream source.crypto address := by
  have missing : state.1.1.2.1 address = none := by
    cases present : state.1.1.2.1 address with
    | none => rfl
    | some output => exact False.elim (unlisted (covered address output present))
  simp only [view, missing, Option.getD_none]

end Interpreter
end BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.ambient_flatten' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.ambient_flatten

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.ambient_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.ambient_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.consistent_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.consistent_patch

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.compiled_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.compiled_consistent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.frame_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.frame_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.source_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.source_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.unlisted_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization.unlisted_source
