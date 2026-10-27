import BeaconcryptCore.Computational.PqxdhLaterSavedFreshness
import BeaconcryptCore.Computational.PqxdhInitialNativeParentChild
import BeaconcryptCore.Computational.PqxdhErasedParentView

/-! The original full finite-checker event is transported through the retained saved-source execution. The separately bounded parent-address collision remains an explicit operational case; no source decision, initializer or disclosure history is replaced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterRetainedEvent
open PqxdhJointKdf PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhOrderedChainHybrids
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedParentPrivatePatch
open PqxdhInitialBeaconAmbient PqxdhInitialNativeParentRealization
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (Ambient A N C))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

/-- The literal saved native resumption equals the existing full partial-routing observer, with every optional reply, source role and ambient effect retained. The parent address is its actual descriptor address. -/
theorem retained_source
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (entry : Entry) (target : RootOutput) (output : FullOutput)
    (state : PqxdhInitialNativeRetained.RetainedState A N C)
    (address : entry.address = PqxdhInitialBuilderContext.address context.original)
    (separate : targetAddress target ≠ entry.address) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (lookup (privatePatch prior target output) entry target)
      (PqxdhInitialNativeAudit.external pre application initial selector aux))
      (PqxdhInitialOriginContext.resume mark sender route decode context
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original (realize entry target)))).run state =
    (fun result => (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront
      (RawCtxSelectedParentCalls.nativeKernel target)) id) result.1, flat result.2)) <$>
      (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer prior entry output
        pre application initial selector aux (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (simulateQ PqxdhInitialParentObserverCompiler.compiler
          (PqxdhInitialOriginContext.stopped mark sender route decode context entry.material))).run (nested state) := by
  have coordinates := parts entry target
  have materialEq : material (realize entry target) = entry.material := congrArg Prod.fst coordinates
  have nextEq : nextChain (realize entry target) = target := congrArg Prod.snd coordinates
  have sameEntry : fromOutput (PqxdhInitialBuilderContext.address context.original) (realize entry target) = entry := by
    change Entry.mk _ (material (realize entry target)) = entry
    rw [← address, materialEq]
  have sourceEq := PqxdhInitialNativeParentChild.frame_compiled source writer prior pre application initial selector aux
    mark sender route decode context (realize entry target) output state
      (by simpa only [nextEq, ← address] using separate)
  rw [sameEntry, nextEq, materialEq] at sourceEq
  rw [PqxdhInitialNativeParentContinuation.retained_program]
  exact sourceEq

/-- The original proof-erased material observer has exactly its original native decision on the literal saved resumption. Only the already explicit parent self-address event is excluded from this operational equality. -/
theorem original_event (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (input : PqxdhInitialSupportedCertificate.Input extra M P I D K Bool Bool A N C S B)
    (entry : Entry) (target : RootOutput) (output : FullOutput)
    (root : RootOutput) (ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (address : entry.address = PqxdhInitialBuilderContext.address input.1.original)
    (separate : targetAddress target ≠ entry.address) :
    PqxdhInitialCommonSecrecy.native source writer mark sender route decode
      (PqxdhErasedParentView.view source pre application initial selector aux root ancestors disclosed selected number 0)
      (.inr input, entry) target output =
    (fun result => PqxdhInitialNativeParentEvent.nativeDecision
      (view (productionStream source.crypto) input.2.1.1.1.2.1) entry target output 0
      ((PqxdhInitialSourceSecrecyResources.earlierInputs root input).map RawCtxFreshChainCut.concreteChain)
      ancestors disclosed selected number result.1) <$>
      (simulateQ (PqxdhInitialNativeRetained.retained source writer
        (lookup (privatePatch (view (productionStream source.crypto) input.2.1.1.1.2.1) target output) entry target)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        (PqxdhInitialOriginContext.resume mark sender route decode input.1
          (PqxdhInitialParentBuilderContext.reply sender route decode input.1.original (realize entry target)))).run
          (flat (PqxdhInitialSupportedCertificate.ambient input)) := by
  have decision := PqxdhInitialNativeParentChecked.decision_source source writer sender route decode mark
    (PqxdhErasedParentView.view source pre application initial selector aux root ancestors disclosed selected number 0).continuation
    (input, entry) target output disclosed (PqxdhInitialSupportedCertificate.ambient input) input.2.2 0 rfl
    ((PqxdhInitialSourceSecrecyResources.earlierInputs root input).map RawCtxFreshChainCut.concreteChain)
    ancestors selected number
  rw [retained_source source writer (view (productionStream source.crypto) input.2.1.1.1.2.1)
    pre application initial selector aux mark sender route decode input.1 entry target output
    (flat (PqxdhInitialSupportedCertificate.ambient input)) address separate, Functor.map_map]
  simpa only [PqxdhInitialCommonSecrecy.native, PqxdhErasedParentView.view,
    PqxdhInitialSourceSecrecyResources.earlier, PqxdhInitialParentStoppedHop.baseProgram,
    nested, flat] using decision

end BeaconcryptCore.Computational.PqxdhLaterRetainedEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedEvent.retained_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedEvent.retained_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterRetainedEvent.original_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterRetainedEvent.original_event
