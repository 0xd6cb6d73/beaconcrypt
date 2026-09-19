import BeaconcryptCore.Computational.PqxdhInitialNativePrefix
import BeaconcryptCore.Computational.PqxdhInitialOriginNativeContext

/-!
An actual full source descriptor consumes the original selective private-step response and preserves all ambient state, cache, cursor and executed-input history. The same callback supports both cached responses and fresh full76 draws; only a proved matched miss before the selected stage yields a uniform predecessor.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeResponse
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialNativeLog PqxdhFullSecretInputKdf
open PqxdhInitialBuilderContext
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
/-- The actual pending source callback returns exactly the original full76 response with its complete selective cache/cursor update; external ambient state remains present. -/
theorem bare_frame_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result S B) (state : Bare A N C) :
    (bare source writer stage external (frame sender route decode context).1).run state =
      (fun result => (PqxdhInitialParentBuilderContext.reply sender route decode context result.1,
        ((state.1.1, result.2), state.2))) <$>
        RawCtxSelectiveChainGame.privateStep source stage (address context) state.1.2 := by
  cases context with
  | inl context =>
      cases context with
      | record request before outside inner =>
          simpa only [bare, frame, PqxdhInitialPostContext.frame, StateT.run, PqxdhInitialParentBuilderContext.reply,
            PqxdhInitialParentContext.reply, address, PqxdhInitialPostContext.address, bind_pure_comp, Functor.map_map] using
            congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
              (RawCtxLoggedParentResponse.frame_step source writer stage sender route decode inner state.1)
      | finish index before control candidate outside inner =>
          cases inner <;>
            simp only [bare, frame, PqxdhInitialPostContext.frame, RawCtxSelectedFamilyContext.ownerFrame,
              StateT.run, PqxdhInitialParentBuilderContext.reply, PqxdhInitialParentContext.reply,
              RawCtxSelectedFamilyNativeContext.ownerReply, address, PqxdhInitialPostContext.address,
              RawCtxSelectedFamilyContext.ownerAddress, bind_pure_comp]
          all_goals rename_i owner outsideOwner pending
          all_goals first
            | simpa only [StateT.run, Functor.map_map] using
                congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
                  (RawCtxPendingParentCallbacks.receive_step (serverCount := S) (beaconCount := B) source writer stage pending state.1)
            | simpa only [StateT.run, Functor.map_map] using
                congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
                  (RawCtxPendingParentCallbacks.send_step (serverCount := S) (beaconCount := B) source writer stage pending state.1)
  | inr context =>
      simp only [bare, frame, builderFrame, StateT.run, PqxdhInitialParentBuilderContext.reply, address, bind_pure_comp]
      simpa only [StateT.run, Functor.map_map] using
        congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
          (RawCtxPendingParentCallbacks.send_step (serverCount := S) (beaconCount := B) source writer stage context.pending state.1)

private theorem inputs_address (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (request : JointKdfAddress) (found : PqxdhInitialPostContext.queryAddress query = some request)
    (past : List JointKdfAddress) : inputs query past = past ++ [request] := by
  cases query with
  | inl query => simp only [PqxdhInitialPostContext.queryAddress] at found; simp only [inputs, RawCtxSelectiveFamilyLog.inputs, found]
  | inr query => cases found

/-- The full carried source callback appends its actual private input only after executing the unchanged selective step. -/
theorem logged_frame_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result S B) (state : State A N C) :
    (handler source writer stage external (frame sender route decode context).1).run state =
      (fun result => (PqxdhInitialParentBuilderContext.reply sender route decode context result.1,
        (((state.1.1.1, result.2), state.1.2 ++ [address context]), state.2))) <$>
        RawCtxSelectiveChainGame.privateStep source stage (address context) state.1.1.2 := by
  simp only [handler, StateT.run, bind_pure_comp]
  have actual := bare_frame_step source writer stage external sender route decode context (erase state)
  simp only [StateT.run] at actual
  rw [actual]
  simp only [Functor.map_map, erase,
    inputs_address _ _ (PqxdhInitialBuilderContext.frame_address sender route decode context)]

def updated (request : JointKdfAddress) (output : FullOutput) (state : State A N C) : State A N C :=
  (((state.1.1.1, (state.1.1.2.1.cacheQuery request output,
    RawCtxSelectiveChainGame.advance state.1.1.2.2 request output)), state.1.2 ++ [request]), state.2)

/-- A cached predecessor is reused with its exact original response and full-state update; the callback never resamples it. -/
theorem frame_hit (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result S B) (state : State A N C) (output : FullOutput)
    (found : state.1.1.2.1 (address context) = some output) :
    (handler source writer stage external (frame sender route decode context).1).run state =
      pure (PqxdhInitialParentBuilderContext.reply sender route decode context output, updated (address context) output state) := by
  rw [logged_frame_step, RawCtxSelectiveChainGame.private_hit source stage (address context) state.1.1.2 output found]
  rfl

/-- A source-selected matched miss before the child stage draws one full76 predecessor and retains its exact response, cache, cursor, prior inputs and ambient state. -/
theorem frame_miss (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result S B) (state : State A N C)
    (missing : state.1.1.2.1 (address context) = none)
    (matching : RawCtxSelectiveChainGame.matched state.1.1.2.2 (address context) = true)
    (before : state.1.1.2.2.depth < stage) :
    (handler source writer stage external (frame sender route decode context).1).run state =
      (fun output => (PqxdhInitialParentBuilderContext.reply sender route decode context output,
        updated (address context) output state)) <$> ($ᵗ FullOutput) := by
  rw [logged_frame_step, RawCtxSelectiveChainGame.private_selected source stage (address context) state.1.1.2 missing matching before]
  simp only [Functor.map_map, updated]

/-- The actual origin-aware selected callback is the same source draw; private trace metadata cannot change its response or any interpreter field. -/
theorem origin_frame_miss (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) (state : State A N C)
    (missing : state.1.1.2.1 (address context.original) = none)
    (matching : RawCtxSelectiveChainGame.matched state.1.1.2.2 (address context.original) = true)
    (before : state.1.1.2.2.depth < stage) :
    (handler source writer stage external (PqxdhInitialOriginContext.frame mark sender route decode context).1).run state =
      (fun output => (PqxdhInitialParentBuilderContext.reply sender route decode context.original output,
        updated (address context.original) output state)) <$> ($ᵗ FullOutput) :=
  frame_miss source writer stage external sender route decode context.original state missing matching before

end BeaconcryptCore.Computational.PqxdhInitialNativeResponse

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeResponse.bare_frame_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeResponse.bare_frame_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeResponse.logged_frame_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeResponse.logged_frame_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeResponse.frame_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeResponse.frame_hit
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeResponse.frame_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeResponse.frame_miss
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeResponse.origin_frame_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeResponse.origin_frame_miss
