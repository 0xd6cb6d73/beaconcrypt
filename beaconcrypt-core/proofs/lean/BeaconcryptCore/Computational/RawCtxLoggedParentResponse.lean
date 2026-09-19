import BeaconcryptCore.Computational.RawCtxLoggedParentPrefix
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext

/-!
The actual source-selected predecessor callback retains both cached responses and fresh full76 draws. Its complete original family frame receives the literal native response, and the same chronological log, table, cursor and shared primitive state are carried into the saved continuation. Public services retain their original implementation. No cache separation, fresh-miss selection or output-distribution premise is inserted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxLoggedParentResponse
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame
open RawCtxSelectedFamilyContext RawCtxSelectedFamilyNativeContext RawCtxSelectiveFamilyLog
variable {M P I D K A Result : Type} {S B : Nat}

/-- The complete original family frame exposes exactly the actual private response and full table/cursor transition. -/
theorem frame_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : RawCtxPendingSelectiveFamily.State A) :
    ((RawCtxPendingSelectiveFamily.handler source writer stage) (frame sender route decode context).1).run state =
      (fun result => (reply sender route decode context result.1, (state.1, result.2))) <$>
        privateStep source stage (address context) state.2 := by
  cases context with
  | family request history outside inner =>
    cases inner with
    | server request before index outside inner =>
      cases inner with
      | owner request before kid peer outside inner =>
        cases inner with
        | receive before outside pending => exact RawCtxPendingParentCallbacks.receive_step source writer stage pending state
        | send before outside pending => exact RawCtxPendingParentCallbacks.send_step source writer stage pending state
    | beacon request before index control associatedData outside inner =>
      cases inner with
      | receive before outside pending => exact RawCtxPendingParentCallbacks.receive_step source writer stage pending state
      | send before outside pending => exact RawCtxPendingParentCallbacks.send_step source writer stage pending state

/-- The same executed callback appends its actual original address after preserving the complete native response and state. -/
theorem logged_frame_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A) :
    ((RawCtxSelectiveFamilyLog.handler source writer stage) (frame sender route decode context).1).run state =
      (fun result => (reply sender route decode context result.1, ((state.1.1, result.2), state.2 ++ [address context]))) <$>
        privateStep source stage (address context) state.1.2 := by
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp]
  have same := frame_step source writer stage sender route decode context state.1
  simp only [StateT.run] at same
  simp only [same, Functor.map_map, inputs, frame_address]

def updated (context : Context M P I D K Result S B) (output : FullOutput) (state : LoggedState A) : LoggedState A :=
  ((state.1.1, (state.1.2.1.cacheQuery (address context) output,
    advance state.1.2.2 (address context) output)), state.2 ++ [address context])

/-- An actual cached predecessor returns its retained complete response without drawing a new parent, then appends the actual request and advances the original cursor. -/
theorem frame_hit (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A) (output : FullOutput)
    (found : state.1.2.1 (address context) = some output) :
    ((RawCtxSelectiveFamilyLog.handler source writer stage) (frame sender route decode context).1).run state =
      pure (reply sender route decode context output, updated context output state) := by
  rw [logged_frame_step, private_hit source stage (address context) state.1.2 output found]
  rfl

/-- A matched predecessor miss before the child stage draws one actual full76 response, then retains its exact native reply and complete logged post-state. -/
theorem frame_miss (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A)
    (missing : state.1.2.1 (address context) = none)
    (selected : matched state.1.2.2 (address context) = true) (before : state.1.2.2.depth < stage) :
    ((RawCtxSelectiveFamilyLog.handler source writer stage) (frame sender route decode context).1).run state =
      (fun output => (reply sender route decode context output, updated context output state)) <$> ($ᵗ FullOutput) := by
  rw [logged_frame_step, private_selected source stage (address context) state.1.2 missing selected before]
  simp only [Functor.map_map, updated]

noncomputable def resume (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (output : FullOutput) (state : LoggedState A) :=
  (simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage)
    ((frame sender route decode context).2 (reply sender route decode context output))).run (updated context output state)

noncomputable def execute (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A) :=
  RawCtxPendingMixedPrefix.finish (RawCtxSelectiveFamilyLog.handler source writer stage)
    (RawCtxPendingMixedPrefix.Stopped.pending (frame sender route decode context).1 (frame sender route decode context).2, state)

/-- A cached predecessor resumes the same complete saved native family continuation from its actual retained response; it does not become an early-completion branch. -/
theorem execute_hit (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A) (output : FullOutput)
    (found : state.1.2.1 (address context) = some output) :
    execute source writer stage sender route decode context state =
      resume source writer stage sender route decode context output state := by
  simp only [execute, RawCtxPendingMixedPrefix.finish, frame_hit source writer stage sender route decode context state output found,
    pure_bind, resume]

/-- A fresh matched predecessor performs its actual full76 draw before the entire original saved native family continuation, retaining the same complete logged post-state. -/
theorem execute_miss (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (state : LoggedState A)
    (missing : state.1.2.1 (address context) = none)
    (selected : matched state.1.2.2 (address context) = true) (before : state.1.2.2.depth < stage) :
    execute source writer stage sender route decode context state =
      ($ᵗ FullOutput) >>= fun output => resume source writer stage sender route decode context output state := by
  simp only [execute, RawCtxPendingMixedPrefix.finish,
    frame_miss source writer stage sender route decode context state missing selected before,
    bind_map_left, resume]

end BeaconcryptCore.Computational.RawCtxLoggedParentResponse

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_step

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.logged_frame_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.logged_frame_step

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.frame_miss

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.execute_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.execute_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxLoggedParentResponse.execute_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLoggedParentResponse.execute_miss
