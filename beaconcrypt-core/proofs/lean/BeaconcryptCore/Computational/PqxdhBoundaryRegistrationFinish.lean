-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive

/-! Real candidate-local receive at the frozen CE native finish command, retaining both shared caches and the full owner registry. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish
open PqxdhBoundaryRegistrationReceive PqxdhBoundaryRecordPrelude
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {Message Root Reader Response KemSK ι : Type} {baseSpec : OracleSpec ι}

/-- Installing the shared complete frame reader changes no preparation, root, initial KDF, application, hash or AEAD callback. -/
theorem callbacks_withReader (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) :
    PqxdhRegistrationSchedule.callbacks setup (withReader codec reader) =
      PqxdhRegistrationSchedule.callbacks setup codec := by
  rfl

/-- Look up the actual public finish owner, run the real local-candidate executor on the original shared native interpreter, and reinstall exactly its returned owner. -/
noncomputable def executeFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK) :
    ProbComp (RustM (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)) :=
  match state.owners[index]? with
  | none => pure (ok (none, state))
  | some owner => do
      let result ← (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
        (executeRegistration reader erased raw owner)).run state.shared
      pure ((fun output => (output.1,
        ({ shared := result.2, owners := state.owners.set index output.2 } : PqxdhRegistrationSchedule.State KemSK))) <$> result.1)

/-- Actual public owner lookup and reinstallation preserve the complete original finish distribution, including both shared caches on rejected and aborted paths. -/
theorem finish_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK) :
    executeFinish setup codec reader erased index raw state =
      (fun result => ok result) <$> (PqxdhRegistrationSchedule.finish setup (withReader codec reader) index raw).run state := by
  unfold executeFinish
  cases found : state.owners[index]? with
  | none => rw [PqxdhRegistrationSchedule.finish_missing setup (withReader codec reader) index raw state found, map_pure]
  | some owner =>
    have original := PqxdhRegistrationSchedule.finish_source setup (withReader codec reader) index raw state owner found
    change (PqxdhRegistrationSchedule.finish setup (withReader codec reader) index raw).run state = _ at original
    rw [original, callbacks_withReader]
    simp only [registration_exact, simulateQ_map, StateT.run_map, bind_pure_comp, Functor.map_map,
      PqxdhOpenContextBridge.map_ok, PqxdhBoundaryRecordPrelude.withReader]

/-- Lift the real finish executor to the complete CE native state, retaining both raw-attempt counters and every produced-frame entry. -/
noncomputable def executeNativeFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    ProbComp (RustM (Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK)) :=
  (fun result => (fun output => (output.1, { state with native := output.2 })) <$> result) <$>
    executeFinish setup codec reader erased index raw state.native

/-- The frozen CE finish command is exactly the candidate-local executor, with the original native interpreter and its entire state. -/
theorem native_finish_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    executeNativeFinish setup codec reader erased index raw state =
      (fun result => ok result) <$> (PqxdhDeploymentNative.handler setup (withReader codec reader)
        checks route serverSeed (.inr (.finish index raw))).run state := by
  simp only [executeNativeFinish, finish_exact, PqxdhDeploymentNative.handler,
    PqxdhDeploymentNative.onNative, PqxdhRegistrationSchedule.handler, Functor.map_map,
    PqxdhOpenContextBridge.map_ok, StateT.run]
  rfl

/-- Every complete continuation sees the original finish reply, shared interpreter state and owner registry together. -/
theorem finish_complete {Result : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK)
    (next : RustM (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK) → ProbComp Result) :
    executeFinish setup codec reader erased index raw state >>= next =
      (PqxdhRegistrationSchedule.finish setup (withReader codec reader) index raw).run state >>=
        fun result => next (ok result) := by
  rw [finish_exact, bind_map_left]

/-- The CE command equality is preserved under any complete continuation, including one inspecting the unchanged counters, produced records and shared native caches. -/
theorem native_finish_complete {Result : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Std.Array Std.U8 229#usize)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK)
    (next : RustM (Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK) → ProbComp Result) :
    executeNativeFinish setup codec reader erased index raw state >>= next =
      (PqxdhDeploymentNative.handler setup (withReader codec reader) checks route serverSeed
        (.inr (.finish index raw))).run state >>= fun result => next (ok result) := by
  rw [native_finish_exact setup codec checks route serverSeed, bind_map_left]

end BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.callbacks_withReader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.callbacks_withReader

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.finish_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.native_finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.native_finish_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.finish_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.finish_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.native_finish_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationFinish.native_finish_complete
