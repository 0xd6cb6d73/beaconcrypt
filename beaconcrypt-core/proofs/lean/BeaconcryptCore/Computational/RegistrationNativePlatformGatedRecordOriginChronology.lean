-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FullSpec Entry FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState)
open RegistrationNativeStageTrace (Call Executed Path)
variable {n : Nat} {I KemSK Reader Response E Failure A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : Std.U64) (bounds : FreshBounds)
local notation "State" => PqxdhDeploymentSecrecy.Ledger × NativeState n E
local notation "impl" => RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKid bounds
attribute [local irreducible] PqxdhRecordLiftIdeal.ctxInterpreter

include ideal in
private theorem path_safe {first last : State} {calls : List (Call FullSpec State)}
    (actual : Path impl first calls last) (safe : PqxdhRecordLiftProtocolHistory.Safe first.2.1.2) :
    PqxdhRecordLiftProtocolHistory.Safe last.2.1.2 := by
  revert safe
  induction actual with
  | nil state => exact fun safe => safe
  | cons call called rest last following ih =>
      intro safe
      exact ih (RegistrationNativePlatformGatedRecordBindingControl.full_advance modes ideal replace setup codec route env reserve serverKid bounds
        call.query call.before safe (call.reply, call.after) called).step.1

include ideal readback in
/-- The chronological callback list is exactly the original full ledger suffix, with no successful-attempt filtering. -/
theorem path_transcript {first last : State} {calls : List (Call FullSpec State)}
    (actual : Path impl first calls last) (safe : PqxdhRecordLiftProtocolHistory.Safe first.2.1.2) :
    last.1.transcript = first.1.transcript ++ calls.map (fun call => (⟨call.query, call.reply⟩ : Entry)) := by
  revert safe
  induction actual with
  | nil state => intro _safe; simp only [List.map_nil, List.append_nil]
  | cons call called rest last following ih =>
      intro safe
      have progress := RegistrationNativePlatformGatedRecordBindingControl.full_advance modes ideal replace setup codec route env reserve serverKid bounds
        call.query call.before safe (call.reply, call.after) called
      have recorded := RegistrationNativePlatformGatedRecordBindingLedger.full_record modes ideal replace setup codec route readback env reserve serverKid bounds
        call.query call.before safe (call.reply, call.after) called
      rw [ih progress.step.1, recorded.1, List.append_assoc]
      rfl

include ideal readback in
/-- Every actual receive in this same chronological execution already has its source seal in its own pre-call cache. -/
theorem path_received {first last : State} {calls : List (Call FullSpec State)}
    (actual : Path impl first calls last) (safe : PqxdhRecordLiftProtocolHistory.Safe first.2.1.2)
    (call : Call FullSpec State) (member : call ∈ calls)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨call.query, call.reply⟩ : Entry).received = some (receiver, raw, .Some opened)) :
    ∃ leading trailing, calls = leading ++ call :: trailing ∧ Path impl first leading call.before ∧
      ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
        PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  obtain ⟨leading, trailing, split, leadingPath, called, _following⟩ := actual.member call member
  refine ⟨leading, trailing, split, leadingPath, ?_⟩
  exact RegistrationNativePlatformGatedRecordOriginStage.full_received_before modes ideal replace setup codec route readback env reserve serverKid bounds
    call.query call.before (path_safe modes ideal replace setup codec route env reserve serverKid bounds leadingPath safe)
    (call.reply, call.after) called receiver raw opened received

include ideal readback in
/-- Every supported complete execution has one exact chronological source witness for its original ledger and every accepted raw receive, including all failed sends and later callbacks. -/
theorem program (work : OracleComp FullSpec A) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : A × State)
    (supported : result ∈ support ((simulateQ impl work).run (PqxdhDeploymentSecrecy.Ledger.empty, before))) :
    ∃ calls, Path impl (PqxdhDeploymentSecrecy.Ledger.empty, before) calls result.2 ∧
      result.2.1.transcript = calls.map (fun call => (⟨call.query, call.reply⟩ : Entry)) ∧
      ∀ call ∈ calls, ∀ receiver raw opened,
        (⟨call.query, call.reply⟩ : Entry).received = some (receiver, raw, .Some opened) →
        ∃ leading trailing, calls = leading ++ call :: trailing ∧
          Path impl (PqxdhDeploymentSecrecy.Ledger.empty, before) leading call.before ∧
          ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
            PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  rw [← RegistrationNativeStageTrace.erase impl work ((PqxdhDeploymentSecrecy.Ledger.empty, before), []), support_map] at supported
  obtain ⟨traced, reached, same⟩ := supported
  have actual := RegistrationNativeStageTrace.path impl work (PqxdhDeploymentSecrecy.Ledger.empty, before) traced reached
  cases same
  refine ⟨traced.2.2, actual, ?_, ?_⟩
  · change traced.2.1.1.transcript = _
    simpa only [PqxdhDeploymentSecrecy.Ledger.empty, List.nil_append] using
      path_transcript modes ideal replace setup codec route readback env reserve serverKid bounds actual safe
  · exact fun call member receiver raw opened received => path_received modes ideal replace setup codec route readback env reserve serverKid bounds
      actual safe call member receiver raw opened received

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.path_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.path_transcript

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.path_received' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.path_received

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology.program
