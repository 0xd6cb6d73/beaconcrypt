-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordOriginInitialized
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Entry FullSpec FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path)
variable {n : Nat} {I KemSK Reader Response E Value Failure : Type} {base : OracleSpec I}
attribute [local irreducible] PqxdhRecordLiftIdeal.ctxInterpreter
abbrev Runtime (n : Nat) (E : Type) := PqxdhDeploymentSecrecy.Ledger ×
  CborRawRecordFlat.NativeState n (RegistrationNativeEntropyPort.State E)
variable (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : RegistrationNativeEntropyInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (secret : CtxPrivate n)
local notation "impl" => RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route
  (RegistrationNativeEntropyPort.environment env) (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) serverKid bounds
local notation "startState" => (PqxdhDeploymentSecrecy.Ledger.empty, (((([], initial), shell), control), secret))

include ideal readback safe in
/-- Every original native ledger has one exact adaptive chronology with the same final private/control state and an actual before-receive source-seal witness for each accepted callback. -/
theorem initialized_stages (result : RegistrationNativeEntropyRun.Result n E Value)
    (supported : result ∈ support (RegistrationNativePlatformGatedNativeEntropy.run modes replace setup codec route env reserve serverKid bounds mode work
      created initial shell control secret)) :
    ∀ born ∈ result.1.1, ∃ final : Runtime n E, ∃ calls : List (Call FullSpec (Runtime n E)),
      Path impl startState calls final ∧ final.2.1.2 = result.1.2 ∧ final.2.2 = result.2 ∧
      RegistrationNativeEntropyTrace.strip (calls.map (fun call => (⟨call.query, call.reply⟩ : Entry))) = born.2.1.2.ledger.transcript ∧
      ∀ call ∈ calls, ∀ receiver raw opened,
        (⟨call.query, call.reply⟩ : Entry).received = some (receiver, raw, core.option.Option.Some opened) →
        ∃ leading trailing, calls = leading ++ call :: trailing ∧ Path impl startState leading call.before ∧
          ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
            PqxdhRecordFactsOriginAccepted.Accepted codec call.before.2.1.2 call.before.2.2 handle raw opened := by
  rw [← RegistrationNativePlatformGatedNativeEntropy.run_transport, support_map] at supported
  obtain ⟨old, oldSupported, rfl⟩ := supported
  simp only [RegistrationNativePlatformGatedEntropyInitial.run, support_map] at oldSupported
  obtain ⟨final, finalSupported, rfl⟩ := oldSupported
  obtain ⟨calls, actual, transcript, stages⟩ := RegistrationNativePlatformGatedRecordOriginChronology.program modes ideal replace setup codec route readback
    (RegistrationNativeEntropyPort.environment env) (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) serverKid bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work))
    (((([], initial), shell), control), secret) safe final finalSupported
  intro born member
  have selected : born = (PqxdhRegistrationJointServerBirth.encode created,
      ((final.1, RegistrationNativeEntropyRestore.ledger final.2.1), final.2.2.1.1.1.2)) := by
    symm
    simpa only [RegistrationNativeEntropyRun.project, RegistrationNativeEntropyProgram.outcome,
      RegistrationNativeEntropyExecution.result, Prod.map, id_eq, Option.map_some, Option.mem_some_iff] using member
  subst born
  refine ⟨final.2, calls, actual, rfl, rfl, ?_, stages⟩
  rw [RegistrationNativeEntropyRestore.ledger_transcript, transcript]

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordOriginInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordOriginInitialized.initialized_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordOriginInitialized.initialized_stages
