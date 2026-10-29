-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyExecution
import BeaconcryptCore.Computational.CborRecordWorldClient

/-! Startup and cursor-filtered whole-program transport. Actual optional constructor failure is retained, and the cursor filter stays below the literal test/fresh draws on both sides. Only public adapter metadata is decoded in the final result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyProgram
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {E Value Reader Response First Second : Type}

def outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (Value × PqxdhDeploymentSecrecy.Ledger) × RegistrationNativeEntropyPort.State E) →
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Value × RegistrationNativeLedger.State) × E) :=
  Option.map (fun old => (old.1, RegistrationNativeEntropyExecution.result old.2))

/-- Actual optional startup and the complete native secrecy execution are preserved, jointly with the full native environment poststate. -/
theorem program (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    outcome <$> PqxdhRecordLiftInterface.program (RegistrationNativeEntropyPort.environment env)
        crypto codec serverKid bounds mode (RegistrationNativeEntropyCompile.compile mode work) =
      RegistrationNativeEntropyWorld.program env crypto codec serverKid bounds mode work := by
  simp only [PqxdhRecordLiftInterface.program, RegistrationNativeEntropyWorld.program,
    RegistrationNativeEntropyPort.environment, simulateQ_map, map_bind, bind_map_left]
  apply bind_congr
  rintro (_ | ⟨created, initial⟩)
  · simp only [Option.map_none, map_pure]
    rfl
  · simp only [Option.map_some, map_bind]
    apply bind_congr
    intro initialized
    have executed := RegistrationNativeEntropyExecution.wrapped_mode env crypto codec serverKid bounds
      mode work ([], initial)
    simpa only [map_pure, bind_pure_comp, Functor.map_map, outcome, Option.map_some,
      RegistrationNativeEntropyPort.environment] using
      (congrArg (fun distribution => (fun result =>
        some (PqxdhRegistrationJointServerBirth.encode created, result)) <$> distribution) executed)

/-- The actual cursor client is natural in final observations and leaves every query/admission branch in place. -/
theorem cursor_map (work : OracleComp (WorldSpec n) First) (observe : First → Second)
    (shell : CborRecordWorldClient.Shell) :
    CborRecordWorldClient.client (observe <$> work) shell =
      observe <$> CborRecordWorldClient.client work shell := by
  simp only [CborRecordWorldClient.client, simulateQ_map, StateT.run_map, Functor.map_map]

/-- The original raw cursor filter remains below all original secrecy sampling in the complete native program. -/
theorem cursor_program (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (shell : CborRecordWorldClient.Shell) :
    outcome <$> CborRecordWorldClient.client
        (PqxdhRecordLiftInterface.program (RegistrationNativeEntropyPort.environment env)
          crypto codec serverKid bounds mode (RegistrationNativeEntropyCompile.compile mode work)) shell =
      CborRecordWorldClient.client
        (RegistrationNativeEntropyWorld.program env crypto codec serverKid bounds mode work) shell := by
  rw [← cursor_map, program]

end BeaconcryptCore.Computational.RegistrationNativeEntropyProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.cursor_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.cursor_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.cursor_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyProgram.cursor_program
