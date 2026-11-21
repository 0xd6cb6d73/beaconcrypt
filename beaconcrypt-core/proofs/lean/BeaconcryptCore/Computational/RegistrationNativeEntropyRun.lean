-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyProgram
import BeaconcryptCore.Computational.CborRawRecordFresh

/-! The actual ML-pin-aware full-ledger World program under the cursor-filtered dynamic record interpreter. The source/output equality derives the old entropy-port representation while retaining the entire native ledger, environment, record control and private record state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyRun
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK E Value Reader Response First Second : Type} {base : OracleSpec ι}

abbrev Outcome (E Value : Type) := Option (PqxdhRegistrationJointServerBirth.ClientCreated (Std.Array Std.U8 151#usize) ×
  (Value × RegistrationNativeLedger.State) × E)
abbrev Result (n : Nat) (E Value : Type) :=
  (Outcome E Value × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n

noncomputable def execute (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) First) :
    ProbComp ((First × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) work).run
      PqxdhRecordLiftProtocol.initialControl)).run CtxPrivate.initial

/-- Mapping a completed observation leaves the entire private record control and CTX state unchanged. -/
theorem execute_map (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) First) (observe : First → Second) :
    Prod.map (Prod.map observe id) id <$> execute modes replace setup codec route work =
      execute modes replace setup codec route (observe <$> work) := by
  simp only [execute, simulateQ_map, StateT.run_map]
  rfl

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) : ProbComp (Result n E Value) :=
  execute modes replace setup codec route (CborRecordWorldClient.client
    (RegistrationNativeEntropyWorld.program env setup.source.crypto codec serverKid bounds mode work))

def project (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value × CtxPrivate n) :
    Result n E Value := Prod.map (Prod.map RegistrationNativeEntropyProgram.outcome id) id old

/-- The complete cursor-filtered native record execution is the exact transported old-record execution, with no simulation premise. -/
theorem run_transport (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    project <$> CborRawRecordHidingLaw.ctxRun modes replace setup codec route
        (RegistrationNativeEntropyPort.environment env) serverKid bounds mode
          (RegistrationNativeEntropyCompile.compile mode work) =
      run modes replace setup codec route env serverKid bounds mode work := by
  change Prod.map (Prod.map RegistrationNativeEntropyProgram.outcome id) id <$>
    execute modes replace setup codec route (CborRecordWorldClient.client
      (PqxdhRecordLiftInterface.program (RegistrationNativeEntropyPort.environment env)
        setup.source.crypto codec serverKid bounds mode (RegistrationNativeEntropyCompile.compile mode work))) = _
  rw [execute_map, RegistrationNativeEntropyProgram.cursor_program]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeEntropyRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRun.execute_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRun.execute_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyRun.run_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyRun.run_transport
