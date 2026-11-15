-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized
import BeaconcryptCore.Computational.CborRawRecordOriginReceiptLedger

/-! Initialized native ledger transport is independent of the private record interpreter. In particular the original native program, public cursor and all callbacks transport jointly with a sticky source marker, instead of assuming a correspondence only after erasing that marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Reader Response E Secret Value : Type}

abbrev OldResult (n : Nat) (E Secret Value : Type) :=
  (PqxdhRecordLiftIdeal.Client n E Value) × Secret
abbrev Result (n : Nat) (E Secret Value : Type) :=
  (RegistrationNativeEntropyRun.Outcome E Value × Control n) × Secret

def project (old : OldResult n (RegistrationNativeEntropyPort.State E) Secret Value) : Result n E Secret Value :=
  Prod.map (Prod.map RegistrationNativeEntropyProgram.outcome id) id old

noncomputable def oldRun (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp))
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : CborRawRecordOriginService.State n E Secret) : ProbComp (OldResult n E Secret Value) :=
  (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
    (result.1, result.2.1), result.2.2.1.1.1), result.2.2.1.2), result.2.2.2)) <$>
    (simulateQ (CborRawRecordOriginFlatten.full service env crypto codec route serverKid bounds)
      (asModeO mode work)).run (PqxdhDeploymentSecrecy.Ledger.empty, before)

/-- Arbitrary private source instrumentation retains its whole initialized joint state through the literal older raw ledger. -/
theorem old_run_flat (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp))
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : CborRawRecordOriginService.State n E Secret) :
    oldRun service env crypto codec route serverKid bounds mode work created before =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        CborRawRecordOriginFlatten.interpret service codec route
          (CborRawRecordEntropyWorld.program env crypto codec serverKid bounds mode work created before.1.1.1)
          before.1.1.2 before.1.2 before.2 := by
  rcases before with ⟨⟨⟨initial, shell⟩, control⟩, secret⟩
  have represented := CborRawRecordOriginFlatten.native_program service env codec route
    (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode work)) initial shell control secret
  unfold oldRun
  simp only [CborRawRecordEntropyWorld.program, CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at represented
  have mapped := congrArg (fun distribution => (fun result : (Value × PqxdhDeploymentSecrecy.Ledger) ×
    CborRawRecordOriginService.State n E Secret =>
      ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)) <$> distribution) represented
  simp only [PqxdhDeploymentSecrecy.wrap, Functor.map_map, CborRawRecordOriginFlatten.interpret,
    CborRawRecordOriginFlatten.full] at mapped ⊢
  exact mapped

noncomputable def run (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp))
    (env : RegistrationNativeEntropyInterface.Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (initial : E) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret) : ProbComp (Result n E Secret Value) :=
  (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
    CborRawRecordOriginFlatten.interpret service codec route
      (RegistrationNativeEntropyInitialized.program env crypto codec serverKid bounds mode work created initial) shell control secret

/-- The complete ML-pin-aware initialized native ledger transports with every actual private marker and poststate, not only its erased output. -/
theorem run_transport (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp))
    (env : RegistrationNativeEntropyInterface.Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (initial : E) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret) :
    project <$> oldRun service (RegistrationNativeEntropyPort.environment env) crypto codec route serverKid bounds mode
      (RegistrationNativeEntropyCompile.compile mode work) created (((([], initial), shell), control), secret) =
      run service env crypto codec route serverKid bounds mode work created initial shell control secret := by
  rw [old_run_flat]
  unfold run
  rw [← RegistrationNativeEntropyInitialized.program_transport env crypto codec serverKid bounds mode work created initial]
  simp only [project, CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized.old_run_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized.old_run_flat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized.run_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized.run_transport
