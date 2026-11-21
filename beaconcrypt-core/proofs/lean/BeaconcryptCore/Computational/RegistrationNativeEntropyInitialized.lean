-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordEntropyPreamble
import BeaconcryptCore.Computational.RegistrationNativeEntropyFresh

/-! The native ML-pin-aware original ledger transports from an already initialized World state, retaining its actual CTX cache and cursor. No pure-start environment is used to supply a CTX digest. The reached native environment still owns no private record seeds or shared World lens. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK E Value Reader Response : Type} {base : OracleSpec ι}

noncomputable def program (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) :
    OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value) :=
  (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result)) <$>
    (simulateQ (RegistrationNativeEntropyWorld.native env)
      (RegistrationNativeLedger.wrap crypto codec serverKid bounds (RegistrationNativeInterface.asModeO mode work))).run initial

/-- The complete native ledger, including the extra ML creation pin, is restored from the exact initialized older entropy-port program. -/
theorem program_transport (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) :
    RegistrationNativeEntropyProgram.outcome <$>
      CborRawRecordEntropyWorld.program (RegistrationNativeEntropyPort.environment env) crypto codec serverKid bounds mode
        (RegistrationNativeEntropyCompile.compile mode work) created ([], initial) =
      program env crypto codec serverKid bounds mode work created initial := by
  have executed := RegistrationNativeEntropyExecution.wrapped_mode env crypto codec serverKid bounds mode work ([], initial)
  have observed := congrArg (fun distribution => (fun result =>
    some (PqxdhRegistrationJointServerBirth.encode created, result)) <$> distribution) executed
  simpa only [program, CborRawRecordEntropyWorld.program, RegistrationNativeEntropyProgram.outcome,
    map_bind, map_pure, bind_pure_comp, Functor.map_map, Option.map_some] using observed

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) : ProbComp (RegistrationNativeEntropyRun.Result n E Value) :=
  (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
    CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      (program env setup.source.crypto codec serverKid bounds mode work created initial) shell control secret

/-- The actual initialized native World execution preserves the exact complete ledger and shared CTX state under entropy-port restoration. -/
theorem run_transport (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    RegistrationNativeEntropyRun.project <$>
      CborRawRecordEntropyInitial.run modes replace setup codec route (RegistrationNativeEntropyPort.environment env)
        serverKid bounds mode (RegistrationNativeEntropyCompile.compile mode work) created (((([], initial), shell), control), secret) =
      run modes replace setup codec route env serverKid bounds mode work created initial shell control secret := by
  rw [CborRawRecordEntropyWorld.run_flat]
  unfold run
  rw [← program_transport env setup.source.crypto codec serverKid bounds mode work created initial]
  simp only [RegistrationNativeEntropyRun.project, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The native original fresh ledger has the byte-accurate bound after any actual public startup effects in the same cache. -/
theorem fresh_bytes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (initial : E) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    𝒟[RegistrationNativeEntropyFresh.event claim <$>
      run (fun _ => .random) id setup codec route env serverKid bounds .P work created initial shell control secret] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← run_transport, Functor.map_map]
  simp only [RegistrationNativeEntropyFresh.project_event]
  exact CborRawRecordEntropyPreamble.fresh_bytes setup codec route (RegistrationNativeEntropyPort.environment env)
    serverKid bounds (RegistrationNativeEntropyCompile.compile .P work) claim created (((([], initial), shell), control), secret)

end BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.program_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.program_transport
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.run_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.run_transport
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized.fresh_bytes
