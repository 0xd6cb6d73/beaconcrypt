-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
/-! The literal complete native ledger program retains the actual reserve tails through its existing ML-pin mailbox transport. No source syntax or whole-handler contract is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformOriginSourceTails (HasTails)
variable {n : Nat} {Platform Failure Reader Response Value : Type}

/-- The literal ML-aware full ledger is lowered through its actual compiler, retaining the entire mailbox, external state, CBOR cursor and private-record control. -/
theorem wrapped (env : RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (before : RegistrationNativeEntropyPort.State Platform) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) :
    HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      (RegistrationNativePlatformOriginNativeTails.source (RegistrationNativeEntropyPort.environment env)
        (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) codec route
        (simulateQ RegistrationNativeEntropyCore.compiler (RegistrationNativeLedger.wrap crypto codec serverKeyId bounds work))
          before shell control) :=
  RegistrationNativePlatformOriginNativeTails.program _ _ _ _ _ _ _ _

/-- The actual native ledger runs at the same reached cursor and record control through the existing full-state transport, retaining the complete restored native result. -/
theorem complete (env : RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : Platform)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler
          (RegistrationNativePlatformGatedNativeEntropy.program env reserve crypto codec serverKeyId bounds mode work created initial)).run shell)).run control) := by
  rw [←RegistrationNativePlatformGatedNativeEntropy.program_transport env reserve crypto codec serverKeyId bounds mode work created initial]
  let original := PqxdhDeploymentSecrecy.wrap crypto codec serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work))
  have tails := RegistrationNativePlatformOriginNativeTails.program (RegistrationNativeEntropyPort.environment env)
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) codec route original ([],initial) shell control
  let observe := fun result : (((Value × PqxdhDeploymentSecrecy.Ledger) × RegistrationNativeEntropyPort.State Platform) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n =>
    ((RegistrationNativeEntropyProgram.outcome
      (some (PqxdhRegistrationJointServerBirth.encode created,result.1.1)),result.1.2),result.2)
  have mapped := RegistrationNativePlatformOriginSourceTails.map observe _ tails
  simpa only [RegistrationNativePlatformGatedEntropyWorld.program,
    RegistrationNativePlatformOriginNativeTails.source,simulateQ_map,StateT.run_map,Functor.map_map,original,observe] using mapped

/-- The actual initialized native World client and its original ledger have the same reserve-tail syntax after exact result restoration; no successful callback or fixed allocator outcome is required. -/
theorem program (env : RegistrationNativeEntropyInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (initial : Platform) :
    HasTails (RegistrationNativeEntropyPort.State Platform) Failure
      (RegistrationNativeRecordOriginProgram.program codec route
        (RegistrationNativePlatformGatedNativeEntropy.program env reserve crypto codec serverKeyId bounds mode work created initial)) := by
  have tails := complete env reserve crypto codec route serverKeyId bounds mode work created initial CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl
  have mapped := RegistrationNativePlatformOriginSourceTails.map
    (fun result=> (RegistrationNativeRecordPackage.encode result.1.1,result.2)) _ tails
  simpa only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
    PqxdhRecordLiftProtocol.schedule,CborRecordWorldClient.client,simulateQ_map,StateT.run_map,Functor.map_map] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.wrapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerTails.program
