-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun

/-! Actual selective native callbacks transport through their entropy interface under any private record service, retaining the full cursor/control/private state. This source equation therefore applies with an actual sticky marker before any marker erasure or event averaging. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run interpret_map)
variable {n : Nat} {ι KemSK ProviderState Value Reader Response E Secret : Type} {base : OracleSpec ι}

def finish (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (result : (Value × RegistrationNativeLedger.State) × RegistrationNativeHiddenEnvironmentWorld.State n E Secret) :
    RegistrationNativeRecordServiceInitialized.Result n E Secret Value :=
  ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)

noncomputable def nativeRun (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    ProbComp (RegistrationNativeRecordServiceInitialized.Result n (State n KemSK ProviderState source) Secret Value) :=
  (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created, result.1.1.1.1.1,
    (result.1.1.1.1.2, result.1.1.1.2)), result.1.2), result.2)) <$>
    CborRawRecordOriginFlatten.interpret service codec route
      (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds mode work before.1 before.2) shell control secret

/-- Concrete stateful closure of the entire original ledger is the actual thin native World execution. -/
theorem native_lower (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    nativeRun service setup checks wire codec route source credential seed scalar candidate provider selectedOwner selectedAccept serverKeyId
      bounds mode work created before shell control secret =
      finish created <$> (lower service codec route
        (simulateQ (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept)
          (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
            (RegistrationNativeInterface.asModeO mode work)))).run (((before, shell), control), secret) := by
  rw [lower_run, ← RegistrationNativeSelectiveEntropyExecution.run_source setup checks wire credential seed scalar candidate provider
    selectedOwner selectedAccept serverKeyId bounds mode work before.1 before.2, interpret_map]
  simp only [nativeRun, finish, Functor.map_map]

/-- Initialized entropy execution is the same full stateful World lowering with its original complete native ledger. -/
theorem entropy_lower (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : RegistrationNativeEntropyInterface.Environment n E) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : E) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    RegistrationNativeRecordServiceInitialized.run service env setup.source.crypto codec route serverKeyId bounds mode work created before shell control secret =
      finish created <$> (lower service codec route
        (simulateQ (RegistrationNativeEntropyWorld.native env)
          (RegistrationNativeLedger.wrap setup.source.crypto codec serverKeyId bounds
            (RegistrationNativeInterface.asModeO mode work)))).run (((before, shell), control), secret) := by
  rw [lower_run]
  simp only [RegistrationNativeRecordServiceInitialized.run, RegistrationNativeEntropyInitialized.program, interpret_map,
    Functor.map_map, finish]

/-- Actual adaptive native execution has the original entropy interface from its derived local allocation invariant. -/
theorem native_source (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds (((before, shell), control), secret)) :
    nativeRun service setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept serverKeyId
      bounds mode work created before shell control secret =
      RegistrationNativeRecordServiceInitialized.run service
        (environment setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (pure none))
        setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) route serverKeyId bounds mode work created before shell control secret := by
  rw [native_lower, entropy_lower service setup]
  exact congrArg (fun distribution => finish created <$> distribution)
    (RegistrationNativeSelectiveEntropyAdaptive.program_source setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept (pure none) service (RegistrationNativeWire.ledgerCodec wire) route _ _ valid)

end BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.native_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.native_lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.entropy_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.entropy_lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordServiceRun.native_source
