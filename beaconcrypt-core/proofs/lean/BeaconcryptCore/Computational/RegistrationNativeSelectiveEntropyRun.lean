-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyAdaptive
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyExecution

/-! The complete actual thin native original-ledger execution has its initialized entropy interpretation. It retains the reached shared CTX cache, actual record control, literal full native ledger and both local states. Its only local invariant is actual allocation correspondence, derived separately from the effectful startup and preserved by all native callbacks. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run interpret_map)
open PqxdhRecordLiftIdeal (CtxPrivate ctxInterpreter KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι KemSK ProviderState Value Reader Response E : Type} {base : OracleSpec ι}

def finish (created : PqxdhLiveServerConstruction.Created Unit)
    (result : (Value × RegistrationNativeLedger.State) × RegistrationNativeHiddenEnvironmentWorld.State n E (CtxPrivate n)) :
    RegistrationNativeEntropyRun.Result n E Value :=
  ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)

noncomputable def nativeRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    ProbComp (RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value) :=
  (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created, result.1.1.1.1.1,
    (result.1.1.1.1.2, result.1.1.1.2)), result.1.2), result.2)) <$>
    CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      (RegistrationNativeSelectiveHiddenInterpreter.run setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds mode work before.1 before.2) shell control secret

/-- Concrete stateful closure of the entire original ledger is the actual thin native World execution. -/
theorem native_lower (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    nativeRun modes replace setup checks wire codec route source credential seed scalar candidate provider selectedOwner selectedAccept serverKeyId
      bounds mode work created before shell control secret =
      finish created <$> (lower (ctxInterpreter modes replace setup codec) codec route
        (simulateQ (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept)
          (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
            (RegistrationNativeInterface.asModeO mode work)))).run (((before, shell), control), secret) := by
  rw [lower_run, ← RegistrationNativeSelectiveEntropyExecution.run_source setup checks wire credential seed scalar candidate provider
    selectedOwner selectedAccept serverKeyId bounds mode work before.1 before.2, interpret_map]
  simp only [nativeRun, finish, Functor.map_map]

/-- Initialized entropy execution is the same full stateful World lowering with its original complete native ledger. -/
theorem entropy_lower (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : RegistrationNativeEntropyInterface.Environment n E) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : E) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :
    RegistrationNativeEntropyInitialized.run modes replace setup codec route env serverKeyId bounds mode work created before shell control secret =
      finish created <$> (lower (ctxInterpreter modes replace setup codec) codec route
        (simulateQ (RegistrationNativeEntropyWorld.native env)
          (RegistrationNativeLedger.wrap setup.source.crypto codec serverKeyId bounds
            (RegistrationNativeInterface.asModeO mode work)))).run (((before, shell), control), secret) := by
  rw [lower_run]
  simp only [RegistrationNativeEntropyInitialized.run, RegistrationNativeEntropyInitialized.program, interpret_map,
    Functor.map_map, finish]

/-- Actual adaptive native execution has the original entropy interface from its derived local allocation invariant. -/
theorem run_source (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds (((before, shell), control), secret)) :
    nativeRun modes replace setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept serverKeyId
      bounds mode work created before shell control secret =
      RegistrationNativeEntropyInitialized.run modes replace setup (RegistrationNativeWire.ledgerCodec wire) route
        (environment setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (pure none))
        serverKeyId bounds mode work created before shell control secret := by
  rw [native_lower, entropy_lower modes replace setup]
  exact congrArg (fun distribution => finish created <$> distribution)
    (RegistrationNativeSelectiveEntropyAdaptive.program_source setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept (pure none) (ctxInterpreter modes replace setup (RegistrationNativeWire.ledgerCodec wire)) (RegistrationNativeWire.ledgerCodec wire) route _ _ valid)

/-- Actual thin native record-ideal fresh guessing retains its byte-accurate entropy term and full original ledger. -/
theorem fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : State n KemSK ProviderState source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds (((before, shell), control), secret)) :
    𝒟[RegistrationNativeEntropyFresh.event claim <$>
      nativeRun (fun _ => .random) id setup checks wire (RegistrationNativeWire.ledgerCodec wire) route source credential seed scalar candidate provider selectedOwner selectedAccept
        serverKeyId bounds .P work created before shell control secret] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [run_source (fun _ => .random) id setup checks wire route source credential seed scalar candidate provider selectedOwner selectedAccept
    serverKeyId bounds .P work created before shell control secret valid]
  exact RegistrationNativeEntropyInitialized.fresh_bytes setup (RegistrationNativeWire.ledgerCodec wire) route _ serverKeyId bounds work claim created before shell control secret

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.native_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.native_lower
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.entropy_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.entropy_lower
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.run_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun.fresh_bytes
