-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRun
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenStartup

/-! The actual effectful native startup and full original-ledger program execute in one cursor/Protocol/CTX interpretation. Constructor and ML failures retain their reached World state. Success continues from exactly the cache populated by native initialization and the actual ML public-pin hash. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open PqxdhRecordLiftIdeal (CtxPrivate ctxInterpreter KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Outcome (n : Nat) (KemSK ProviderState Value : Type) (source : RegistrationNativeMldsa.Source) :=
  Option (PqxdhLiveServerConstruction.Created Unit ×
    (((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) ×
      RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState))

abbrev Result (n : Nat) (KemSK ProviderState Value : Type) (source : RegistrationNativeMldsa.Source) :=
  ((Outcome n KemSK ProviderState Value source × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n

abbrev Started (n : Nat) (source : RegistrationNativeMldsa.Source) :=
  ((Option (RegistrationNativeHiddenStartup.Started source) × CborRecordWorldClient.Shell) ×
    PqxdhRecordLiftProtocol.Control n) × CtxPrivate n

/-- The final observation keeps the complete original ledger, both local states, public record control and private CTX state. -/
def project (result : Result n KemSK ProviderState Value source) :
    RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value :=
  ((result.1.1.1.map (fun finished =>
    (PqxdhRegistrationJointServerBirth.encode finished.1, finished.2.1.1, (finished.2.1.2, finished.2.2))), result.1.2), result.2)

noncomputable def after (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (started : Started n source) : ProbComp (RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value) :=
  match started.1.1.1 with
  | none => pure ((none, started.1.2), started.2)
  | some born => RegistrationNativeSelectiveEntropyRun.nativeRun modes replace setup checks wire
      (RegistrationNativeWire.ledgerCodec wire) route source born.native.credential seed scalar candidate provider
      selectedOwner selectedAccept serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
      born.created (born.native.frontend, RegistrationNativeSelectiveHiddenInterpreter.initial providerState)
      started.1.1.2 started.1.2 started.2

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (secret : CtxPrivate n) : ProbComp (RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value) :=
  project <$> CborRawRecordOriginFlatten.interpret
    (ctxInterpreter modes replace setup (RegistrationNativeWire.ledgerCodec wire)) (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeSelectiveHiddenStartup.program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary)
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret

/-- The complete actual startup program splits at its literal reached success/failure, retaining that exact shared cache for the full original native ledger. -/
theorem run_start (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (secret : CtxPrivate n) :
    run modes replace setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary secret =
      (CborRawRecordOriginFlatten.interpret
        (ctxInterpreter modes replace setup (RegistrationNativeWire.ledgerCodec wire)) (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret >>= fun started =>
          after modes replace setup checks wire route source seed scalar candidate provider providerState selectedOwner selectedAccept serverKeyId bounds mode adversary started) := by
  unfold run RegistrationNativeSelectiveHiddenStartup.program
  rw [CborRawRecordOriginFlatten.interpret_bind, map_bind]
  apply bind_congr
  intro started
  rcases started with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none => simp only [CborRawRecordOriginFlatten.interpret_pure, map_pure, project, Option.map_none, after]
  | some born =>
      simp only [bind_pure_comp]
      rw [RegistrationNativeHiddenEnvironmentWorld.interpret_map, Functor.map_map]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup.run_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup.run_start
