-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLowModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram
/-! Erasing the private typed journal from the same source LowSpec execution recovers the unchanged complete native ledger program. Public source Slice operands, private rejected sends, result values, ledger, native state and persistent platform state are retained; no source or event correspondence is a caller premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error Value :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
local notation "native"=>RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential
local notation "typed"=>RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) setup checks configuration.agreement.representation created credential
  configuration.keyView configuration.sealFailure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
  configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
  (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
  (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem runtime_native (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source) :
    Prod.map id Prod.fst <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential) work).run before=
    (RegistrationNativePlatformPackedState.pack (simulateQ native
      (simulateQ RegistrationNativePlatformPublicAdapterLowSpec.nativeAdapter work))).run before.1 :=by
  rw [RegistrationNativePlatformPublicAdapterAuditLowModel.native_program]
  unfold RegistrationNativePlatformPublicAdapterAuditLowModel.coreModel
  rw [QueryImpl.simulateQ_compose,←RegistrationNativePlatformPackedState.simulate_pack]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem program (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source) :
    Prod.map id Prod.fst <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
        (RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
          serverKid bounds mode work)).run before=
    (RegistrationNativePlatformPackedState.pack (simulateQ typed
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKid bounds mode
        (RegistrationNativePlatformPublicAdapterInterface.compile mode work)))).run before.1 :=by
  rw [runtime_native,RegistrationNativePlatformPublicAdapterLedgerCompile.program_native]
  unfold RegistrationNativePlatformPublicAdapterDispatcherCore.native
  rw [RegistrationNativePlatformPublicAdapterRawProgram.program]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram.runtime_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram.runtime_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram.program
