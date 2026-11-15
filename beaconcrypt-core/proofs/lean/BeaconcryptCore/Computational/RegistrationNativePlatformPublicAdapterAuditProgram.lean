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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram
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
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed (n:=n) configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential

omit [PublicWrapperPlatform.CryptoOperations] in
theorem program (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source) :
    (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
      (RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKid bounds mode work)).run before=
    (simulateQ (RegistrationNativePlatformPublicAdapterTypedAudit.handler typed failure)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKid bounds mode
        (RegistrationNativePlatformPublicAdapterInterface.compile mode work))).run before :=by
  rw [RegistrationNativePlatformPublicAdapterAuditLowModel.raw_program]
  unfold RegistrationNativePlatformPublicAdapterAuditModel.raw RegistrationNativeRawAdapter.handler
  have compiled:=RegistrationNativePlatformPublicAdapterLedgerCompile.program_typed setup.source.crypto wire serverKid bounds mode work
  rw [QueryImpl.simulateQ_compose] at compiled
  have adapterEq :RegistrationNativeRawAdapter.adapter RegistrationNativeConcreteCodec.wire=
      RegistrationNativeRawAdapter.adapter wire :=by
    funext query
    cases query with
    | inl coin=>rfl
    | inr command=>cases command <;>rfl
  rw [QueryImpl.simulateQ_compose,adapterEq,compiled]

omit [PublicWrapperPlatform.CryptoOperations] in
theorem flag (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source) :
    Prod.map id RegistrationNativePlatformPublicAdapterTypedAudit.flag <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
        (RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
          serverKid bounds mode work)).run before=
    (simulateQ (RegistrationNativePlatformPublicAdapterTypedAudit.badHandler typed failure)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKid bounds mode
        (RegistrationNativePlatformPublicAdapterInterface.compile mode work))).run
      (RegistrationNativePlatformPublicAdapterTypedAudit.flag before) :=by
  rw [program]
  exact RegistrationNativePlatformPublicAdapterTypedAudit.flag_program typed failure _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram.flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram.flag
