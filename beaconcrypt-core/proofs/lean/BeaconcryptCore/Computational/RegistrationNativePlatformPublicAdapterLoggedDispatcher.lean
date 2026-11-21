-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedActualSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The canonical dispatcher observes actual source signing and first-record operations in Bundle, Build and Finish. All other operations carry the same source log. Erasing only the observations recovers the exact original source dispatcher under arbitrary adaptive clients and Rust stopping behavior. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
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
variable {Value :Type}
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def stages :QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec
    (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R (P×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P))
  | .inl (.inr (.bundle index))=>RegistrationNativePlatformPublicAdapterSourceLogLift.ofOutcome
      (fun before=>RegistrationNativePlatformPublicAdapterBundleLoggedSource.operation configuration created before index)
  | .inl (.inr (.build handle payload))=>RegistrationNativePlatformPublicAdapterSourceLogLift.ofOutcome
      (fun before=>RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.operation configuration before handle payload)
  | .inl (.inr (.finish index input))=>RegistrationNativePlatformPublicAdapterSourceLogLift.ofOutcome
      (fun before=>RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation configuration created before index input)
  | query=>RegistrationNativePlatformPublicAdapterSourceLogLift.lift
      (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created query)

noncomputable def interpreter :QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec
    (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R (P×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)):=
  fun query=>RegistrationNativePlatformPublicAdapterSourceLogLift.callback query (stages configuration created query)

theorem query_erase (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (interpreter configuration created query) before=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created query)
        (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=by
  apply RegistrationNativePlatformPublicAdapterSourceLogLift.callback_erase
  intro current
  cases query with
  | inr refused=>exact RegistrationNativePlatformPublicAdapterSourceLogLift.lift_erase _ current
  | inl publicQuery=>cases publicQuery with
    | inl coins=>exact RegistrationNativePlatformPublicAdapterSourceLogLift.lift_erase _ current
    | inr command=>cases command with
      | bundle index=>
        rw [stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        exact RegistrationNativePlatformPublicAdapterBundleLoggedSource.erase configuration created current index
      | build handle payload=>
        rw [stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        rw [←RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.operation_source configuration current handle payload]
        exact RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation_erase configuration current handle payload
      | finish index input=>
        rw [stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        exact RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation_erase configuration created current index input
      | _=>exact RegistrationNativePlatformPublicAdapterSourceLogLift.lift_erase _ current

theorem program_erase (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.outcome <$>
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (simulateQ (interpreter configuration created) work) before=
      RegistrationNativePlatformPublicAdapterSourceRuntime.run
        (simulateQ (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created) work)
        (RegistrationNativePlatformPublicAdapterSourceEvents.store before) :=
  RegistrationNativePlatformPublicAdapterSourceEvents.program (interpreter configuration created)
    (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created)
    (query_erase configuration created) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher.query_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher.program_erase
