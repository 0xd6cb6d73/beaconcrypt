-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The canonical initialized execution runs actual source objects and backend with their actual operation log. Its observer receives the actual returned source Store, including terminal primitive cache and persistent platform state. Every ledger and roster event is a marginal of this one execution. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
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
variable [AdapterServerConstructorPrimitive.Standard]
variable {Value :Type}
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
variable (decision :RegistrationNativeExperiment.Public→(Value×RegistrationNativeLedger.State)→
  RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P→Bool)

noncomputable def initial (world :PqxdhRecordLiftWorld.State n)
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source) (previous :P) :
    RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P :=
  let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.initialStore world ready previous
  {stored with backend:=(stored.backend.1,(stored.backend.2,[]))}

def observe (publication :RegistrationNativeExperiment.Public)
    (output :RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P (Value×RegistrationNativeLedger.State)) :Bool×P :=
  (match output.1 with
    | .ok (value,objects)=>decision publication value (RegistrationNativePlatformPublicAdapterSourceRuntime.join objects output.2)
    | .fail _ | .div=>false,output.2.2.1)

noncomputable def profile :StateT P ProbComp Bool :=fun previous=>do
  let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
  match packet.val.1.ready with
  | none=>pure (false,previous)
  | some ready=> observe decision ready.initial.public <$>
    (RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedDispatcher.interpreter configuration ready.initial.created)
        (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public))
      (initial packet.val.2 ready previous))

/-- Every ledger/roster observer is a marginal of this same actual initialized source execution. -/
theorem profile_ledger (ledgerDecision :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R→Bool) :
    profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (fun _ value stored=>ledgerDecision (value,RegistrationNativePlatformPublicAdapterSourceRuntime.objects stored))=
    RegistrationNativePlatformPublicAdapterLedgerExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary ledgerDecision :=by
  funext previous
  unfold profile RegistrationNativePlatformPublicAdapterLedgerExecution.profile
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>rfl
  | some ready=>
    dsimp only
    have erased:=RegistrationNativePlatformPublicAdapterLoggedDispatcher.program_erase configuration ready.initial.created
      (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public)
      (initial world ready previous)
    have observed:=congrArg (fun computation=>RegistrationNativePlatformPublicAdapterLedgerExecution.observe ledgerDecision <$>computation) erased
    simp only [Functor.map_map] at observed
    exact observed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution.profile_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution.profile_ledger
