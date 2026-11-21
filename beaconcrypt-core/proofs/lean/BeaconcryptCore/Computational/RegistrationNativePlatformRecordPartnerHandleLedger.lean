import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerTypedHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelFreeStep
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallStep (RoleStep)
open RegistrationNativeInstallTypedEntry (entry)
open BeaconcryptCore.Refinement
variable {Value : Type}
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "owned" => RegistrationNativeMldsa.owned source credential
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "frontend" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source owned selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "joint" => RegistrationNativePlatformRecordPartnerSlotTrace.handler setup canonical owned seed scalar candidate provider physical
open RegistrationNativePlatformRecordPartnerHandleKernel (State kernel)
local notation "actual" => RegistrationNativePlatformRecordPartnerHandleKernel.typed setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route

def handleList (role : PqxdhRecordLiftInterface.Role) (before : State n KemSK ProviderState Platform Secret source) :=
  RegistrationNativePlatformRecordPartnerSnapshotHandleSource.handleList role before.2.1

def Held (before : State n KemSK ProviderState Platform Secret source) : Prop :=
  RegistrationNativePlatformHiddenAllocationCore.Holds (kernel before).2

/-- The exact actual closed snapshot callback supplies its own local successful handle suffix. The physical index invariant is derived from the same Kernel state. -/
theorem typed_handles (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : Held before) (supported : result∈support ((actual query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    handleList role result.2=handleList role before++RegistrationNativeInstallOrdinals.handles role [RegistrationNativeInstallTypedEntry.entry query result.1] := by
  have indexed : RegistrationNativeHiddenAllocationOwners.Indexed before.1.1.beacons := prior.indexed
  simp only [RegistrationNativePlatformRecordPartnerHandleKernel.typed,StateT.run,support_map] at supported
  obtain ⟨reached,called,rfl⟩ := supported
  have localResult := RegistrationNativePlatformRecordPartnerSnapshotHandleSource.supported setup canonical owned seed scalar candidate provider physical
    role (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed ((frontend query).run before.1)) before.2 reached called
  exact RegistrationNativePlatformRecordPartnerTypedHandles.handler setup checks canonical source owned selectedOwner selectedAccept
    (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer role query before.1 indexed
      (handleList role before) (RegistrationNativePlatformRecordPartnerSnapshotHandleSource.observe role reached) localResult

/-- The full unchanged source compiler derives its complete successful-handle ledger from concrete role callbacks and actual physical allocation preservation. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK ProviderState Platform Secret source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK ProviderState Platform Secret source))
    (prior : Held before) (supported : result∈support (RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds actual mode work before)) :
    Held result.2.2 ∧ ∀role,handleList role result.2.2=handleList role before++RegistrationNativeInstallOrdinals.handles role result.2.1.transcript := by
  apply RegistrationNativePlatformRecordPartnerHandlesLedger.full_program actual canonical handleList Held
    (typed_handles setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    (RegistrationNativePlatformRecordPartnerHandleKernel.typed_holds setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer service codec route)
    setup.source.crypto serverKeyId bounds (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty,before)
      (fun role=>handleList role before) prior _ result supported
  intro role
  simp only [RegistrationNativeLedger.empty,RegistrationNativeInstallOrdinals.handles,List.filterMap_nil,List.append_nil]

private theorem program_source (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK ProviderState Platform Secret source) :
    (simulateQ actual work).run before=(fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ joint (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed ((simulateQ frontend work).run before.1))).run before.2 := by
  let embedded := QueryImpl.mapStateTBase RegistrationNativePlatformPublicCoinEmbedding.embed frontend
  have linked : actual=QueryImpl.Stateful.link embedded joint := by
    funext query current
    rcases current with ⟨frontBefore,jointBefore⟩
    change (actual query).run (frontBefore,jointBefore)=(QueryImpl.Stateful.link embedded joint query).run (frontBefore,jointBefore)
    rw [QueryImpl.Stateful.link_impl_apply_run]
    rfl
  rw [linked,QueryImpl.Stateful.simulateQ_link_run,←QueryImpl.simulateQ_mapStateTBase_run RegistrationNativePlatformPublicCoinEmbedding.embed frontend work before.1]
  rfl

/-- The whole original public source run has exactly this concrete full compiler outcome after product association alone. -/
theorem source_run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK ProviderState Platform Secret source) :
    RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds actual mode work before=
      (fun result=> (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      (simulateQ joint (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source owned selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before.1))).run before.2 := by
  rw [RegistrationNativeFullCompiler.compile_run,program_source,Functor.map_map]
  rfl

/-- A supported original public snapshot execution therefore supplies the exact successful-handle list of its same native ledger, without a callback or handle-correspondence premise. -/
theorem from_source (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK ProviderState Platform Secret source)
    (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
      RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (prior : Held before) (supported : result∈support ((simulateQ joint (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run setup checks wire source owned selectedOwner selectedAccept (setup.dh.publicKey scalar)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before.1))).run before.2)) :
    ∀role,RegistrationNativePlatformRecordPartnerSnapshotHandleSource.handleList role result.2.1=
      handleList role before++RegistrationNativeInstallOrdinals.handles role result.1.1.2.transcript := by
  have reached := Set.mem_image_of_mem (fun result=> (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) supported
  rw [←support_map,←source_run] at reached
  exact (full setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer service codec route serverKeyId bounds mode work before _ prior reached).2
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.typed_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.typed_handles
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.full
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.source_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.from_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger.from_source
