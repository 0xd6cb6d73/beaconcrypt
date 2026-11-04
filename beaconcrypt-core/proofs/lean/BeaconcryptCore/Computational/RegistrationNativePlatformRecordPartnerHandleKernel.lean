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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel
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
abbrev State (n : Nat) (KemSK ProviderState Platform Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformPublicFrontend.State source Platform ×
    RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret)

def kernel (before : State n KemSK ProviderState Platform Secret source) :
    RegistrationNativePlatformSelectiveInstallKernel.State n KemSK ProviderState Platform Secret source :=
  let (front,(_ghost,(trace,(privateBefore,(shell,(control,secret)))))) := before
  (trace,(( ((front,privateBefore),shell),control),secret))

def project (result : Value × State n KemSK ProviderState Platform Secret source) := (result.1,kernel result.2)

def repack (result : (((Value × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) ×
    RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × RegistrationNativePlatformLorIdealPhysical.State n Secret) :=
  let ((((value,front),trace),privateAfter),(shell,(control,secret))) := result
  (value,(trace,((((front,privateAfter),shell),control),secret)))

noncomputable def typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK ProviderState Platform Secret source) ProbComp) := fun query before=>
  (fun result=>(result.1.1,(result.1.2,result.2))) <$>
    (simulateQ joint (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed ((frontend query).run before.1))).run before.2

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before=Prod.map change id <$>work before := StateT.run_map change work before

/-- Erasing only the snapshot observer and reassociating actual World state recovers the literal current selective Kernel callback. -/
theorem typed_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source) :
    project <$> (typed setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before=
    (RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run (kernel before) := by
  have same := congrArg (Functor.map (repack (Platform := Platform)))
    (RegistrationNativePlatformRecordPartnerSnapshotSource.native_source setup canonical owned seed scalar candidate provider physical
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed ((frontend query).run before.1)) before.2)
  rw [RegistrationNativePlatformLorIdealPhysical.program_source] at same
  simpa only [typed,project,kernel,repack,RegistrationNativePlatformRecordPartnerSnapshotSource.project,
    RegistrationNativePlatformSelectiveInstallKernel.typed,StateT.run,RegistrationNativeHiddenEnvironmentWorld.lower,
    RegistrationNativePlatformSelectiveInstallKernel.close,RegistrationNativePlatformSelectiveInstallKernel.front,
    simulateQ_map,map_apply,RegistrationNativeHiddenEnvironmentWorld.interpret_map,Functor.map_map,Prod.map_def,id_eq] using same


/-- The actual physical allocation invariant persists on the same joint callback without an index or source-state premise. -/
theorem typed_holds (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState Platform Secret source)
    (prior : RegistrationNativePlatformHiddenAllocationCore.Holds (kernel before).2)
    (supported : result∈support ((typed setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before)) :
    RegistrationNativePlatformHiddenAllocationCore.Holds (kernel result.2).2 := by
  have reached := Set.mem_image_of_mem project supported
  rw [←support_map,typed_source] at reached
  exact RegistrationNativePlatformSelectiveInstallKernel.typed_holds setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query (kernel before) (project result) prior reached
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel.typed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel.typed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleKernel.typed_holds
