-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace
import BeaconcryptCore.Computational.RegistrationNativeTargetStateMap
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativeInstallOrdinals (messages)
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
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route

local notation "frontend" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source sign selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "original" => fun request => RegistrationNativePlatformSelectiveInstallKernel.embedded (frontend request)
local notation "closed" => QueryImpl.flattenStateT (QueryImpl.mapStateTBase
  (RegistrationNativeInstallRuntimeTrace.callback setup canonical sign seed scalar candidate provider service codec route) original)

def split (before : State n KemSK ProviderState Platform Secret source) :
    RegistrationNativePlatformPublicFrontend.State source Platform × RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret :=
  (before.2.1.1.1.1,RegistrationNativePlatformInstallRuntimeTrace.runtime before)

/-- The literal current callback retains its platform state and complete private trace under a bijective reassociation. -/
theorem query (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source) :
    Prod.map id split <$> (actual request).run before = (closed request).run (split before) := by
  rw [RegistrationNativePlatformInstallRuntimeTrace.typed_source,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformSelectiveInstallKernel.embedded,Functor.map_map,split,
    RegistrationNativePlatformInstallRuntimeTrace.attach,RegistrationNativePlatformInstallRuntimeTrace.runtime,
    RegistrationNativePlatformInstallRuntime.runtime,RegistrationNativePlatformInstallRuntime.attach,StateT.run,Prod.map_def,id_eq]

/-- The complete adaptive program preserves the same frontend/platform and physical private state jointly. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK ProviderState Platform Secret source) :
    Prod.map id split <$> (simulateQ actual work).run before = (simulateQ closed work).run (split before) :=
  RegistrationNativeTargetStateMap.program split actual closed
    (query setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram.program
