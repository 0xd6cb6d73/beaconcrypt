-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceSource
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
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
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route

local notation "selected" => Selected setup seed scalar candidate
local notation "invariant" => RegistrationNativeInstallLedger.Holds events slots Valid selected


open RegistrationNativePlatformInstallKernelTraceSource (Result attach)

/-- The actual current full-ledger source derives its final ordinal-to-hidden-slot invariant jointly with the complete record trace. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Platform Secret source) (prior : Valid before) (empty : events before = [])
    (result : Result n KemSK ProviderState Platform Secret (Value × RegistrationNativeLedger.State) source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
          (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
            (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
              view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before.2.1.1.1.1))).run before.1)).run before.2.1.1.1.2)
      before.2.1.1.2 before.2.1.2 before.2.2)) :
    invariant ((attach result).1.2,(attach result).2) := by
  have reached : attach result ∈ support ((simulateQ actual
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical serverKeyId bounds mode work)).run before) := by
    rw [RegistrationNativePlatformInstallKernelTraceSource.program,support_map]
    refine ⟨result,?_,rfl⟩
    simpa only [← QueryImpl.simulateQ_mapStateTBase_run,RegistrationNativePlatformPublicFrontend.run] using supported
  have fullReached : ((attach result).1.1,((attach result).1.2,(attach result).2)) ∈ support
      (RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds actual mode work before) := by
    rw [RegistrationNativeFullCompiler.compile_run,support_map]
    exact ⟨attach result,reached,rfl⟩
  exact RegistrationNativePlatformInstallKernelLedger.run setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route serverKeyId bounds mode work before _ prior empty fullReached

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant.run
