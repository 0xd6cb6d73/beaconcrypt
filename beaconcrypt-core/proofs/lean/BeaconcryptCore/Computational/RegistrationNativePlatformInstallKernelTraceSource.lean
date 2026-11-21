-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelProgram
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceSource
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

abbrev Result (n : Nat) (KemSK ProviderState Platform Secret Value : Type) (source : RegistrationNativeMldsa.Source) :=
  (((((Value × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) ×
    RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × CborRecordWorldClient.Shell) ×
      PqxdhRecordLiftProtocol.Control n) × Secret

def attach (result : Result n KemSK ProviderState Platform Secret Value source) : Value × State n KemSK ProviderState Platform Secret source :=
  match result with
  | ((((((value, front), trace), thin), shell), control), secret) =>
      (value, (trace, ((((front, thin), shell), control), secret)))

private def rejoin (result : ((Value × RegistrationNativePlatformPublicFrontend.State source Platform) × RegistrationNativeG2Trace.State) ×
    RegistrationNativeInstallRuntime.Runtime n KemSK ProviderState Secret) : Value × State n KemSK ProviderState Platform Secret source :=
  match result with
  | (((value, front), trace), (((thin, shell), control), secret)) =>
      (value, (trace, ((((front, thin), shell), control), secret)))

/-- Complete typed execution preserves the same full chronological and physical poststate under the actual selective Cbor source. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK ProviderState Platform Secret source) :
    (simulateQ (actual) work).run before =
      attach <$> CborRawRecordOriginFlatten.interpret service codec route
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical sign seed scalar candidate provider)
          ((simulateQ RegistrationNativeG2Trace.handler
            ((simulateQ (QueryImpl.mapStateTBase RegistrationNativePlatformPublicCoinEmbedding.embed
              (RegistrationNativePlatformPublicFrontend.handler setup checks canonical source sign selectedOwner selectedAccept
                (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work).run before.2.1.1.1.1)).run before.1)).run before.2.1.1.1.2)
        before.2.1.1.2 before.2.1.2 before.2.2 := by
  let callback := RegistrationNativeInstallRuntimeTrace.callback setup canonical sign seed scalar candidate provider service codec route
  let current := RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source sign selectedOwner selectedAccept
    (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let frontend := QueryImpl.mapStateTBase RegistrationNativePlatformPublicCoinEmbedding.embed current
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT callback frontend work
    before.2.1.1.1.1 (RegistrationNativePlatformInstallRuntimeTrace.runtime before)
  have kernel : Prod.map id RegistrationNativePlatformInstallKernelProgram.split <$>
      (simulateQ (actual) work).run before =
      (simulateQ (callback.mapStateTBase frontend).flattenStateT work).run
        (before.2.1.1.1.1, RegistrationNativePlatformInstallRuntimeTrace.runtime before) :=
    RegistrationNativePlatformInstallKernelProgram.program setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route work before
  rw [← kernel] at nested
  have first : RegistrationNativePlatformInstallRuntimeTrace.attach <$>
      (simulateQ callback ((simulateQ frontend work).run before.2.1.1.1.1)).run
        (RegistrationNativePlatformInstallRuntimeTrace.runtime before) =
      (simulateQ (actual) work).run before := by
    rw [nested]
    simp only [Functor.map_map, RegistrationNativePlatformInstallKernelProgram.split, RegistrationNativePlatformInstallRuntimeTrace.attach,
      RegistrationNativePlatformInstallRuntimeTrace.runtime, RegistrationNativePlatformInstallRuntime.attach, RegistrationNativePlatformInstallRuntime.runtime,
      Prod.map_def, id_eq, Prod.mk.eta, id_map']
  rw [← first]
  have traced := RegistrationNativeInstallRuntimeTrace.program_source setup canonical sign seed scalar candidate provider service codec route
    ((simulateQ frontend work).run before.2.1.1.1.1) (RegistrationNativePlatformInstallRuntimeTrace.runtime before)
  simp only [RegistrationNativePlatformInstallRuntimeTrace.runtime] at traced
  calc _ = rejoin <$> (simulateQ (RegistrationNativeInstallRuntime.publicCallback setup canonical sign seed scalar candidate provider service codec route)
      ((simulateQ RegistrationNativeG2Trace.handler ((simulateQ frontend work).run before.2.1.1.1.1)).run before.1)).run
        (RegistrationNativePlatformInstallRuntime.runtime before.2) := by
        rw [← traced, Functor.map_map]
        rfl
    _ = _ := by
      change rejoin <$> (simulateQ (fun query => RegistrationNativeHiddenEnvironmentWorld.lower service codec route
        (RegistrationNativeSelectiveHiddenInterpreter.handler setup canonical sign seed scalar candidate provider query)) _).run _ = _
      rw [← RegistrationNativeHiddenEnvironmentWorld.program_lower, RegistrationNativeHiddenEnvironmentWorld.lower_run, Functor.map_map]
      rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceSource.program
