-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntime
import BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformPublicCoinEmbedding (embed)
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

abbrev Runtime (n : Nat) (KemSK ProviderState Secret : Type) :=
  RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret

def runtime (before : State n KemSK ProviderState Platform Secret source) : Runtime n KemSK ProviderState Secret :=
  (before.1, RegistrationNativePlatformInstallRuntime.runtime before.2)

def attach (result : (Value × RegistrationNativePlatformPublicFrontend.State source Platform) × Runtime n KemSK ProviderState Secret) :
    Value × State n KemSK ProviderState Platform Secret source :=
  (result.1.1, (result.2.1, (RegistrationNativePlatformInstallRuntime.attach (result.1, result.2.2)).2))

noncomputable abbrev callback := @RegistrationNativeInstallRuntimeTrace.callback

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "owned" => RegistrationNativeMldsa.owned source credential
local notation "frontend" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source owned selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

omit primitive in
private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal corrected callback, including persistent P, runs through its explicit embedded tree in one unchanged chronological private runtime. -/
theorem typed_source (query : TypedSpec.Domain) (before : State n KemSK ProviderState Platform Secret source) :
    (RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query).run before =
      attach <$> (simulateQ (RegistrationNativeInstallRuntimeTrace.callback setup canonical owned seed scalar candidate provider service codec route)
        (simulateQ embed ((frontend query).run before.2.1.1.1.1))).run (runtime before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeHiddenEnvironmentWorld.lower service codec route
      (RegistrationNativePlatformSelectiveInstallKernel.close setup canonical owned seed scalar candidate provider
        (RegistrationNativePlatformSelectiveInstallKernel.front frontend before.1 query))).run before.2 = _
  rw [RegistrationNativePlatformInstallRuntime.frontend]
  simp only [RegistrationNativePlatformSelectiveInstallKernel.front, StateT.run, simulateQ_map, map_apply, Functor.map_map]
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativePlatformInstallRuntime.publicCallback setup canonical owned seed scalar candidate provider service codec route)
    RegistrationNativeG2Trace.handler
    (simulateQ embed ((frontend query).run before.2.1.1.1.1)) before.1 (RegistrationNativePlatformInstallRuntime.runtime before.2)
  simp only [StateT.run] at nested
  rw [nested]
  simp only [RegistrationNativeInstallRuntimeTrace.callback, Functor.map_map, runtime,
    RegistrationNativePlatformInstallRuntime.attach, RegistrationNativePlatformInstallRuntime.runtime,
    Prod.map_def, id_eq]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace.typed_source
