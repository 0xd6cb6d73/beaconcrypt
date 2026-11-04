-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveInstallKernel
import BeaconcryptCore.Computational.RegistrationNativeInstallRuntime

/-! Reassociation of the actual local frontend and thin-service states lets finite native owner proofs run against the same physical allocator. The equations retain the complete cursor, Protocol control and arbitrary private-service poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntime
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
variable {n : Nat} {ι KemSK ProviderState Platform Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Platform Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformHiddenAllocationCreate.State n KemSK ProviderState Platform Secret source

abbrev Runtime (n : Nat) (KemSK ProviderState Secret : Type) :=
  RegistrationNativeHiddenEnvironmentWorld.State n (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret

def runtime (before : State n KemSK ProviderState Platform Secret source) :
    Runtime n KemSK ProviderState Secret :=
  (((before.1.1.1.2, before.1.1.2), before.1.2), before.2)

def attach (result : (Value × RegistrationNativePlatformPublicFrontend.State source Platform) ×
    Runtime n KemSK ProviderState Secret) : Value × State n KemSK ProviderState Platform Secret source :=
  (result.1.1, ((((result.1.2, result.2.1.1.1), result.2.1.1.2), result.2.1.2), result.2.2))

noncomputable def publicCallback (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (Runtime n KemSK ProviderState Secret) ProbComp) :=
  fun query => lower service codec route (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query)

/-- Every actual mutable frontend program closes through the same physical World, with no copied allocator state. -/
theorem frontend (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePlatformSelectiveInstallKernel.FrontendM n KemSK Platform source Value)
    (before : State n KemSK ProviderState Platform Secret source) :
    (lower service codec route (RegistrationNativePlatformSelectiveInstallKernel.close setup wire sign seed scalar candidate provider work)).run before =
      attach <$> (simulateQ (publicCallback setup wire sign seed scalar candidate provider service codec route)
        (work.run before.1.1.1.1)).run (runtime before) := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run]
  simp only [RegistrationNativePlatformSelectiveInstallKernel.close, StateT.run]
  rw [RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  have joined := congrArg (fun action => action.run (runtime before))
    (RegistrationNativeHiddenEnvironmentWorld.program_lower service codec route
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) (work.run before.1.1.1.1))
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run] at joined
  change _ = (simulateQ (publicCallback setup wire sign seed scalar candidate provider service codec route)
    (work.run before.1.1.1.1)).run (runtime before) at joined
  simp only [StateT.run] at joined
  rw [← joined]
  simp only [Functor.map_map, attach, runtime]

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntime.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntime.frontend
