-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentJoint

/-! Reassociation of the actual local frontend and thin-service states lets finite native owner proofs run against the same physical allocator. The equations retain the complete cursor, Protocol control and arbitrary private-service poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK ProviderState Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeHiddenEnvironmentJoint.State n KemSK ProviderState Secret source

def runtime (before : State n KemSK ProviderState Secret source) :
    RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret :=
  (((before.1.1.1.2, before.1.1.2), before.1.2), before.2)

def attach (result : (Value × RegistrationNativePublicFrontend.State source) ×
    RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret) : Value × State n KemSK ProviderState Secret source :=
  (result.1.1, ((((result.1.2, result.2.1.1.1), result.2.1.1.2), result.2.1.2), result.2.2))

noncomputable def publicCallback (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret) ProbComp) :=
  fun query => lower service codec route (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider query)

/-- Every actual mutable frontend program closes through the same physical World, with no copied allocator state. -/
theorem frontend (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK ProviderState Secret source) :
    (lower service codec route (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider work)).run before =
      attach <$> (simulateQ (publicCallback setup wire sign seed scalar provider service codec route)
        (work.run before.1.1.1.1)).run (runtime before) := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run,
    RegistrationNativeHiddenEnvironmentEffects.close_run, RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  have joined := congrArg (fun action => action.run (runtime before))
    (RegistrationNativeHiddenEnvironmentWorld.program_lower service codec route
      (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) (work.run before.1.1.1.1))
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run] at joined
  change _ = (simulateQ (publicCallback setup wire sign seed scalar provider service codec route)
    (work.run before.1.1.1.1)).run (runtime before) at joined
  rw [← joined]
  simp only [Functor.map_map, attach, runtime]

/-- The finite native callback interpreter is exactly the composed public request lowering. -/
theorem trusted_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    simulateQ (RegistrationNativeHiddenAllocationRuntime.callback setup wire sign seed scalar provider service codec route) work =
      simulateQ (publicCallback setup wire sign seed scalar provider service codec route)
        (simulateQ RegistrationNativeHiddenAllocationRuntime.lift work) := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact RegistrationNativeHiddenEnvironmentWorld.program_lower service codec route
    (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider)
    (RegistrationNativeHiddenAllocationRuntime.lift query)

def nativeAttach (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (before : RegistrationNativePublicFrontend.State source)
    (result : ((Value × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment) ×
      RegistrationNativeHiddenAllocationRuntime.State n KemSK ProviderState Secret) : Value × State n KemSK ProviderState Secret source :=
  attach ((result.1.1.1, { before with beacons := RegistrationNativePublicOwners.pack selected publicPrekey result.1.1.2, environment := result.1.2 }), result.2)

/-- Actual native birth and publication execute through precisely the same reached physical allocator before scalar erasure and local-state reassembly. -/
theorem native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK ProviderState Secret source) :
    (lower service codec route (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider
      (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)))).run before =
      nativeAttach selected publicPrekey before.1.1.1.1 <$>
        (simulateQ (RegistrationNativeHiddenAllocationRuntime.callback setup wire sign seed scalar provider service codec route)
          ((work.run (before.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.1.1.1.environment)).run (runtime before) := by
  let observed := fun result : (Value × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment =>
    (result.1.1, { before.1.1.1.1 with beacons := RegistrationNativePublicOwners.pack selected publicPrekey result.1.2, environment := result.2 })
  have actual : (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)).run before.1.1.1.1 =
      observed <$> simulateQ RegistrationNativeHiddenAllocationRuntime.lift
        ((work.run (before.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.1.1.1.environment) := by
    simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativePublicOwners.executeLocal, StateT.run,
      simulateQ_map, Functor.map_map, observed, RegistrationNativeHiddenAllocationRuntime.lift, QueryImpl.simulateQ_compose]
  rw [frontend, actual, simulateQ_map, StateT.run_map, ← trusted_program]
  simp only [Functor.map_map, observed]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.frontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.trusted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution.native
