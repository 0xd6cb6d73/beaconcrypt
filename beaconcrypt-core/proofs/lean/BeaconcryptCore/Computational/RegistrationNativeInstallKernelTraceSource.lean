-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelProgram

/-! A complete actual typed execution is the literal native frontend AST observed by G2Trace, interpreted by the selective material service and the same cursor-aware Cbor World. The equation retains the joint frontend, trace, allocator control and arbitrary private-service state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceSource
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Result (n : Nat) (KemSK ProviderState Secret Value : Type) (source : RegistrationNativeMldsa.Source) :=
  (((((Value × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) ×
    RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) × CborRecordWorldClient.Shell) ×
      PqxdhRecordLiftProtocol.Control n) × Secret

def attach (result : Result n KemSK ProviderState Secret Value source) : Value × State n KemSK ProviderState Secret source :=
  match result with
  | ((((((value, front), trace), thin), shell), control), secret) =>
      (value, (trace, ((((front, thin), shell), control), secret)))

private def rejoin (result : ((Value × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) ×
    RegistrationNativeInstallRuntime.Runtime n KemSK ProviderState Secret) : Value × State n KemSK ProviderState Secret source :=
  match result with
  | (((value, front), trace), (((thin, shell), control), secret)) =>
      (value, (trace, ((((front, thin), shell), control), secret)))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)

/-- Complete typed execution preserves the same full chronological and physical poststate under the actual selective Cbor source. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK ProviderState Secret source) :
    (simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work).run before =
      attach <$> CborRawRecordOriginFlatten.interpret service codec route
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          ((simulateQ RegistrationNativeG2Trace.handler
            ((simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept
              (setup.dh.publicKey scalar)) work).run before.2.1.1.1.1)).run before.1)).run before.2.1.1.1.2)
        before.2.1.1.2 before.2.1.2 before.2.2 := by
  let callback := RegistrationNativeInstallRuntimeTrace.callback setup wire sign seed scalar candidate provider service codec route
  let frontend := RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT callback frontend work
    before.2.1.1.1.1 (RegistrationNativeInstallRuntimeTrace.runtime before)
  have kernel : Prod.map id RegistrationNativeInstallKernelProgram.split <$>
      (simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work).run before =
      (simulateQ (callback.mapStateTBase frontend).flattenStateT work).run
        (before.2.1.1.1.1, RegistrationNativeInstallRuntimeTrace.runtime before) :=
    RegistrationNativeInstallKernelProgram.program setup checks wire sign seed scalar candidate provider service codec route
      selectedOwner selectedAccept work before
  rw [← kernel] at nested
  have first : RegistrationNativeInstallRuntimeTrace.attach <$>
      (simulateQ callback ((simulateQ frontend work).run before.2.1.1.1.1)).run
        (RegistrationNativeInstallRuntimeTrace.runtime before) =
      (simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) work).run before := by
    rw [nested]
    simp only [Functor.map_map, RegistrationNativeInstallKernelProgram.split, RegistrationNativeInstallRuntimeTrace.attach,
      RegistrationNativeInstallRuntimeTrace.runtime, RegistrationNativeInstallRuntime.attach, RegistrationNativeInstallRuntime.runtime,
      Prod.map_def, id_eq, Prod.mk.eta, id_map']
  rw [← first]
  have traced := RegistrationNativeInstallRuntimeTrace.program_source setup wire sign seed scalar candidate provider service codec route
    ((simulateQ frontend work).run before.2.1.1.1.1) (RegistrationNativeInstallRuntimeTrace.runtime before)
  simp only [RegistrationNativeInstallRuntimeTrace.runtime] at traced
  calc _ = rejoin <$> (simulateQ (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route)
      ((simulateQ RegistrationNativeG2Trace.handler ((simulateQ frontend work).run before.2.1.1.1.1)).run before.1)).run
        (RegistrationNativeInstallRuntime.runtime before.2) := by
        rw [← traced, Functor.map_map]
        rfl
    _ = _ := by
      change rejoin <$> (simulateQ (fun query => RegistrationNativeHiddenEnvironmentWorld.lower service codec route
        (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query)) _).run _ = _
      rw [← RegistrationNativeHiddenEnvironmentWorld.program_lower, RegistrationNativeHiddenEnvironmentWorld.lower_run, Functor.map_map]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceSource.program
