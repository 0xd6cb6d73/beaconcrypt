-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceSource
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelLedger

/-! The original complete ledger and native installation trace are coupled to the physical hidden slots of their same actual selective Cbor execution. This consumes the derived callback laws rather than assuming a target-origin or whole-game correspondence. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceInvariant
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallKernelTraceSource (Result attach)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual full-ledger Cbor source derives the same final ordinal-to-hidden-slot invariant jointly with its complete trace. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Secret source) (prior : Valid before) (empty : events before = [])
    (result : Result n KemSK ProviderState Secret (Value × RegistrationNativeLedger.State) source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
            serverKeyId bounds mode work before.2.1.1.1.1)).run before.1)).run before.2.1.1.1.2)
      before.2.1.1.2 before.2.1.2 before.2.2)) :
    RegistrationNativeInstallLedger.Holds events slots Valid (Selected setup seed scalar candidate)
      ((attach result).1.2, (attach result).2) := by
  have reached : attach result ∈ support
      ((simulateQ (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept)
        (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before) := by
    rw [RegistrationNativeInstallKernelTraceSource.program, support_map]
    exact ⟨result, supported, rfl⟩
  have fullReached : ((attach result).1.1, ((attach result).1.2, (attach result).2)) ∈ support
      (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept) mode work before) := by
    rw [RegistrationNativeFullCompiler.compile_run, support_map]
    exact ⟨attach result, reached, rfl⟩
  exact RegistrationNativeInstallKernelLedger.run setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept serverKeyId bounds mode work before _ prior empty fullReached

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceInvariant.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelTraceInvariant.run
