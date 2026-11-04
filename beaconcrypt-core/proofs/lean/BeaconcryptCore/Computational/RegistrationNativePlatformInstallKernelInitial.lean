-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup

/-! Literal effectful native startup establishes physical owner allocation and Protocol safety for the chronological kernel. Constructor and ML generation failure probabilities, the public Server import and the same shared hash state remain in the original startup AST. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots)
variable {n : Nat} {ι KemSK ProviderState Platform Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def initial (started : RegistrationNativeHiddenStartup.Started source) (providerState : ProviderState)
    (previous : Platform) (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    State n KemSK ProviderState Platform Secret source :=
  (RegistrationNativeG2Trace.initial,
    (((((started.native.frontend, previous), (RegistrationNativeHiddenInterpreter.initial providerState, known)), shell), control), secret))

/-- The actual successful startup supplies the physical allocation and safety certificate consumed by all later native installation callbacks. -/
theorem initialized (setup : PqxdhServerAuthExperiment.Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (providerState : ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (secret : Secret) (started : RegistrationNativeHiddenStartup.Started source)
    (previous : Platform) (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (after : Secret)
    (supported : (((some started, shell), control), after) ∈ support
      (CborRawRecordOriginFlatten.interpret service codec route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret)) :
    Valid (initial (KemSK := KemSK) started providerState previous known shell control after) := by
  constructor
  · exact RegistrationNativePlatformHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId identity
      providerState previous known service codec route secret started shell control after supported
  · exact (RegistrationNativeRecordHandleSlots.interpreted service codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftProtocolHistory.initial_safe secret
      (((some started, shell), control), after) supported).1

/-- Chronology starts empty after the same actual startup; startup itself performs no ongoing material installation. -/
theorem empty (started : RegistrationNativeHiddenStartup.Started source) (providerState : ProviderState)
    (previous : Platform) (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    events (initial (KemSK := KemSK) started providerState previous known shell control secret) = [] := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial.initialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial.empty
