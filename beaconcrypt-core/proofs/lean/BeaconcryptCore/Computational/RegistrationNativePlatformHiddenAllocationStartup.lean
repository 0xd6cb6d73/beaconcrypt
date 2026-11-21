-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK ProviderState Platform Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
/-- The unchanged actual public startup establishes the new complete source/platform allocation invariant after all real constructor and hash effects. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (providerState : ProviderState) (previous : Platform)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (secret : Secret) (started : RegistrationNativeHiddenStartup.Started source)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (after : Secret)
    (supported : (((some started, shell), control), after) ∈ support
      (CborRawRecordOriginFlatten.interpret service codec route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret)) :
    RegistrationNativePlatformHiddenAllocationCore.Holds
      (((((started.native.frontend, previous),
        (RegistrationNativeHiddenInterpreter.initial (n := n) (KemSK := KemSK) providerState, known)), shell), control), after) := by
  have actual := RegistrationNativeHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId identity
    providerState service codec route secret started shell control after supported
  exact ⟨actual.length, actual.indexed, actual.cursor⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup.initialized
