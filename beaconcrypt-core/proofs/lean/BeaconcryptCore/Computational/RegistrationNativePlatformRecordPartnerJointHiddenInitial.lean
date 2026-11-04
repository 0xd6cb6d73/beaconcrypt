-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelTraceInvariant
/-! The actual effectful startup initializes the chronological hidden-handle invariant while retaining the complete warmed private service state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK ProviderState Platform Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route
/-- The literal startup initializes the same kernel with arbitrary retained hidden material and known-word caches. -/
theorem startup (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (previous : Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (secret : Secret)
    (born : RegistrationNativeHiddenStartup.Started source)
    (after : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (supported : (some born,after)∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,secret))) :
    RegistrationNativePlatformInstallKernelStorage.Valid
      (RegistrationNativeG2Trace.initial,(((((born.native.frontend,previous),privateBefore),after.1),after.2.1),after.2.2)) := by
  rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map] at supported
  obtain ⟨actual,called,equal⟩ := supported
  have exactCall : (((some born,after.1),after.2.1),after.2.2)∈support
      (CborRawRecordOriginFlatten.interpret service codec route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret) := by
    have named : actual=(((some born,after.1),after.2.1),after.2.2) := by
      cases actual with | mk left state =>
        cases left with | mk left control =>
          cases left with | mk value shell =>
            cases equal
            rfl
    simpa only [named] using called
  have initial := RegistrationNativePlatformInstallKernelInitial.initialized setup ensureInit identityIndex serverKeyId identity
    privateBefore.1.provider service codec route secret born previous privateBefore.2 after.1 after.2.1 after.2.2 exactCall
  exact ⟨⟨initial.1.length,initial.1.indexed,initial.1.cursor⟩,initial.2⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial.startup
