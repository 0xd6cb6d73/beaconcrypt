-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueNative
/-! Genuine completed-table initialization derives allocator goodness, and the actual effectful startup derives the same handle-kernel allocation and empty-origin receipts at its full warm physical poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK ProviderState Platform Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

/-- Filling the initial material table changes no empty address or allocator property. -/
theorem cold_private (budget : PqxdhDeploymentInterface.Budget)
    (materials : RegistrationNativeG3Tables.MaterialTable (budget.cap 4+budget.cap 5)) :
    RegistrationNativeSelectiveHiddenDictionaryRun.Good
      (RegistrationNativePlatformG3UniformOpaqueNative.privateState (KemSK:=KemSK)
        (ProviderState:=RegistrationNativeKemSwitchSource.Phase) none budget materials) := by
  exact RegistrationNativeHiddenServiceInvariant.initial

variable (setup : Setup base KemSK)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation service codec route

/-- Actual source startup supplies the same full allocation receipt and empty opaque origins, without changing its reached private state. -/
theorem startup (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (previous : Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (secret : Secret)
    (born : RegistrationNativeHiddenStartup.Started source)
    (after : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (supported : (some born,after)∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run
        (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,secret)))) :
    RegistrationNativePlatformRecordPartnerHandleLedger.Held
      ((born.native.frontend,previous),(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,after))) ∧
    RegistrationNativePlatformRecordSlotGhost.initial.origins=RegistrationNativePlatformRecordSlotControl.origins after.2.1 := by
  constructor
  · exact (RegistrationNativePlatformRecordPartnerJointHiddenInitial.startup setup service codec route
      ensureInit identityIndex serverKeyId identity previous privateBefore secret born after supported).1
  · have kept:=RegistrationNativePlatformRecordPartnerJointInitial.startup service codec route setup source
      ensureInit identityIndex serverKeyId identity
      (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,secret)) (some born,after) supported
    change RegistrationNativePlatformRecordSlotControl.origins after.2.1=
      RegistrationNativePlatformRecordSlotControl.origins PqxdhRecordLiftProtocol.initialControl at kept
    rw [kept]
    rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial.cold_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial.cold_private
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial.startup
