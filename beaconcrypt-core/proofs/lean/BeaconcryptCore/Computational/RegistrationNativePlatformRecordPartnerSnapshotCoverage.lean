-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceSource
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt
/-! The common ordered slot/descriptor observer is the exact persistent closing of the existing public-slot and G2 observers. Only product association changes; dropping the slot observer recovers the original complete G2 execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotCoverage
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformRecordPartnerSlotTrace (State handler)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "actual" => handler setup wire sign seed scalar candidate provider physical

/-- Every current hidden handle is covered by an earlier same-role successful receipt on the literal joint execution. -/
theorem program (work : OracleComp (Spec n KemSK) A) (before : State n KemSK ProviderState Physical)
    (valid : RegistrationNativePlatformRecordSlotReceipt.Complete before.1.snapshot)
    (result : A × State n KemSK ProviderState Physical)
    (supported : result∈support ((simulateQ actual work).run before)) :
    RegistrationNativePlatformRecordSlotReceipt.Complete result.2.1.snapshot := by
  rw [RegistrationNativePlatformRecordPartnerSlotTrace.program_source setup wire sign seed scalar candidate provider physical,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact RegistrationNativePlatformRecordSlotReceipt.interpreted backend
    ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1) before.1 valid before.2.2 reached called

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotCoverage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotCoverage.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotCoverage.program
