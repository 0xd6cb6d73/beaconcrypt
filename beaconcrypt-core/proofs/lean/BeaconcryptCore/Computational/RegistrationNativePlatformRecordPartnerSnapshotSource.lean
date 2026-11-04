-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceSource
/-! Erasing only the joint snapshot observer recovers the literal persistent native G2 execution under the same selective backend and physical service. The final native and physical states are retained, with only product association changed. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformRecordPartnerSlotTrace (State)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
local notation "joint" => RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate provider physical

def project (value : A × State n KemSK ProviderState Physical) :=
  (((value.1,value.2.2.1),value.2.2.2.1),value.2.2.2.2)

private theorem backend_run (work : OracleComp (Spec n KemSK) A)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState × Physical) :
    (simulateQ backend work).run before =
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ physical ((simulateQ actual work).run before.1)).run before.2 := by
  rw [RegistrationNativePlatformRecordPartnerSlotInput.closed,OracleComp.simulateQ_flattenStateT_run,
    ←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]

/-- The complete supported joint snapshot has the same original G2/native/physical execution after the named projection. -/
theorem native_source (work : OracleComp (Spec n KemSK) A) (before : State n KemSK ProviderState Physical) :
    project <$> (simulateQ joint work).run before =
      (simulateQ physical ((simulateQ actual ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1)).run before.2.2.1)).run before.2.2.2 := by
  have erased := RegistrationNativePlatformRecordPartnerSlotTrace.trace_source setup wire sign seed scalar candidate provider physical work before
  have projected := congrArg (fun tree => (fun value : A × (RegistrationNativeG2Trace.State ×
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState × Physical)) =>
        (((value.1,value.2.1),value.2.2.1),value.2.2.2)) <$> tree) erased
  rw [QueryImpl.Stateful.simulateQ_link_run,backend_run] at projected
  simp only [Functor.map_map] at projected
  change project <$> (simulateQ joint work).run before =
    id <$> (simulateQ physical ((simulateQ actual ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1)).run before.2.2.1)).run before.2.2.2 at projected
  simpa only [id_map] using projected


end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource.native_source
