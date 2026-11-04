import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceSource
/-! Erasing only the joint snapshot observer recovers the literal persistent native G2 execution under the same selective backend and physical service. The final native and physical states are retained, with only product association changed. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource
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

def handleList (role : PqxdhRecordLiftInterface.Role) (ghost : RegistrationNativePlatformPublicRecordSlots.State n) :=
  RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role ghost.snapshot

def observe (role : PqxdhRecordLiftInterface.Role) (result : A × State n KemSK ProviderState Physical) :=
  (result.1,handleList role result.2.1)

/-- The same actual joint snapshot handle list is the literal free handle observer closed by the original private backend. Only the other analysis coordinates are erased. -/
theorem source (role : PqxdhRecordLiftInterface.Role) (work : OracleComp (Spec n KemSK) A)
    (before : State n KemSK ProviderState Physical) :
    observe role <$> (simulateQ joint work).run before=
      (simulateQ backend ((simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role) work).run (handleList role before.1))).run' before.2.2 := by
  let traced := (simulateQ RegistrationNativeG2Trace.handler work).run before.2.1
  let initial := (handleList role before.1)
  have g2Erased := congrArg (fun tree=>(simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler (KemSK := KemSK) role) tree).run initial)
    (RegistrationNativeG2Trace.program_erase work before.2.1)
  simp only [simulateQ_map,StateT.run_map] at g2Erased
  have slots := RegistrationNativePlatformRecordPartnerSnapshotHandles.program_source role traced before.1
  have freeLaw : (fun result : (A × RegistrationNativeG2Trace.State) × RegistrationNativePlatformPublicRecordSlots.State n=>
      (result.1.1,handleList role result.2)) <$>RegistrationNativePlatformPublicRecordSlots.program traced before.1=
      (simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role) work).run initial := by
    have mappedSlots := congrArg (Functor.map (fun result : (A × RegistrationNativeG2Trace.State) × List PqxdhDeploymentInterface.Handle=>(result.1.1,result.2))) slots
    simp only [Functor.map_map,Prod.map_def,id_eq] at mappedSlots
    exact mappedSlots.trans g2Erased
  have closed := congrArg (fun tree=>(simulateQ backend tree).run' before.2.2) freeLaw
  simp only [simulateQ_map,StateT.run'_eq,StateT.run_map,Functor.map_map] at closed
  rw [RegistrationNativePlatformRecordPartnerSlotTrace.program_source,Functor.map_map]
  simpa only [observe,StateT.run'_eq,traced,initial] using closed

/-- An actual reached handle-list observation belongs to that same free callback observer, rather than an independently selected source history. -/
theorem supported (role : PqxdhRecordLiftInterface.Role) (work : OracleComp (Spec n KemSK) A)
    (before : State n KemSK ProviderState Physical) (result : A × State n KemSK ProviderState Physical)
    (reached : result∈support ((simulateQ joint work).run before)) :
    observe role result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role) work).run (handleList role before.1)) := by
  have current := Set.mem_image_of_mem (observe role) reached
  rw [←support_map,source] at current
  exact OracleComp.support_simulateQ_run'_subset backend _ before.2.2 current
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandleSource.supported
