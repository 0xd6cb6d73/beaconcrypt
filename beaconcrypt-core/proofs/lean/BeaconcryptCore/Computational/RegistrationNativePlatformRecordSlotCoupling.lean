-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling
/-! Opaque slot provenance is an analysis output of the original hidden-install client before materialization. The same known/hidden coupling retains it and charges exactly the original repeated-role audit event. No key or slot-reconstruction security assumption is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativePlatformRecordSlotGhost (program)
open RegistrationNativePlatformG3RecordCoupling (known hidden)
open RegistrationNativeG3GuardedCoupling (audit)
open RegistrationNativeG3AuditedWorld (Seeds seeded)
open RegistrationNativeG3GuardedWorld (marked)
open PqxdhRecordLiftWorld (State)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (seeds : Seeds n) (work : OracleComp (WorldSpec n) A)
    (ghost : RegistrationNativePlatformRecordSlotGhost.State n) (before : State n)

/-- Erasing the analysis ID receipts retains the full known-side record/cache observation. The opaque IDs were recorded before conversion to known kernels. -/
theorem known_erase :
    (fun result => (result.1.1,result.2)) <$> known setup codec route seeds (program work ghost) before =
      known setup codec route seeds work before := by
  have erased := RegistrationNativePlatformRecordSlotGhost.interpreted_erase
    (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds) work ghost before
  have mapped := congrArg (Functor.map (fun result => (result.1,RegistrationNativePlatformPublicWorldObservation.recordView result.2))) erased
  simpa only [known,Functor.map_map] using mapped

/-- Erasing the same analysis coordinate retains the complete guarded hidden-side observation, including failed calls. -/
theorem hidden_erase :
    (fun result => (result.1.1,result.2)) <$> hidden setup codec route (program work ghost) before =
      hidden setup codec route work before := by
  have erased := RegistrationNativePlatformRecordSlotGhost.interpreted_erase
    (CborRecordWorldSimulation.guarded setup codec route) work ghost before
  have mapped := congrArg (Functor.map (fun result => (result.1,RegistrationNativePlatformPublicWorldObservation.recordView result.2))) erased
  simpa only [RegistrationNativePlatformG3RecordCoupling.hidden,Functor.map_map] using mapped

/-- The slot observer leaves the entire actual audit state and its sticky repeated-role event unchanged. -/
theorem audit_erase :
    (fun result => (result.1.1,result.2)) <$> audit setup codec route seeds (program work ghost) before =
      audit setup codec route seeds work before := by
  have erased := RegistrationNativePlatformRecordSlotGhost.interpreted_erase
    ((marked setup codec route seeds true) ∘ₛ RegistrationNativeG3Materialize.materialize) work ghost (before,false)
  simpa only [audit,QueryImpl.simulateQ_compose] using erased

/-- The complete slot-aware known/hidden comparison pays exactly the original known-side repeated-role charge, with no new owner factor or resource premise. -/
theorem fixed_bound :
    discreteDistance (known setup codec route seeds (program work ghost) before)
      (hidden setup codec route (program work ghost) (seeded seeds before)) ≤
        (Pr{let result ← audit setup codec route seeds work before}[result.2.2=true]).toReal := by
  have sameBool := congrArg (Functor.map (fun result => result.2.2)) (audit_erase setup codec route seeds work ghost before)
  simp only [Functor.map_map] at sameBool
  have sameProbability := congrArg (fun game => Pr{let flag ← game}[flag=true]) sameBool
  simp only [prEvent_map] at sameProbability
  rw [← sameProbability]
  exact RegistrationNativePlatformG3RecordCoupling.fixed_bound setup codec route seeds (program work ghost) before
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.known_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.known_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.hidden_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.hidden_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.audit_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.audit_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCoupling.fixed_bound
