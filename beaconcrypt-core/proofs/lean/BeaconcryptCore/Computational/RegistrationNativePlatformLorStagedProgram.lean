-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontend
/-! Generic interpretation reassociation retains the complete controller, chronological observer and persistent private state over any lawful base monad. It changes only product association and has no source, record-service or callback premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram
variable {I J K Front Trace Private A : Type} {spec : OracleSpec I} {requests : OracleSpec J} {observations : OracleSpec K}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (implementation : QueryImpl spec (StateT Private m))
    (observer : QueryImpl observations (StateT Trace (OracleComp spec)))

theorem controller_program (controller : QueryImpl requests (StateT Front (OracleComp spec)))
    (work : OracleComp requests A) (before : Front × Private) :
    (simulateQ (QueryImpl.mapStateTBase implementation controller).flattenStateT work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation ((simulateQ controller work).run before.1)).run before.2 := by
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

theorem trace_program (work : OracleComp observations A) (before : Trace × Private) :
    (simulateQ (QueryImpl.mapStateTBase implementation observer).flattenStateT work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation ((simulateQ observer work).run before.1)).run before.2 := by
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

theorem program (controller : QueryImpl requests (StateT Front (OracleComp observations)))
    (work : OracleComp requests A) (before : Front × (Trace × Private)) :
    (fun result => (((result.1,result.2.1),result.2.2.1),result.2.2.2)) <$>
      (simulateQ (QueryImpl.mapStateTBase (QueryImpl.mapStateTBase implementation observer).flattenStateT controller).flattenStateT work).run before =
      (simulateQ implementation ((simulateQ observer ((simulateQ controller work).run before.1)).run before.2.1)).run before.2.2 := by
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [trace_program]
  simp only [bind_pure_comp,Functor.map_map,id_map']

end BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.controller_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.controller_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.trace_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.trace_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStagedProgram.program
