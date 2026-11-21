-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
/-! Exact reassociation of a persistent free World service and its physical closing. No controller is replaced: frontend, source chronology, symbolic private state and the complete reached physical state are retained. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing
variable {n : Nat} {KemSK Private Physical Front Value J : Type} {world : OracleSpec J}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT Private (OracleComp world)))
    (physical : QueryImpl world (StateT Physical ProbComp))
noncomputable def closed : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (Private × Physical) ProbComp) :=
  (physical.mapStateTBase implementation).flattenStateT

noncomputable def trace {m : Type → Type} [Monad m]
    (impl : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private m)) :=
  (impl.mapStateTBase RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT
noncomputable def typed {m : Type → Type} [Monad m]
    (impl : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private m))
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)))) :=
  ((trace impl).mapStateTBase controller).flattenStateT

private theorem trace_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private m))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State) (privateBefore : Private) :
    (simulateQ (trace impl) work).run (before,privateBefore) =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ impl ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before)).run privateBefore := by
  rw [trace,OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

private theorem typed_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private m))
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (front : Front) (before : RegistrationNativeSecretWordFrontendTrace.State) (privateBefore : Private) :
    (simulateQ (typed impl controller) work).run (front,(before,privateBefore)) =
      (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
        (simulateQ impl ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
          ((simulateQ controller work).run front)).run before)).run privateBefore := by
  rw [typed,OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [trace_run]
  simp only [bind_pure_comp,Functor.map_map]

/-- Closing the free Word service retains both of its complete state coordinates. -/
theorem word_program (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : Private) (physicalBefore : Physical) :
    (simulateQ physical ((simulateQ implementation work).run before)).run physicalBefore =
      (fun result => ((result.1,result.2.1),result.2.2)) <$>
        (simulateQ (closed implementation physical) work).run (before,physicalBefore) :=
  OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT physical implementation work before physicalBefore

/-- Arbitrary adaptive typed programs commute with the actual physical closing, retaining their full source trace and platform state. -/
theorem program (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (front : Front) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (privateBefore : Private) (physicalBefore : Physical) :
    (fun result => ((result.1,(result.2.1,(result.2.2.1,result.2.2.2.1))),result.2.2.2.2)) <$>
      (simulateQ (RegistrationNativePlatformLorStatefulSupport.traced (closed implementation physical) controller) work).run
        (front,(before,(privateBefore,physicalBefore))) =
      (simulateQ physical ((simulateQ (typed implementation controller) work).run (front,(before,privateBefore)))).run physicalBefore := by
  change (fun result => ((result.1,(result.2.1,(result.2.2.1,result.2.2.2.1))),result.2.2.2.2)) <$>
      (simulateQ (typed (closed implementation physical) controller) work).run
        (front,(before,(privateBefore,physicalBefore))) = _
  rw [typed_run,typed_run]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]
  rw [word_program implementation physical ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
    ((simulateQ controller work).run front)).run before) privateBefore physicalBefore]
  simp only [Functor.map_map]

/-- A literal current callback is the single-query instance of the same full-state association. -/
theorem query (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (front : Front) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (privateBefore : Private) (physicalBefore : Physical) :
    (fun result => ((result.1,(result.2.1,(result.2.2.1,result.2.2.2.1))),result.2.2.2.2)) <$>
      (RegistrationNativePlatformLorStatefulSupport.traced (closed implementation physical) controller request).run
        (front,(before,(privateBefore,physicalBefore))) =
      (simulateQ physical ((typed implementation controller request).run (front,(before,privateBefore)))).run physicalBefore := by
  simpa only [simulateQ_spec_query] using program implementation physical controller (liftM (RegistrationNativeRawAdapter.TypedSpec.query request)) front before privateBefore physicalBefore

/-- The literal all-mode raw compiler retains its original complete ledger through the same physical state association. -/
theorem full (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : Front) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (privateBefore : Private) (physicalBefore : Physical) :
    (fun result => ((result.1,(result.2.1,(result.2.2.1,(result.2.2.2.1,result.2.2.2.2.1)))),result.2.2.2.2.2)) <$>
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds
        (RegistrationNativePlatformLorStatefulSupport.traced (closed implementation physical) controller) mode work
        (front,(before,(privateBefore,physicalBefore))) =
      (simulateQ physical ((fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ (typed implementation controller) (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work)).run
          (front,(before,privateBefore)))).run physicalBefore := by
  have compared := congrArg (Functor.map (fun result => ((result.1.1.1,(result.1.1.2,result.1.2)),result.2)))
    (program implementation physical controller (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work)
      front before privateBefore physicalBefore)
  simpa only [RegistrationNativeFullCompiler.compile_run,simulateQ_map,StateT.run_map,Functor.map_map] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.word_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.word_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorPhysicalClosing.full
