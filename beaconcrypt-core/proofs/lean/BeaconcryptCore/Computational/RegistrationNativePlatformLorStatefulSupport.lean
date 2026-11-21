-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace
/-! State reassociation and support projection for the literal Word controller under any persistent stateful interpretation. The World service is not closed to a particular record implementation. The original frontend, platform state, chronological observer and every returned reply are retained; only the explicitly projected private coordinate is omitted by a support conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
variable {n : Nat} {KemSK Front Private Value : Type}
abbrev Spec (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordInterface.Spec n KemSK
abbrev State (Front Private : Type) := Front × Private
abbrev TracedState (Front Private : Type) := Front × (RegistrationNativeSecretWordFrontendTrace.State × Private)
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT Front (OracleComp (Spec n KemSK))))
noncomputable def typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State Front Private) ProbComp) :=
  (QueryImpl.mapStateTBase implementation controller).flattenStateT
noncomputable def trace : QueryImpl (Spec n KemSK)
    (StateT (RegistrationNativeSecretWordFrontendTrace.State × Private) ProbComp) :=
  (QueryImpl.mapStateTBase implementation RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT
noncomputable def traced : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (TracedState Front Private) ProbComp) :=
  (QueryImpl.mapStateTBase (trace implementation) controller).flattenStateT

theorem typed_run (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State Front Private) :
    (typed implementation controller query).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation ((controller query).run before.1)).run before.2 :=
  QueryImpl.flattenStateT_mapStateTBase_apply_run _ _ _ _ _

theorem typed_support (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State Front Private)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State Front Private)
    (supported : result ∈ support ((typed implementation controller query).run before)) :
    (result.1,result.2.1) ∈ support ((controller query).run before.1) := by
  rw [typed_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset implementation _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

theorem trace_program (work : OracleComp (Spec n KemSK) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private) :
    (simulateQ (trace implementation) work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before.1)).run before.2 := by
  rw [trace,OracleComp.simulateQ_flattenStateT_run,← QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

theorem trace_support (work : OracleComp (Spec n KemSK) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : Value × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result ∈ support ((simulateQ (trace implementation) work).run before)) :
    (result.1,result.2.1) ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before.1) := by
  rw [trace_program,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  apply OracleComp.support_simulateQ_run'_subset implementation _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

theorem traced_support (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState Front Private)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState Front Private)
    (supported : result ∈ support ((traced implementation controller query).run before)) :
    ((result.1,result.2.1),result.2.2.1) ∈ support
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler ((controller query).run before.1)).run before.2.1) := by
  rw [traced,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  exact trace_support implementation _ before.2 reached called

theorem program_trace (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : TracedState Front Private) :
    (fun result => (((result.1,result.2.1),result.2.2.1),result.2.2.2)) <$>
      (simulateQ (traced implementation controller) work).run before =
        (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
          ((simulateQ controller work).run before.1)).run before.2.1)).run before.2.2 := by
  rw [traced,OracleComp.simulateQ_flattenStateT_run,← QueryImpl.simulateQ_mapStateTBase_run]
  rw [trace_program]
  simp only [bind_pure_comp,Functor.map_map,id_map']

theorem program_support (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : TracedState Front Private)
    (result : Value × TracedState Front Private)
    (supported : result ∈ support ((simulateQ (traced implementation controller) work).run before)) :
    ((result.1,result.2.1),result.2.2.1) ∈ support
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler ((simulateQ controller work).run before.1)).run before.2.1) := by
  have mapped := Set.mem_image_of_mem (fun result : Value × TracedState Front Private =>
    (((result.1,result.2.1),result.2.2.1),result.2.2.2)) supported
  rw [←support_map,program_trace] at mapped
  apply OracleComp.support_simulateQ_run'_subset implementation _ before.2.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.typed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.typed_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.typed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.typed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.trace_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.trace_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.trace_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.trace_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.traced_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.traced_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.program_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.program_trace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.program_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport.program_support
