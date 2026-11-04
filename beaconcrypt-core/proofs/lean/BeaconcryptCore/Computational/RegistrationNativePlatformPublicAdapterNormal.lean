-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! A concrete source runner with proved normal Rust return can expose that unique actual return without a failure continuation or fallback source object. Its complete terminal state is retained in the exact erasure law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal
variable {A S : Type}

def Normal (work : ProbComp (RustM A ×S)) : Prop :=
  ∀result,result∈support work →∃returned,result.1=.ok returned

noncomputable def returned (work : ProbComp (RustM A ×S)) (normal : Normal work)
    (result : {value //value∈support work}) : A :=
  Classical.choose (normal result.val result.property)

theorem returned_exact (work : ProbComp (RustM A ×S)) (normal : Normal work)
    (result : {value //value∈support work}) : result.val.1=.ok (returned work normal result) :=
  Classical.choose_spec (normal result.val result.property)

noncomputable def select (work : ProbComp (RustM A ×S)) (normal : Normal work) : ProbComp (A ×S) :=
  (fun result=>(returned work normal result,result.val.2)) <$>PFunctor.FreeM.attachSupp work

theorem erase (work : ProbComp (RustM A ×S)) (normal : Normal work) :
    Prod.map RustM.ok id <$>select work normal=work := by
  unfold select
  rw [Functor.map_map]
  have point : (fun result : {value //value∈support work} =>
      Prod.map RustM.ok id (returned work normal result,result.val.2))=Subtype.val := by
    funext result
    simp only [Prod.map,id_eq,←returned_exact work normal result,Prod.mk.eta]
  rw [point]
  exact PFunctor.FreeM.map_attachSupp work

theorem state (runner : StateT S ProbComp (RustM A)) (normal : ∀before,Normal (runner.run before))
    (before : S) :
    Prod.map RustM.ok id <$> (fun state=>select (runner.run state) (normal state)) before=runner.run before :=
  erase (runner.run before) (normal before)

theorem unique (work : ProbComp (RustM A ×S)) (normal : Normal work)
    (actual : ProbComp (A ×S)) (same : Prod.map RustM.ok id <$>actual=work) :
    select work normal=actual := by
  apply (map_inj_right (f:=Prod.map RustM.ok id) ?_).mp
  · exact (erase work normal).trans same.symm
  · intro first second equal
    change (RustM.ok first.1,first.2)=(RustM.ok second.1,second.2) at equal
    apply Prod.ext
    · exact RustM.ok.inj (congrArg (fun result : RustM A ×S=>result.1) equal)
    · exact congrArg (fun result : RustM A ×S=>result.2) equal

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.returned_exact' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.returned_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.state
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormal.unique
