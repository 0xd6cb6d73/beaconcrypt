-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorStartup
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame
open BeaconcryptCore.Computational
variable {n : Nat}

private theorem sampled {A : Type} (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A×PqxdhRecordLiftWorld.State n)
    (supported : result∈support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    result.2.server=before.server ∧ result.2.owners=before.owners := by
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,support_map] at supported
  obtain ⟨inner,_called,rfl⟩:=supported
  exact ⟨rfl,rfl⟩

theorem keys (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (before : PqxdhRecordLiftWorld.State n)
    (result : Option (AdapterServerConstructorJoint.Prepared source)×PqxdhRecordLiftWorld.State n)
    (supported : result∈support ((AdapterServerConstructorStartup.keys source ensureInit).run before)) :
    result.2.server=before.server ∧ result.2.owners=before.owners := by
  simp only [AdapterServerConstructorStartup.keys,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨seed,seedSupport,supported⟩:=supported
  have seedFrame:=sampled _ before seed seedSupport
  cases chosen:seed.1 with
  | none=>
    rw [chosen] at supported
    simp only [StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact seedFrame
  | some secret=>
    rw [chosen] at supported
    simp only [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨credential,credentialSupport,supported⟩:=supported
    have credentialFrame:=sampled _ seed.2 credential credentialSupport
    simp only [StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨credentialFrame.1.trans seedFrame.1,credentialFrame.2.trans seedFrame.2⟩
end BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame.keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame.keys
