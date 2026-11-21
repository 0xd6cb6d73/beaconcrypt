-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedSourceRows
/-! Every nonempty guarded witness names the public key of the same final selected source row. Later creates and key aliases cannot substitute that identity. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey
open PqxdhJointIdentity (Primitives PublicIdentity)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry keys)
open RegistrationNativeIdentityTemplateLateIdentity (Witness raw)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {A : Type}

private theorem raw_key (joint : Primitives) (identity : PublicIdentity)
    (value : RegistrationNativeIdentityAdaptiveHashCapture.Candidate joint identity ⊕ Option Found)
    (witness : Witness) (same : raw joint identity value=some witness) : witness.1=identity := by
  cases value with
  | inl candidate=>exact congrArg Prod.fst (Option.some.inj same).symm
  | inr found=>
      change (RegistrationNativeIdentityCensorPacketClient.candidate joint identity found).map
        (fun candidate=>(identity,⟨candidate.1,candidate.2.val⟩))=some witness at same
      cases formed : RegistrationNativeIdentityCensorPacketClient.candidate joint identity found with
      | none=>simp only [formed,Option.map_none] at same; cases same
      | some candidate=>
          simp only [formed,Option.map_some] at same
          exact congrArg Prod.fst (Option.some.inj same).symm

/-- A successful guarded continuation carries exactly its actual selected public registry identity. -/
theorem resume_key (joint : Primitives) (selected : Nat)
    (cut : RegistrationNativeIdentityTemplateSelectionCut.Cut (Option Found)) (registry : Registry)
    (witness : Witness)
    (supported : some witness∈support (RegistrationNativeIdentityTemplateGuardedLateIdentity.resume joint selected cut registry)) :
    registry selected=some witness.1 := by
  cases cut with
  | returned value=>
      simp only [RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,mem_support_pure_iff] at supported
      cases supported
  | selected message next=>
      cases found : registry selected with
      | none=>
          simp only [RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,found,mem_support_pure_iff] at supported
          cases supported
      | some identity=>
          simp only [RegistrationNativeIdentityTemplateGuardedLateIdentity.resume,found,mem_support_bind_iff] at supported
          obtain ⟨chosen,_queried,continued⟩ := supported
          cases chosen with
          | false=>simp only [Bool.false_eq_true,ite_false,mem_support_pure_iff] at continued; cases continued
          | true=>
              simp only [ite_true,support_map] at continued
              obtain ⟨value,_captured,same⟩ := continued
              rw [raw_key joint identity value witness same]

private theorem value_support (joint : Primitives) (selected : Nat) (work : OracleComp Spec A)
    (publicBefore : Public) (before : SourceState) (result : (A × Public) × SourceState)
    (supported : result∈support ((simulateQ (source joint)
      ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run publicBefore)).run before)) :
    result.1.1∈support work := by
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeIdentityTemplatePolicy.handler selected) work publicBefore
  rw [StateT.run'_eq,support_map]
  refine ⟨result.1,?_,rfl⟩
  apply OracleComp.support_simulateQ_run'_subset (source joint) _ before
  rw [StateT.run'_eq,support_map]
  exact ⟨result,supported,rfl⟩

/-- Every nonempty result of the actual complete guarded program identifies its same final selected source public row, without an identity-equality or key-injectivity premise. -/
theorem supported (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (publicBefore : Public) (before : SourceState) (result : (Option Witness × Public) × SourceState)
    (reached : result∈support ((simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected work (keys joint before) publicBefore)).run before))
    (witness : Witness) (returned : result.1.1=some witness) : keys joint result.2 selected=some witness.1 := by
  rw [RegistrationNativeIdentityTemplateGuardedLateSource.execution,mem_support_bind_iff] at reached
  obtain ⟨cut,_prefix,continued⟩ := reached
  have free := value_support joint selected _ cut.1.2 cut.2 result continued
  rw [returned] at free
  exact RegistrationNativeIdentityTemplateGuardedSourceRows.row_kept joint _ cut.2 result continued selected witness.1
    (resume_key joint selected cut.1.1 (keys joint cut.2) witness free)

/-- The successful complete guarded result has a genuine final selected seed row whose public identity is exactly the witness identity. -/
theorem row (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (publicBefore : Public) (before : SourceState) (result : (Option Witness × Public) × SourceState)
    (reached : result∈support ((simulateQ (source joint)
      (RegistrationNativeIdentityTemplateGuardedLateSource.program joint selected work (keys joint before) publicBefore)).run before))
    (witness : Witness) (returned : result.1.1=some witness) :
    ∃ seed,result.2.seeds[selected]?=some seed ∧ witness.1=joint.publicKeys seed := by
  have same := supported joint selected work publicBefore before result reached witness returned
  simp only [keys] at same
  cases found : result.2.seeds[selected]? with
  | none=>simp only [found,Option.map_none] at same; cases same
  | some seed=>
      simp only [found,Option.map_some] at same
      exact ⟨seed,rfl,(Option.some.inj same).symm⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.resume_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.resume_key

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFinalKey.row
