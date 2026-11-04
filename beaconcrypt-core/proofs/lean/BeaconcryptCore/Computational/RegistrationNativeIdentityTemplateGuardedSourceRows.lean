-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry
/-! The actual public source only appends generated identity rows. Every existing indexed public identity is retained through arbitrary service, reveal, report and independent-coin replies; no distinctness of seeds or public keys is required. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedSourceRows
open PqxdhJointIdentity (Primitives PublicIdentity)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source)
open RegistrationNativeIdentityTemplatePublicRegistry (keys)
variable {A : Type}

private theorem query_kept (joint : Primitives) (query : PublicSpec.Domain)
    (before : SourceState) (result : PublicSpec.Range query × SourceState)
    (supported : result∈support ((source joint query).run before))
    (selected : Nat) (identity : PublicIdentity) (prior : keys joint before selected=some identity) :
    keys joint result.2 selected=some identity := by
  rcases query with (dynamic|report)|coin
  · obtain ⟨appended,extension,_count⟩ := PqxdhDynamicIdentityPool.lazyImpl_seed_extension joint dynamic before result supported
    have found := prior
    change before.seeds[selected]?.map joint.publicKeys=some identity at found
    obtain ⟨seed,seedAt,_public⟩ := Option.map_eq_some_iff.mp found
    have below := (List.getElem?_eq_some_iff.mp seedAt).1
    simpa only [keys,extension,List.getElem?_append_left below] using prior
  · simp only [source,RegistrationNativeIdentityMainSource.implementation,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact prior
  · change result∈support ((fun answer=>(answer,before)) <$> (unifSpec.query coin : ProbComp _)) at supported
    rw [support_map] at supported
    obtain ⟨answer,_called,rfl⟩ := supported
    exact prior

/-- Every actual adaptive public source continuation keeps its already existing indexed identity row. -/
theorem row_kept (joint : Primitives) (work : OracleComp PublicSpec A) (before : SourceState)
    (result : A × SourceState) (supported : result∈support ((simulateQ (source joint) work).run before))
    (selected : Nat) (identity : PublicIdentity) (prior : keys joint before selected=some identity) :
    keys joint result.2 selected=some identity :=
  OracleComp.simulateQ_run_preserves_inv_of_query (source joint)
    (fun current=>keys joint current selected=some identity)
    (fun query current held next reached=>query_kept joint query current next reached selected identity held)
    work before prior result supported
end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedSourceRows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedSourceRows.row_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedSourceRows.row_kept
