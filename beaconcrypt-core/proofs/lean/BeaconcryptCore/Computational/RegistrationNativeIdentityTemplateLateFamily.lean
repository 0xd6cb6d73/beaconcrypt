-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily
/-! The late-key client is an identity-free public program, so the actual on-demand source may reserve its future family before execution. All public local state, optional output and genuine source audit remain joint. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily
open PqxdhJointIdentity (Primitives IdentitySeed)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
open RegistrationNativeIdentityTemplateLateIdentity (Witness)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityIndependentSource (IsCreate)
abbrev Spec := RegistrationNativeIdentityTemplateCensorRecognition.Spec
abbrev Found := RegistrationNativeIdentityCensorPacketClient.Found
abbrev SourceState := PqxdhDynamicIdentityPool.SourceState

noncomputable def program (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public) :=
  (simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
    (RegistrationNativeIdentityTemplateLateIdentity.visit joint selected work registry)).run before

noncomputable def independent (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public) :=
  simulateQ RegistrationNativeIdentityTemplateProtocol.independent (program joint selected work registry before)

/-- The newly public key discovery preserves the exact original creation bill, including rows generated before later failures. -/
theorem query_bound (joint : Primitives) (selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativeIdentityTemplateCreateCounts.TargetCreate cap) :
    (independent joint selected work registry before).IsQueryBoundP IsCreate cap := by
  apply RegistrationNativeIdentityTemplateCreateCounts.policy
  exact RegistrationNativeIdentityTemplateLateIdentity.query_bound joint selected work _ cap bounded registry

noncomputable def run (joint : Primitives) (count selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public) : ProbComp ((Fin count → IdentitySeed) ×
      ((Option Witness × Public) × (PqxdhDynamicIdentityRouting.PublicState × PqxdhJointIdentityFreshness.GlobalState count))) := do
  let seeds ← PqxdhJointIdentityFamily.sampleFamily count
  let result ← (simulateQ (QueryImpl.Stateful.link
      (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
      (PqxdhJointIdentityFreshness.sourceImpl joint seeds))
    (independent joint selected work registry before)).run
      (PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFreshness.initialState count)
  pure (seeds,result)

def project {count : Nat} (result : (Fin count → IdentitySeed) ×
    ((Option Witness × Public) × (PqxdhDynamicIdentityRouting.PublicState × PqxdhJointIdentityFreshness.GlobalState count))) :
    (Option Witness × Public) × SourceState :=
  (result.2.1,(PqxdhDynamicIdentityRouting.projection result.1 result.2.2).2)

/-- Literal on-demand execution and the explicitly sampled reserved family have the same full result and source pool marginal. No future identity is a parameter of the client. -/
theorem source_marginal (joint : Primitives) (count selected : Nat) (work : OracleComp Spec (Option Found))
    (registry : Registry) (before : Public)
    (bounded : work.IsQueryBoundP RegistrationNativeIdentityTemplateCreateCounts.TargetCreate count) :
    EvalDistEq ((simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        (program joint selected work registry before)).run PqxdhDynamicIdentityPool.initialState)
      (project <$> run joint count selected work registry before) := by
  have coupled := (RegistrationNativeIdentityIndependentFamily.dynamic_reserved_complete joint count
    (independent joint selected work registry before) (query_bound joint selected work registry before count bounded)).map (Prod.map id Prod.snd)
  have erased := RegistrationNativeIdentityIndependentFamily.history_erasure count
    (RegistrationNativeIdentityIndependentSource.lazyImpl joint) (independent joint selected work registry before)
    (PqxdhJointIdentityFreshness.initialState count,PqxdhDynamicIdentityPool.initialState)
  rw [RegistrationNativeIdentityIndependentFamily.dynamicRun,erased] at coupled
  rw [independent,RegistrationNativeIdentityTemplateProtocol.independent_source] at coupled
  simpa only [RegistrationNativeIdentityIndependentFamily.reservedRun,run,project,independent,map_bind,map_pure,
    Functor.map_map,Prod.map_def,id_eq] using coupled

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily.query_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateFamily.source_marginal
