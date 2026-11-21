-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource
open PqxdhDynamicIdentityPool (DynamicSpec SourceState)
abbrev Spec := DynamicSpec + unifSpec

def IsCreate : Spec.Domain → Prop
  | .inl (.inr .create) => True
  | _ => False
instance : DecidablePred IsCreate := fun query => by
  unfold IsCreate
  split <;> infer_instance

noncomputable def lazyImpl (joint : PqxdhJointIdentity.Primitives) : QueryImpl Spec (StateT SourceState ProbComp)
  | .inl query => PqxdhDynamicIdentityPool.lazyImpl joint query
  | .inr coin => StateT.lift (unifSpec.query coin : ProbComp _)

noncomputable def eagerImpl (joint : PqxdhJointIdentity.Primitives) (seeds : List PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT SourceState ProbComp)
  | .inl query => PqxdhDynamicIdentityPool.eagerImpl joint seeds query
  | .inr coin => StateT.lift (unifSpec.query coin : ProbComp _)

/-- Independent ambient coins execute their literal sampler without adding a pool observation or changing any private source field. -/
theorem independent (joint : PqxdhJointIdentity.Primitives) (coin : unifSpec.Domain) (before : SourceState) :
    (lazyImpl joint (.inr coin)).run before =
      (fun reply => (reply, before)) <$> (unifSpec.query coin : ProbComp _) := by
  change (do let reply ← (unifSpec.query coin : ProbComp _); pure (reply, before)) = _
  exact bind_pure_comp _ _

/-- Reserving private future identity seeds leaves that independent ambient coin branch literally unchanged. -/
theorem eager_independent (joint : PqxdhJointIdentity.Primitives) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (coin : unifSpec.Domain) (before : SourceState) :
    (eagerImpl joint seeds (.inr coin)).run before = (lazyImpl joint (.inr coin)).run before := rfl
end BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource.independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource.independent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource.eager_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource.eager_independent
