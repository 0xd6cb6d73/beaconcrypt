-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativeIdentityIndependentSource renaming Spec → IndependentSpec
open PqxdhDynamicIdentityPool (SourceState)
variable {A : Type}

def independent : QueryImpl unifSpec (OracleComp IndependentSpec) := fun coin => IndependentSpec.query (.inr coin)

def protocol : QueryImpl PqxdhJointPhase1Reports.ProtocolSpec
    (StateT RegistrationNativePlatformCtxBackend.State (OracleComp IndependentSpec))
  | .inl query => StateT.lift (IndependentSpec.query (.inl query))
  | .inr _ => pure ()

noncomputable def reify : QueryImpl Spec
    (StateT RegistrationNativePlatformCtxBackend.State (OracleComp IndependentSpec))
  | .inl query => protocol query
  | .inr bytes => fun before => simulateQ independent ((RegistrationNativePlatformCtxBackend.physical bytes).run before)

private noncomputable def localSource (joint : PqxdhJointIdentity.Primitives) :
    QueryImpl unifSpec (StateT SourceState ProbComp) :=
  RegistrationNativeIdentityIndependentSource.lazyImpl joint ∘ₛ independent

private theorem coin_source (joint : PqxdhJointIdentity.Primitives) (coin : unifSpec.Domain) :
    localSource joint coin = (StateT.lift (unifSpec.query coin : ProbComp _) : StateT SourceState ProbComp _) := by
  rw [localSource,QueryImpl.apply_compose,independent,simulateQ_spec_query]
  rfl

/-- Reified ambient randomness runs on the original pool without appending any source observation. -/
theorem uniform_source (joint : PqxdhJointIdentity.Primitives) (work : ProbComp A) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
      (simulateQ independent work)).run before = (fun value => (value,before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have steps : localSource joint = (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT SourceState ProbComp) :=
    funext (coin_source joint)
  change (simulateQ (localSource joint) work).run before = _
  rw [steps,simulateQ_liftTarget,simulateQ_ofLift_eq_self]
  change (do let value ← work; pure (value,before)) = _
  rw [bind_pure_comp]


/-- The physical interpreter reifies over independent coins while protocol calls retain the literal full original source pool. -/
theorem query_source (joint : PqxdhJointIdentity.Primitives) (query : Spec.Domain)
    (physical : RegistrationNativePlatformCtxBackend.State) (pool : SourceState) :
    (fun result => (result.1.1,(result.2,result.1.2))) <$>
      (simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
        ((reify query).run physical)).run pool =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint query).run (pool,physical) := by
  cases query with
  | inl query => cases query with
    | inl query =>
      change (fun result => (result.1.1,(result.2,result.1.2))) <$>
        (simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
          (do let reply ← IndependentSpec.query (.inl query); pure (reply,physical))).run pool =
        (fun result => (result.1,(result.2,physical))) <$> (PqxdhDynamicIdentityPool.lazyImpl joint query).run pool
      rw [bind_pure_comp,simulateQ_map,StateT.run_map,simulateQ_spec_query]
      simp only [RegistrationNativeIdentityIndependentSource.lazyImpl,Functor.map_map]
      rfl
    | inr report => rfl
  | inr bytes =>
    change (fun result => (result.1.1,(result.2,result.1.2))) <$>
      (simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
        (simulateQ independent ((RegistrationNativePlatformCtxBackend.physical bytes).run physical))).run pool =
      (fun result => (result.1,(pool,result.2))) <$> (RegistrationNativePlatformCtxBackend.physical bytes).run physical
    rw [uniform_source,Functor.map_map]


private noncomputable def linked (joint : PqxdhJointIdentity.Primitives) :
    QueryImpl Spec (StateT (RegistrationNativePlatformCtxBackend.State × SourceState) ProbComp) :=
  QueryImpl.Stateful.link reify (RegistrationNativeIdentityIndependentSource.lazyImpl joint)

private theorem query_link (joint : PqxdhJointIdentity.Primitives) (query : Spec.Domain)
    (before : RegistrationNativePlatformCtxBackend.State × SourceState) :
    Prod.map id Prod.swap <$> (linked joint query).run before =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint query).run before.swap := by
  rcases before with ⟨physical,pool⟩
  rw [linked,QueryImpl.Stateful.link_impl_apply_run,Functor.map_map]
  exact query_source joint query physical pool

/-- Independent-coin reification preserves the complete original adaptive source result, full identity pool and physical hash cache/journal. -/
theorem program_source (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A)
    (physical : RegistrationNativePlatformCtxBackend.State) (pool : SourceState) :
    (fun result => (result.1.1,(result.2,result.1.2))) <$>
      (simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
        ((simulateQ reify work).run physical)).run pool =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run (pool,physical) := by
  have complete := OracleComp.map_run_simulateQ_eq_of_query_map_eq (linked joint)
    (RegistrationNativePlatformIdentityCtxSource.implementation joint) Prod.swap (query_link joint) work (physical,pool)
  rw [linked,QueryImpl.Stateful.simulateQ_link_run,Functor.map_map] at complete
  exact complete

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.uniform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent.program_source
