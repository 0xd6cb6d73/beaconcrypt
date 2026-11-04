-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointIdentityFamily (sampleFamily familyPublic)
open PqxdhJointIdentityFreshness (GlobalState initialState sourceImpl)
open PqxdhDynamicIdentityPool (SourceState)
open PqxdhDynamicIdentityRouting (PublicState initialPublicState sourceState projection)
open RegistrationNativeIdentityIndependentRouting (routeImpl)
open RegistrationNativePlatformIdentityCtxIndependent (reify)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {A : Type}
abbrev Physical := RegistrationNativePlatformCtxBackend.State
abbrev Result (count : Nat) (A : Type) := (Fin count → IdentitySeed) × ((A × Physical) × (PublicState × GlobalState count))

noncomputable def run (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp Spec A) (physical : Physical) : ProbComp (Result count A) := do
  let seeds ← sampleFamily count
  let result ← (simulateQ (QueryImpl.Stateful.link (routeImpl (familyPublic joint seeds)) (sourceImpl joint seeds))
    ((simulateQ reify work).run physical)).run (initialPublicState,initialState count)
  pure (seeds,result)

def project {count : Nat} (result : Result count A) : A × RegistrationNativePlatformIdentityCtxSource.State :=
  (result.2.1.1,(sourceState result.1 result.2.2.1,result.2.1.2))

private def sourceProject {count : Nat} (result : (A × Physical) × (GlobalState count × SourceState)) :
    A × RegistrationNativePlatformIdentityCtxSource.State :=
  (result.1.1,(result.2.2,result.1.2))

/-- The complete original shared-CTX source marginal is obtained from one eager finite family execution, retaining all private seeds, router audit and successful signing histories in that execution. -/
theorem source_marginal (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp Spec A) (physical : Physical)
    (bounded : ((simulateQ reify work).run physical).IsQueryBoundP RegistrationNativeIdentityIndependentSource.IsCreate count) :
    EvalDistEq ((simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run
      (PqxdhDynamicIdentityPool.initialState,physical))
      (project <$> run joint count work physical) := by
  have family := (RegistrationNativeIdentityIndependentFamily.dynamic_reserved_complete joint count
    ((simulateQ reify work).run physical) bounded).map (sourceProject (A := A))
  have erased := congrArg (fun result => (fun value => (value.1.1,(value.2,value.1.2))) <$> result)
    (RegistrationNativeIdentityIndependentFamily.history_erasure count (RegistrationNativeIdentityIndependentSource.lazyImpl joint)
      ((simulateQ reify work).run physical) (initialState count,PqxdhDynamicIdentityPool.initialState))
  simp only [Functor.map_map] at erased
  change sourceProject <$> RegistrationNativeIdentityIndependentFamily.dynamicRun joint count
    ((simulateQ reify work).run physical) = _ at erased
  rw [RegistrationNativePlatformIdentityCtxIndependent.program_source] at erased
  rw [erased] at family
  have projected : sourceProject <$> RegistrationNativeIdentityIndependentFamily.reservedRun joint count
      ((simulateQ reify work).run physical) = project <$> run joint count work physical := by
    simp only [RegistrationNativeIdentityIndependentFamily.reservedRun,run,map_bind,map_pure]
    rfl
  rw [projected] at family
  exact family


/-- The same supported family execution derives its final router capacity; no final-pool representation or capacity is a caller premise. -/
theorem capacity (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp Spec A) (physical : Physical) (result : Result count A)
    (reached : result ∈ support (run joint count work physical)) : result.2.2.1.created ≤ count := by
  simp only [run,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨seeds,_sampled,raw,called,rfl⟩ := reached
  exact RegistrationNativeIdentityIndependentRouting.program_count joint seeds _ _ (Nat.zero_le count) raw called

/-- Every reserved index has its exact full source signing/DH history, including aliases and future uncreated entries, in this same supported family execution. -/
theorem history (joint : PqxdhJointIdentity.Primitives) (count : Nat) (work : OracleComp Spec A)
    (physical : Physical) (result : Result count A) (reached : result ∈ support (run joint count work physical))
    (identity : Fin count) :
    result.2.2.2.histories identity = RegistrationNativeIdentityHistory.history identity.val (project result).2.1.transcript := by
  simp only [run,mem_support_bind_iff,mem_support_pure_iff] at reached
  obtain ⟨seeds,_sampled,raw,called,rfl⟩ := reached
  change raw.2.2.histories identity = RegistrationNativeIdentityHistory.history identity.val raw.2.1.transcript
  rw [RegistrationNativeIdentityIndependentReplay.routed_initialized joint seeds _ raw called]
  exact RegistrationNativeIdentityHistory.replay_history identity raw.2.1.transcript

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.source_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.source_marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.capacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily.history
