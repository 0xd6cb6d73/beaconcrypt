-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxNoReveal
/-! The unissued-field client executes the actual full physical hash interpreter using independent public coins, while all genuine identity requests retain their exact source pool or reserved-family histories. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource
open RegistrationNativeIdentityIndependentSource renaming Spec → Independent
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {A : Type}

def embed : QueryImpl Independent (OracleComp PublicSpec)
  | .inl query => PublicSpec.query (.inl (.inl query))
  | .inr coin => PublicSpec.query (.inr coin)

noncomputable def reify : QueryImpl Spec
    (StateT RegistrationNativePlatformCtxBackend.State (OracleComp PublicSpec)) :=
  embed.mapStateTBase RegistrationNativePlatformIdentityCtxIndependent.reify

private theorem source_embed (joint : PqxdhJointIdentity.Primitives) :
    RegistrationNativeIdentityTemplateProtocol.source joint ∘ₛ embed = RegistrationNativeIdentityIndependentSource.lazyImpl joint := by
  funext query before
  cases query <;> simp only [QueryImpl.apply_compose,embed,simulateQ_spec_query]
  all_goals rfl

/-- Reification preserves the entire actual private source pool, physical CTX cache/journal and client return value, without a censor or a hidden-ROM change. -/
theorem program_source (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A)
    (physical : RegistrationNativePlatformCtxBackend.State) (pool : PqxdhDynamicIdentityPool.SourceState) :
    (fun result => (result.1.1,(result.2,result.1.2))) <$>
      (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        ((simulateQ reify work).run physical)).run pool =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run (pool,physical) := by
  rw [reify,←QueryImpl.simulateQ_mapStateTBase_run,←QueryImpl.simulateQ_compose,source_embed]
  exact RegistrationNativePlatformIdentityCtxIndependent.program_source joint work physical pool

private theorem reserved_embed {count : Nat} (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin (count+1) → PqxdhJointIdentity.IdentitySeed) :
    RegistrationNativeIdentityTemplateChosenSource.reserved joint seeds ∘ₛ embed =
      QueryImpl.Stateful.link (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
        (PqxdhJointIdentityFreshness.sourceImpl joint seeds) := by
  funext request before
  cases request with
  | inl request =>
      simp only [QueryImpl.apply_compose,embed,simulateQ_spec_query]
      rfl
  | inr coin =>
      simp only [QueryImpl.apply_compose,embed,simulateQ_spec_query]
      have expanded := QueryImpl.Stateful.link_impl_apply_run
        (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
        (PqxdhJointIdentityFreshness.sourceImpl joint seeds) (.inr coin) before.1 before.2
      simp only [StateT.run] at expanded
      rw [expanded]
      simp only [RegistrationNativeIdentityTemplateChosenSource.reserved,
        RegistrationNativeIdentityIndependentRouting.routeImpl,QueryImpl.Stateful.Frame.prod]
      rfl

/-- Public reification and the actual reserved-family interpreter retain the same physical result, public router and every target/non-target history. -/
theorem family_program {count : Nat} (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin (count+1) → PqxdhJointIdentity.IdentitySeed) (work : OracleComp Spec A)
    (physical : RegistrationNativePlatformCtxBackend.State)
    (before : PqxdhDynamicIdentityRouting.PublicState × PqxdhJointIdentityFreshness.GlobalState (count+1)) :
    (simulateQ (RegistrationNativeIdentityTemplateChosenSource.reserved joint seeds)
      ((simulateQ reify work).run physical)).run before =
      (simulateQ (QueryImpl.Stateful.link
        (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
        (PqxdhJointIdentityFreshness.sourceImpl joint seeds))
        ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify work).run physical)).run before := by
  rw [reify,←QueryImpl.simulateQ_mapStateTBase_run,←QueryImpl.simulateQ_compose,reserved_embed]

private theorem coin_scope (sampler : ProbComp A) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.coins sampler).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.Allowed := by
  induction sampler using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityTemplateProtocol.coins]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,ih⟩

private theorem query_safe (request : Spec.Domain) (physical : RegistrationNativePlatformCtxBackend.State)
    (allowed : RegistrationNativePlatformIdentityCtxNoReveal.Allowed request) :
    ((reify request).run physical).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.Allowed := by
  cases request with
  | inl request => cases request with
    | inr report => exact allQueriesSatisfy_pure _ _
    | inl request =>
      change AllQueriesSatisfy ((fun reply => (reply,physical)) <$> (PublicSpec.query (.inl (.inl request)) : OracleComp PublicSpec _)) _
      apply RegistrationNativeIdentityMainNoRevealCore.mapped
      apply (allQueriesSatisfy_query_iff _ _).mpr
      change RegistrationNativeIdentityMainNoRevealCore.DynamicAllowed request
      cases request with
      | inl coin => trivial
      | inr request => cases request <;> simp_all [RegistrationNativePlatformIdentityCtxNoReveal.Allowed,
          RegistrationNativePlatformIdentityCtxNoReveal.IsReveal,RegistrationNativeIdentityMainNoRevealCore.DynamicAllowed]
  | inr bytes =>
      change (simulateQ embed (simulateQ RegistrationNativePlatformIdentityCtxIndependent.independent
        ((RegistrationNativePlatformCtxBackend.physical bytes).run physical))).AllQueriesSatisfy _
      rw [←QueryImpl.simulateQ_compose]
      have same : embed ∘ₛ RegistrationNativePlatformIdentityCtxIndependent.independent = RegistrationNativeIdentityTemplateProtocol.coins := by
        funext coin
        simp only [QueryImpl.apply_compose,RegistrationNativePlatformIdentityCtxIndependent.independent,simulateQ_spec_query]
        rfl
      rw [same]
      exact coin_scope _

/-- Literal no-reveal source syntax, including all physical hash coins, is sufficient for the public ordinary-challenger program. -/
theorem program_safe (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy RegistrationNativePlatformIdentityCtxNoReveal.Allowed)
    (physical : RegistrationNativePlatformCtxBackend.State) :
    ((simulateQ reify work).run physical).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.Allowed := by
  induction work using OracleComp.inductionOn generalizing physical with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      exact allQueriesSatisfy_bind (query_safe query physical first) (fun reached => ih reached.1 (later reached.1) reached.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.family_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.family_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource.program_safe
