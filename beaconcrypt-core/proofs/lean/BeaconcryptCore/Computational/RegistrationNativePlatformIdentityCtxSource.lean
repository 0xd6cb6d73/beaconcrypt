-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler

/-! Generated Ed seeds and the physical CTX cache/journal occupy separate private interpreter coordinates. All ordinary joint requests retain the original service semantics; shared hash work changes no generated seed. Removing only auxiliary uniform transcript entries recovers the literal common hash backend. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
open RegistrationNativePlatformIdentityCtxCompiler (Spec protocol backend)
open PqxdhDynamicIdentityPool (SourceState)
variable {Value : Type}

abbrev State := SourceState × RegistrationNativePlatformCtxBackend.State

def normalize (before : State) : State := (RegistrationNativeIdentityCompiler.poolView before.1, before.2)

noncomputable def implementation (primitives : PqxdhJointIdentity.Primitives) : QueryImpl Spec (StateT State ProbComp)
  | .inl query => fun before => (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativeIdentityMainSource.implementation primitives query).run before.1
  | .inr bytes => fun before => (fun result => (result.1, (before.1, result.2))) <$>
      (RegistrationNativePlatformCtxBackend.physical bytes).run before.2

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem pool_coin (query : unifSpec.Domain) (reply : unifSpec.Range query) (before : SourceState) :
    RegistrationNativeIdentityCompiler.poolView (PqxdhDynamicIdentityPool.record (.inl query) reply before) =
      RegistrationNativeIdentityCompiler.poolView before := by
  simp only [RegistrationNativeIdentityCompiler.poolView, PqxdhDynamicIdentityPool.record, List.filter_append,
    List.filter_cons, RegistrationNativeIdentityCompiler.keep, Bool.false_eq_true, ite_false,
    List.filter_nil, List.append_nil]

/-- The complete old indexed protocol interpreter is retained call for call beside the same independent physical hash state. -/
theorem protocol_source (primitives : PqxdhJointIdentity.Primitives)
    (work : OracleComp PqxdhJointPhase1Reports.ProtocolSpec Value) (before : State) :
    (simulateQ (implementation primitives) (simulateQ protocol work)).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativeIdentityMainSource.implementation primitives) work).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, protocol, implementation,
      StateT.run, bind_apply, map_bind, bind_map_left]
    exact bind_congr (fun result => ih result.1 (result.2, before.2))

private noncomputable def backendActual (primitives : PqxdhJointIdentity.Primitives) :
    QueryImpl RegistrationNativePlatformCtxBackend.Spec (StateT State ProbComp) :=
  implementation primitives ∘ₛ backend

private noncomputable def backendLiteral : QueryImpl RegistrationNativePlatformCtxBackend.Spec (StateT State ProbComp) :=
  fun query before => (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativePlatformCtxBackend.implementation query).run before.2

private theorem backend_query (primitives : PqxdhJointIdentity.Primitives)
    (query : RegistrationNativePlatformCtxBackend.Spec.Domain) (before : State) :
    Prod.map id normalize <$> (backendActual primitives query).run before =
      (backendLiteral query).run (normalize before) := by
  cases query with
  | inl bytes =>
    simp only [backendActual, backendLiteral, QueryImpl.apply_compose, backend, simulateQ_spec_query,
      implementation, RegistrationNativePlatformCtxBackend.implementation, StateT.run, Functor.map_map,
      Prod.map, id_eq, normalize]
    rfl
  | inr query =>
    simp only [backendActual, backendLiteral, QueryImpl.apply_compose, backend, simulateQ_spec_query,
      implementation, RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
      RegistrationNativePlatformCtxBackend.implementation, StateT.run, lift_apply, bind_pure_comp, Functor.map_map,
      Prod.map, id_eq, normalize, pool_coin]
    rfl

private theorem literal_program (work : OracleComp RegistrationNativePlatformCtxBackend.Spec Value) (before : State) :
    (simulateQ backendLiteral work).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, backendLiteral,
      map_bind, bind_map_left]
    exact bind_congr (fun result => ih result.1 (before.1, result.2))

/-- Arbitrary shared hash/coin work retains the exact physical cache/journal/P-independent semantics and every generated seed; only the joint game's extra uniform transcript entries are normalized. -/
theorem backend_source (primitives : PqxdhJointIdentity.Primitives)
    (work : OracleComp RegistrationNativePlatformCtxBackend.Spec Value) (before : State) :
    Prod.map id normalize <$> (simulateQ (implementation primitives) (simulateQ backend work)).run before =
      (fun result => (result.1, (RegistrationNativeIdentityCompiler.poolView before.1, result.2))) <$>
        (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before.2 := by
  rw [← QueryImpl.simulateQ_compose]
  change Prod.map id normalize <$> (simulateQ (backendActual primitives) work).run before = _
  rw [OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ normalize (backend_query primitives) work before,
    literal_program]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource.protocol_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource.protocol_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource.backend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource.backend_source
