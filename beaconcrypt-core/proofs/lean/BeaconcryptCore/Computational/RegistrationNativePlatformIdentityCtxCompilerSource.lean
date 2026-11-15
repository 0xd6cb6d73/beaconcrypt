-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient

/-! The source interpretation of the shared-hash indexed compiler retains both private service states independently. Physical cache restoration and uniform-transcript normalization are explicit; all native counters, generated credentials, KEM rows and ordinary failed effects remain source fields. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
variable {I KemSK Value : Type} {base : OracleSpec I} {n : Nat} {source : RegistrationNativeMldsa.Source}

abbrev Full (n : Nat) (KemSK : Type) := Context n KemSK × RegistrationNativePlatformIdentityCtxSource.State

def project (before : Full n KemSK) : RegistrationNativeIdentityWorld.State n KemSK :=
  ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1,
    RegistrationNativeIdentityCompiler.poolView before.2.1⟩

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (RegistrationNativePlatformIdentityProgram.Spec n KemSK) (StateT (Full n KemSK) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) query).run before.1)).run before.2

/-- Every literal actual ambient callback restores the same source Context while retaining its actual private joint seed table. -/
theorem ambient_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeIdentityFrontend.Ambient n KemSK).Domain) (before : Full n KemSK) :
    Prod.map id project <$> (implementation (source := source) setup checks representation created (.inr (.inl query))).run before =
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created (.inr (.inl query))).run (project before) := by
  have combined := congrArg (fun distribution =>
    (fun result => (result.1.1, ({
      context := RegistrationNativePlatformIdentityCtxAmbient.replace result.2.2.1 result.1.2
      identities := result.2.1 } : RegistrationNativeIdentityWorld.State n KemSK))) <$> distribution)
    (RegistrationNativePlatformIdentityCtxSource.backend_source setup.joint
      ((RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created query).run before.1) before.2)
  have ambient := congrArg (fun distribution =>
    (fun result => (result.1, ({context := result.2, identities := RegistrationNativeIdentityCompiler.poolView before.2.1} :
      RegistrationNativeIdentityWorld.State n KemSK))) <$> distribution)
    (RegistrationNativePlatformIdentityCtxAmbient.query_source (source := source) setup checks representation created query (before.1, before.2.2))
  simp only [implementation, RegistrationNativePlatformIdentityCtxCompiler.free,
    RegistrationNativePlatformIdentityCtxCompiler.implementation, StateT.run,
    Functor.map_map, Prod.map_def, id_eq, project, RegistrationNativePlatformIdentityCtxSource.normalize,
    RegistrationNativePlatformIdentityCtxAmbient.implementation, RegistrationNativePlatformIdentityCtxAmbient.realize,
    RegistrationNativePlatformIdentityProgram.implementation, RegistrationNativeIdentityWorld.implementation] at combined ambient ⊢
  exact combined.trans ambient

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

attribute [local irreducible] RegistrationNativeIdentityWorld.implementation PqxdhDynamicIdentityPool.lazyImpl

private theorem joint_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : PqxdhDynamicIdentityPool.PoolSpec.Domain) (before : Full n KemSK) :
    Prod.map id project <$> (implementation (source := source) setup checks representation created (.inr (.inr query))).run before =
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created (.inr (.inr query))).run (project before) := by
  have same := RegistrationNativePlatformIdentityCompiler.query_source (source := source) setup checks representation created
    (.inr (.inr query)) (RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1, before.2.1)
  cases query <;>
    simp only [implementation, RegistrationNativePlatformIdentityCtxCompiler.free,
      RegistrationNativePlatformIdentityCtxCompiler.implementation, RegistrationNativePlatformIdentityCtxCompiler.joint,
      simulateQ_map, simulateQ_spec_query, RegistrationNativePlatformIdentityCtxSource.implementation,
      RegistrationNativeIdentityMainSource.implementation,
      StateT.run, Functor.map_map, Prod.map_def, id_eq, project,
      RegistrationNativePlatformIdentityCompiler.compiled, RegistrationNativePlatformIdentityCompiler.implementation,
      RegistrationNativeIdentityCompiler.implementation, map_apply, lift_apply,
      RegistrationNativeIdentityCompiler.project] at same ⊢
  all_goals try exact same
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, map_apply,
    Functor.map_map, Prod.map_def, id_eq] at same
  exact same

private theorem uniform_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : unifSpec.Domain) (before : Full n KemSK) :
    Prod.map id project <$> (implementation (source := source) setup checks representation created (.inl query)).run before =
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created (.inl query)).run (project before) := by
  simp only [implementation, RegistrationNativePlatformIdentityCtxCompiler.free,
    RegistrationNativePlatformIdentityCtxCompiler.implementation, RegistrationNativePlatformIdentityCtxCompiler.coins,
    simulateQ_map, simulateQ_spec_query, RegistrationNativePlatformIdentityCtxSource.implementation,
    RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, RegistrationNativePlatformIdentityProgram.implementation,
    StateT.run, lift_apply, map_apply, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, project,
    RegistrationNativeIdentityCompiler.poolView, PqxdhDynamicIdentityPool.record,
    List.filter_append, List.filter_cons, RegistrationNativeIdentityCompiler.keep,
    Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil]
  rfl

/-- Each concrete indexed compiler query restores the complete original native source state; the physical CTX cache and generated joint table stay in the private interpreter. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain) (before : Full n KemSK) :
    Prod.map id project <$> (implementation (source := source) setup checks representation created query).run before =
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created query).run (project before) := by
  cases query with
  | inl query => exact uniform_source setup checks representation created query before
  | inr query => cases query with
    | inl query => exact ambient_source setup checks representation created query before
    | inr query => exact joint_source setup checks representation created query before

/-- Arbitrary adaptive owner/Env programs use the same literal native source interpretation without exposing the private physical hash addresses to executable compiler state. -/
theorem complete (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value) (before : Full n KemSK) :
    Prod.map id project <$> (simulateQ (implementation (source := source) setup checks representation created) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source setup checks representation created) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.ambient_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.ambient_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerSource.complete
