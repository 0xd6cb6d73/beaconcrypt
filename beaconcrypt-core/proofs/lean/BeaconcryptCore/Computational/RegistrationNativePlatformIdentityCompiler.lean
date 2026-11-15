-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityProgram
import BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler

/-! The effectful opaque-Ed language is compiled to the same executable ordinary indexed joint service. Extra allocator/writer coins do not charge native World counters. The source projection removes only the joint service's auxiliary uniform-query transcript entries, exactly as the existing identity compiler; native pools, cache, counters and ordinary private service attempts remain retained. This theorem supplies operational correspondence, not a primitive resource bound or publication-security premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDynamicIdentityPool (DynamicSpec SourceState lazyImpl)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformIdentityProgram (Spec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Spec n KemSK) (StateT (Context n KemSK) (OracleComp DynamicSpec))
  | .inl query => StateT.lift (DynamicSpec.query (.inl query) : OracleComp DynamicSpec _)
  | .inr query => RegistrationNativeIdentityCompiler.implementation (source := source) setup checks representation created query

noncomputable def compiled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Spec n KemSK) (StateT (Context n KemSK × SourceState) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl setup.joint) ((implementation (source := source) setup checks representation created query).run before.1)).run before.2

/-- Both ordinary native operations and separate external coins preserve the exact source state projection, with true native counters unchanged by external draws. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (Spec n KemSK).Domain) (before : Context n KemSK × SourceState) :
    Prod.map id RegistrationNativeIdentityCompiler.project <$>
      (compiled (source := source) setup checks representation created query).run before =
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created query).run
        (RegistrationNativeIdentityCompiler.project before) := by
  cases query with
  | inr query =>
    exact RegistrationNativeIdentityCompiler.query_source setup checks representation created query before
  | inl query =>
    unfold compiled
    have coin := RegistrationNativeIdentityCompiler.coins_source setup.joint (unifSpec.query query : ProbComp _) before.2
    have same := congrArg (fun distribution => (fun result => (result.1, ({ context := before.1, identities := result.2 } : RegistrationNativeIdentityWorld.State n KemSK))) <$> distribution) coin
    simp only [implementation, RegistrationNativeIdentityCompiler.coins, simulateQ_map,
      simulateQ_spec_query, StateT.run_lift, StateT.run_map, bind_pure_comp,
      Functor.map_map, Prod.map, id_eq, RegistrationNativeIdentityCompiler.project,
      RegistrationNativePlatformIdentityProgram.implementation] at same ⊢
    exact same

/-- The complete adaptive effectful opaque program has its exact ordinary joint-source execution, with its full continued state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Spec n KemSK) Value) (before : Context n KemSK × SourceState) :
    Prod.map id RegistrationNativeIdentityCompiler.project <$>
      (simulateQ (compiled (source := source) setup checks representation created) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) work).run
        (RegistrationNativeIdentityCompiler.project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationNativeIdentityCompiler.project
    (query_source setup checks representation created) work before

/-- The interpreted callback compiler is literally the executable indexed service tree, rather than an assumed challenger/program equality. -/
theorem compiled_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Spec n KemSK) Value) (before : Context n KemSK × SourceState) :
    (simulateQ (compiled (source := source) setup checks representation created) work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (lazyImpl setup.joint)
          ((simulateQ (implementation (source := source) setup checks representation created) work).run before.1)).run before.2 := by
  have linked : compiled (n := n) (source := source) setup checks representation created =
      QueryImpl.Stateful.link (implementation (n := n) (source := source) setup checks representation created) (lazyImpl setup.joint) := by
    funext query current
    rfl
  rw [linked, QueryImpl.Stateful.simulateQ_link_run]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.compiled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler.compiled_program
