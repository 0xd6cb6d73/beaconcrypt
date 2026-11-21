-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState

/-! The original side of the effectful Ed bundle executes the literal generic source program under the same native context and platform interpreter. Stateful serializer calls and already-counted native requests are interleaved at their actual positions. No full-controller correspondence premise or private counter projection is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformIdentityProgram (OriginalSpec)
variable {n : Nat} {ι KemSK Platform E Value Next Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def runBase (work : StateT Platform (OracleComp (OriginalSpec n KemSK)) Value) :
    StateT (Context n KemSK × Platform) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (RegistrationNativePlatformIdentityProgram.originalImplementation (source := source) setup checks representation created)
      (work.run before.2)).run before.1

noncomputable def implementation
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT (Context n KemSK × Platform) ProbComp)
  | .inl query => fun before => (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created query).run before.1
  | .inr query => fun before => (fun result => (result.1, (before.1, result.2))) <$> (writer query).run before.2

def free (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Platform (OracleComp (OriginalSpec n KemSK)))
  | .inl query => RegistrationNativePlatformIdentityOriginalBundle.trusted query
  | .inr query => RegistrationNativePlatformIdentityOriginalBundle.writerProgram (writer query)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem runBase_pure (value : Value) :
    runBase (n := n) (source := source) (Platform := Platform) setup checks representation created (pure value) = pure value := by
  funext before
  simp only [runBase, StateT.run_pure, pure_apply, simulateQ_pure, map_pure]

private theorem runBase_bind (work : StateT Platform (OracleComp (OriginalSpec n KemSK)) Value)
    (next : Value → StateT Platform (OracleComp (OriginalSpec n KemSK)) Next) :
    runBase (source := source) setup checks representation created (work >>= next) =
      (runBase (source := source) setup checks representation created work >>= fun value => runBase (source := source) setup checks representation created (next value)) := by
  funext before
  simp only [runBase, StateT.run_bind, bind_apply, simulateQ_bind, map_bind, bind_map_left]

private theorem runBase_simulate {κ : Type} {spec : OracleSpec κ}
    (handler : QueryImpl spec (StateT Platform (OracleComp (OriginalSpec n KemSK)))) (work : OracleComp spec Value) :
    runBase (source := source) setup checks representation created (simulateQ handler work) =
      simulateQ (fun query => runBase (source := source) setup checks representation created (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, runBase_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, runBase_bind, ih]

private theorem external_probability (work : ProbComp Value) (before : Context n KemSK) :
    (simulateQ (RegistrationNativePlatformIdentityProgram.originalImplementation (source := source) setup checks representation created)
      (simulateQ (RegistrationNativePlatformIdentityProgram.externalOriginalLift (n := n) (KemSK := KemSK)) work)).run before =
      (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityProgram.externalOriginalLift,
      RegistrationNativePlatformIdentityProgram.originalImplementation, StateT.run_bind, StateT.run_lift,
      bind_pure_comp, bind_map_left, ih, map_bind]

private theorem external_apply (work : ProbComp Value) (before : Context n KemSK) :
    simulateQ (RegistrationNativePlatformIdentityProgram.originalImplementation (source := source) setup checks representation created)
      (simulateQ (RegistrationNativePlatformIdentityProgram.externalOriginalLift (n := n) (KemSK := KemSK)) work) before =
      (fun value => (value, before)) <$> work :=
  external_probability (source := source) setup checks representation created work before

/-- Each concrete native or source writer callback recovers its exact context/P execution. -/
theorem query (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) :
    runBase (source := source) setup checks representation created (free writer request) =
      implementation (source := source) setup checks representation created writer request := by
  cases request with
  | inl request =>
    funext before
    simp only [runBase, free, RegistrationNativePlatformIdentityOriginalBundle.trusted,
      lift_apply, simulateQ_map, simulateQ_spec_query,
      RegistrationNativePlatformIdentityProgram.originalLift,
      RegistrationNativePlatformIdentityProgram.originalImplementation,
      StateT.run, map_apply, Functor.map_map, implementation, Prod.map, id_eq]
  | inr request =>
    funext before
    simp only [runBase, free, RegistrationNativePlatformIdentityOriginalBundle.writerProgram, StateT.run,
      external_apply, Functor.map_map, implementation]
    rfl

private theorem original_program (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    RegistrationNativePlatformIdentityBundleRun.originalBundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer =
      RegistrationNativePlatformGenericBundle.evaluate (free writer)
        (RegistrationNativePlatformGenericBundle.program E setup source index) := by
  rw [RegistrationNativePlatformGenericBundle.program_evaluate]
  exact RegistrationNativePlatformIdentityOriginalBundle.bundle_source setup index writer

/-- The complete original-side bundle has the same literal actual source tree, interpreted at its real context/P call positions and retaining every failed return. -/
theorem bundle (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeIdentitySourceSimulation.OldState n KemSK Auxiliary source × Platform) :
    RegistrationNativePlatformIdentityProgram.runOld setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.originalBundle setup index writer) before =
      (fun result => (result.1.1.1, (((result.1.1.2, result.1.2), result.2.1), result.2.2))) <$>
        (simulateQ (implementation (source := source) setup checks representation created writer)
          (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.1.1.1).run before.1.1.2)).run
            (before.1.2, before.2) := by
  rw [original_program]
  have native := congrFun (runBase_simulate (source := source) setup checks representation created (free writer)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.1.1.1).run before.1.1.2)) (before.1.2, before.2)
  simp_rw [query setup checks representation created writer] at native
  have law := congrArg (fun distribution =>
    (fun result => (result.1.1.1, (((result.1.1.2, result.1.2), result.2.1), result.2.2))) <$> distribution) native
  simp only [runBase, RegistrationNativePlatformIdentityProgram.runOld,
    RegistrationNativePlatformGenericBundle.evaluate, StateT.run, Functor.map_map] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext.bundle
