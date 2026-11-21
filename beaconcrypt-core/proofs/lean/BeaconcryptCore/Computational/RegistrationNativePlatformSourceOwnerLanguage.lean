-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
/-! The actual effectful registration writer is reified using only its external uniform queries, while trusted owner requests keep their original interface. Both interpretations retain the same mutable platform state. This is a free-program and state-reassociation construction, not a callback law assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSourceOwnerJoint (Spec nativeHandler)
open RegistrationNativePlatformSourceOwnerEmbedding (embed)
variable {n : Nat} {ι KemSK Platform E Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

abbrev Base (n : Nat) (KemSK Platform : Type) := StateT Platform (OracleComp (Spec n KemSK))

def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (Base n KemSK Platform) :=
  fun query => StateT.lift ((Spec n KemSK).query (.inl query))
def coins : QueryImpl unifSpec (OracleComp (Spec n KemSK)) := fun query => (Spec n KemSK).query (.inr query)
def platform (work : StateT Platform ProbComp Value) : Base n KemSK Platform Value :=
  fun previous => simulateQ coins (work.run previous)
def handler (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (Base n KemSK Platform)
  | .inl query => trusted query
  | .inr query => platform (writer query)

def embedding (work : Base n KemSK Platform Value) : RegistrationNativePlatformPublicFrontend.Base n KemSK Platform Value :=
  fun previous => simulateQ embed (work.run previous)

theorem embedding_pure (value : Value) : embedding (n := n) (KemSK := KemSK) (Platform := Platform) (pure value) = pure value := by
  funext previous
  rfl

theorem embedding_bind (work : Base n KemSK Platform Value) (next : Value → Base n KemSK Platform Next) :
    embedding (work >>= next) = (embedding work >>= fun value => embedding (next value)) := by
  funext previous
  simp only [embedding, StateT.run_bind, simulateQ_bind]
  rfl

theorem embedding_trusted (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    embedding (trusted (Platform := Platform) query) = RegistrationNativePlatformPublicFrontend.trusted query := by
  funext previous
  simp only [embedding, trusted, simulateQ_map, simulateQ_spec_query,
    RegistrationNativePlatformPublicFrontend.trusted, embed, StateT.run, lift_apply]

theorem embedding_platform (work : StateT Platform ProbComp Value) :
    embedding (n := n) (KemSK := KemSK) (platform work) = RegistrationNativePlatformPublicFrontend.platform work := by
  funext previous
  simp only [embedding, StateT.run, platform, RegistrationNativePlatformPublicFrontend.platform]
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- Every literal generic owner/writer request compiles to the corrected public dictionary on the same P. -/
theorem embedding_program
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) Value) :
    embedding (simulateQ (handler writer) work) =
      simulateQ (fun query => match query with
        | .inl query => RegistrationNativePlatformPublicFrontend.trusted query
        | .inr query => RegistrationNativePlatformPublicFrontend.writer writer query) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact embedding_pure value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embedding_bind, ih]
    cases query with
    | inl query => rw [handler, embedding_trusted]
    | inr query => rw [handler, embedding_platform]; rfl

noncomputable def native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (work : Base n KemSK Platform Value) : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform Value :=
  fun before previous => (fun result => ((result.1.1, result.2), result.1.2)) <$>
    (simulateQ (nativeHandler setup checks representation created source) (work.run previous)).run before

theorem native_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    native (n := n) (Platform := Platform) setup checks representation created source (pure value) = pure value := by
  funext before previous
  simp only [native, StateT.run, pure_apply, simulateQ_pure, map_pure]

theorem native_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : Base n KemSK Platform Value) (next : Value → Base n KemSK Platform Next) :
    native setup checks representation created source (work >>= next) =
      (native setup checks representation created source work >>= fun value => native setup checks representation created source (next value)) := by
  funext before previous
  simp only [StateT.run, bind_apply, native, simulateQ_bind, map_bind, bind_map_left]

private theorem native_coins (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : ProbComp Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (simulateQ (nativeHandler setup checks representation created source) (simulateQ coins work)) before =
      (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_apply, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, coins, nativeHandler, bind_apply,
      lift_apply, bind_map_left, ih, map_bind]
    rfl

/-- External writer work retains its exact returned P and leaves the full native state untouched. -/
theorem native_platform (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : StateT Platform ProbComp Value) :
    native (n := n) setup checks representation created source (platform work) = StateT.lift work := by
  funext before previous
  simp only [native, StateT.run, platform, native_coins, Functor.map_map, lift_apply, map_apply]
  rfl

private theorem counted_coins (work : ProbComp Value) (previous : Platform) :
    (simulateQ RegistrationNativePlatformMldsaProgram.coins work) previous = (fun value => (value, previous)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_apply, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformMldsaProgram.coins,
      bind_apply, lift_apply, bind_map_left, ih, map_bind]

/-- The trusted branch retains the exact native sampler and its measured counter updates; only external coins are uncounted. -/
theorem native_trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    native (Platform := Platform) setup checks representation created source (trusted query) =
      RegistrationNativePlatformExperiment.trusted RegistrationNativePlatformMldsaProgram.coins setup checks representation created source query := by
  funext before previous
  simp only [native, trusted, lift_apply, simulateQ_map, simulateQ_spec_query,
    nativeHandler, map_apply, Functor.map_map, StateT.run,
    RegistrationNativePlatformExperiment.trusted, RegistrationNativePlatformExperiment.liftNative, counted_coins]
  rfl

/-- The entire free stateful owner/writer program has the literal native platform dictionary. -/
theorem native_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) Value) :
    native setup checks representation created source (simulateQ (handler writer) work) =
      simulateQ (RegistrationNativePlatformExperiment.bundleHandler RegistrationNativePlatformMldsaProgram.coins
        setup checks representation created source writer) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact native_pure setup checks representation created value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, native_bind, ih]
    cases query with
    | inl query => rw [handler, native_trusted]; rfl
    | inr query => rw [handler, native_platform]; rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.embedding_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerLanguage.native_program
