-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram
import BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram

/-! The actual source Init writer and native trusted leaves share one indexed KEM interpreter and one persistent external platform state. The private pool is separate from the executable client; all actual source draw counts and failed writer poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativePlatformKemCountedProgram (M execute runState inject lift)
open RegistrationNativePlatformMldsaProgram (coins)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

noncomputable def trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Client (M KemSK Platform)) :=
  fun query => inject (RegistrationNativeKemCountedTrusted.implementation setup checks representation created query)

def writer (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Client (M KemSK Platform)) :=
  fun query => lift (StateT.lift (implementation query))

noncomputable def handler (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Client (M KemSK Platform))
  | .inl query => trusted setup checks representation created query
  | .inr query => writer implementation query

noncomputable def program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    StateT Client (M KemSK Platform) (RustM (Option Pqxdh.Bytes)) := fun before => do
  let result ← (simulateQ (handler setup checks representation created implementation)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))).run before
  pure ((do let optional ← result.1.1.1
            .ok (optional.map TranscriptAuthParts.absSlice)),
    { result.2 with beacons := result.1.1.2, server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

def project (before : Native × Platform) : (Client × Platform) × Pool KemSK := ((ofNative before.1, before.2), before.1.pool)
def restore (before : (Client × Platform) × Pool KemSK) : Native × Platform := (toNative before.1.1 before.2, before.1.2)

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- Every actual source trusted/writer request retains the complete native, external and private-pool state in the counted interpretation. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) (before : Native) (previous : Platform) :
    (execute setup (handler setup checks representation created implementation query)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source implementation query)).run (before, previous) := by
  cases query with
  | inl query =>
      have law := congrArg (fun distribution => (fun result => (result.1, ((result.2.1, previous), result.2.2))) <$> distribution)
        (RegistrationNativeKemCountedTrusted.query_source setup checks representation created query before)
      simp only [handler, trusted, execute, RegistrationNativePlatformKemCountedProgram.run_inject,
        RegistrationNativePlatformKemCountedProgram.arrange, RegistrationNativePlatformPackedState.pack,
        RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.trusted,
        RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformMldsaProgram.lift_coins,
        StateT.run, lift_apply, Functor.map_map, project, RegistrationNativeKemCountedTrusted.arrange,
        RegistrationNativeKemCountedTrusted.project, Prod.map, id_eq] at law ⊢
      exact law
  | inr query =>
      rw [handler, writer, RegistrationNativePlatformKemCountedProgram.execute_lift]
      simp only [RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.bundleHandler,
        RegistrationNativePlatformExperiment.writer, StateT.run, lift_apply, Functor.map_map, project, Prod.map, id_eq]
      simp only [map_apply, Functor.map_map]
      rfl

/-- Arbitrary adaptive source writer/trusted continuations retain that same joint state and full actual costs. -/
theorem tree_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) Value) (before : Native) (previous : Platform) :
    (execute setup (simulateQ (handler setup checks representation created implementation) work)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source implementation) work)).run (before, previous) := by
  have step (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) (first : Native × Platform) :
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source implementation query)).run first =
        (execute setup (handler setup checks representation created implementation query)).run (project first) :=
    (query_source setup checks representation created implementation query first.1 first.2).symm
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project step work (before, previous)
  rw [RegistrationNativePlatformKemCountedProgram.execute_simulate, RegistrationNativePlatformPackedState.simulate_pack]
  exact law.symm

/-- The complete actual Init publication, source encoder, phase update and lifecycle suffix keep their literal three-coordinate poststate. -/
theorem source_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : Native) (previous : Platform) :
    (execute setup (program setup checks representation created implementation index)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.bundle coins setup checks representation created source implementation index)).run (before, previous) := by
  have law := congrArg (fun distribution => (fun result =>
      ((do let optional ← result.1.1.1
           .ok (optional.map TranscriptAuthParts.absSlice)),
        (({ result.2.1.1 with beacons := result.1.1.2, server := { result.2.1.1.server with
            world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.1.1.server.world.world.1 } }, result.2.1.2), result.2.2))) <$> distribution)
    (tree_source setup checks representation created implementation
      (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) before previous)
  simp only [execute, runState, program, StateT.run, bind_pure_comp,
    RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, map_apply, Functor.map_map,
    RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.bundle, project, ofNative,
    RegistrationNativePlatformKemCountedProgram.arrange, Prod.map, id_eq] at law ⊢
  exact law

/-- Lossless client/pool reassembly recovers the literal source bundle execution, including failed writers and exact native counters. -/
theorem native_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : Native) (previous : Platform) :
    Prod.map id restore <$> (execute setup (program setup checks representation created implementation index)).run (project (before, previous)) =
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.bundle coins setup checks representation created source implementation index)).run (before, previous) := by
  rw [source_program, Functor.map_map]
  change id <$> _ = _
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.tree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.tree_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle.native_source
