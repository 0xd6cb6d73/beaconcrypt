-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingScope
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain

/-! The literal actual CTX compiler distributes over the real publication dictionary. Its separately threaded owner/Env/P state is reopened exactly between callbacks. The syntactic NoKem scope derives the needed full environment patch frame; no generic ambient monad hom or whole controller law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformIdentityCtxEnvPatch (Env patch)
open RegistrationNativePlatformIdentityCtxOutgoingScope (Work)
variable {n : Nat} {I KemSK Platform Value Next : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Frontend (Value : Type) := RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value
abbrev MainState := RegistrationNativeIdentityMain.State n KemSK source × Platform
abbrev Intermediate (Value : Type) := (((Value × RegistrationNativeIdentityFrontend.State source) × Env) × Platform) × Context n KemSK

def close (result : Intermediate (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) Value) :
    Value × MainState (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) :=
  (result.1.1.1.1, ({ context := patch result.1.1.2 result.2, beacons := result.1.1.1.2 }, result.1.2))

theorem run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : Frontend (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) Value)
    (before : MainState (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)) :
    (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work).run before =
      close <$> (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created))
          (((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)).run before.2)).run before.1.context := rfl

/-- The actual compiler's pure closing operation rejoins exactly the initial environment and full World. -/
theorem pure_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := source)
      setup checks representation created (pure value) = pure value := by
  funext before
  change (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created (pure value)).run before =
    (pure value : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source Value).run before
  rw [run]
  simp only [StateT.run_pure, simulateQ_pure, map_pure, close, patch, RegistrationWorldAgreementCompiler.join_erase]

private theorem close_patch (environment : Env)
    (result : Intermediate (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) Value) :
    close (Prod.map id (patch environment) result) = close result := rfl

/-- Sequential source publication actions close and reopen the same exact state; only the later tree requires the derived syntactic publication scope. -/
theorem bind_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : Frontend (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) Value)
    (next : Value → Frontend (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) Next)
    (allowed : ∀ value, Work (next value)) :
    RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created (work >>= next) =
      (do let value ← RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work
          RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created (next value)) := by
  funext before
  change (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created (work >>= next)).run before =
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work >>= fun value =>
      RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created (next value)) :
        RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source Next).run before
  rw [run]
  simp only [StateT.run_bind, run, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr
  intro middle
  change close <$> (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created))
      ((((next middle.1.1.1.1).run middle.1.1.1.2).run middle.1.1.2).run middle.1.2)).run middle.2 =
    close <$> (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created))
      ((((next middle.1.1.1.1).run middle.1.1.1.2).run middle.1.1.2).run middle.1.2)).run (patch middle.1.1.2 middle.2)
  rw [← RegistrationNativePlatformIdentityCtxEnvPatch.program setup checks representation created _
    (allowed middle.1.1.1.1 middle.1.1.1.2 middle.1.1.2 middle.1.2) middle.1.1.2 middle.2]
  simp only [Functor.map_map, close_patch]

/-- The actual outgoing hash/ML/Ed and mutable writer dictionary folds query by query through Main, with every source assumption discharged from literal syntax. -/
theorem publication {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner writer) work) =
      simulateQ (fun query => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup index owner writer query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure_source setup checks representation created value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, bind_source setup checks representation created _ _
      (fun reply => RegistrationNativePlatformIdentityCtxOutgoingScope.publication setup index owner writer (next reply))]
    exact congrArg (fun continued => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityPublication.callback setup index owner writer query) >>= continued) (funext ih)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold.publication
