-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle

/-! The executable ordinary indexed identity client recovers the literal chosen native stateful bundle, retaining complete private source/P state on every successful or failed publication. Source rows are used only in the private interpretation; the client itself holds the generated Ed handle and public identity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project)
open RegistrationNativeIdentityMainOrdinary (attach)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def bundle (index : Nat) : M n KemSK Platform source (RustM (Option Pqxdh.Bytes)) :=
  RegistrationNativePlatformIdentityNativeBundle.reply <$>
    RegistrationNativePlatformIdentityMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)

private def closeRaw (result : (((RegistrationNativePlatformIdentityNativeBundle.Reply × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform) × RegistrationNativeIdentityWorld.Context n KemSK) :=
  let closed := RegistrationNativePlatformIdentityNativeBundle.closeOld
    (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.2), result.1.2))
  (closed.1.1, (closed.1.2, closed.2))

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- Full native source bundle restoration includes the actual six-field source writer, the original mutable P and every failed signing/writing prefix. -/
theorem bundle_source (index : Nat) (before : (State n KemSK source × Platform) × SourceState)
    (owned : RegistrationNativeIdentityMainSource.Owned setup.joint (before.1.1, before.2)) :
    Prod.map id project <$>
      (interpret setup.joint (bundle setup checks representation created writer index)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
          (project before).1).run (project before).2 := by
  have execution := RegistrationNativePlatformIdentityMain.beacon_execution setup checks representation created
    (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) before
  have moved := congrArg (fun distribution =>
    (fun result => (RegistrationNativePlatformIdentityNativeBundle.reply result.1, project result.2)) <$> distribution) execution
  have finite := RegistrationNativePlatformIdentityBundleObservation.bundle_source setup checks representation created writer index
    before.1.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world) before.1.2
    ⟨before.1.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ owned
  have closed := congrArg (fun distribution => closeRaw <$> distribution) finite
  have native := RegistrationNativePlatformIdentityNativeBundle.original_source setup checks representation created writer
    (RegistrationNativeIdentityRealization.owners before.2 before.1.1.beacons) before.1.1.context before.1.2 index
  have final := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) native
  simp only [RegistrationNativePlatformIdentityProgram.runOld, Functor.map_map,
    RegistrationNativePlatformIdentityNativeBundle.closeOld] at final
  simp only [interpret, bundle, StateT.run, map_apply, simulateQ_map, Functor.map_map, Prod.map, id_eq,
    RegistrationNativePlatformIdentityMain.poolProjection, project, RegistrationNativeIdentityMainSource.project,
    RegistrationNativePlatformIdentityMain.assemble, RegistrationNativePlatformIdentityBundleObservation.observe,
    RegistrationNativePlatformIdentityNativeBundle.closeOld, closeRaw] at moved closed ⊢
  exact moved.trans (closed.trans final)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBundle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBundle.bundle_source
