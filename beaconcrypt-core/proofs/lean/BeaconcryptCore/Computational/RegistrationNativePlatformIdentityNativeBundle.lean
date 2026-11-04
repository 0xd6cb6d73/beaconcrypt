-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleContext
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment

/-! The original side of the effectful opaque-Ed bundle recovers the literal current native bundle, including the complete private World/KEM/context and actual shared platform state. The source/native equation is derived from individual trusted and serializer requests and the actual generic source tree; no whole-bundle equality premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityMainOrdinary (attach)
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Owners" => RegistrationNativeBeaconFrontend.State source
local notation "Env" => RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State
abbrev Reply := RustM (Option (alloc.vec.Vec U8))

def attachP (owners : Owners) (before : Context n KemSK × Platform) : Native × Platform :=
  (attach owners before.1, before.2)

def reply (result : Reply) : RustM (Option Pqxdh.Bytes) := do
  let optional ← result
  .ok (optional.map TranscriptAuthParts.absSlice)

def closeSource (result : ((Reply × Owners) × Env) × (Context n KemSK × Platform)) :
    (RustM (Option Pqxdh.Bytes) × Native) × Platform :=
  ((reply result.1.1.1,
    ⟨{result.2.1.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.1.server.world.world.1},
      result.1.1.2, result.2.1.kem, result.2.1.parsedAccepts⟩), result.2.2)

def closeNative (result : ((Reply × Owners) × Env) × (Native × Platform)) :
    (RustM (Option Pqxdh.Bytes) × Native) × Platform :=
  ((reply result.1.1.1, { result.2.1 with
      beacons := result.1.1.2
      server := { result.2.1.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.1.server.world.world.1 } }), result.2.2)

def closeOld (result : Reply × (RegistrationNativeIdentitySourceSimulation.OldState n KemSK RegistrationServerRoleBackend.State source × Platform)) :
    (RustM (Option Pqxdh.Bytes) × Native) × Platform :=
  ((reply result.1,
    ⟨{result.2.1.2.server with world := RegistrationWorldAgreementCompiler.join result.2.1.1.2 result.2.1.2.server.world.world.1},
      result.2.1.1.1, result.2.1.2.kem, result.2.1.2.parsedAccepts⟩), result.2.2)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def target : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK)
    (StateT (Native × Platform) ProbComp) := fun request => RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.bundleHandler RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer request)

/-- Each actual native trusted/source serializer request retains its complete source/native context and P poststate, with the fixed ambient roster restored. -/
theorem query (owners : Owners) (request : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain)
    (before : Context n KemSK × Platform) :
    Prod.map id (attachP owners) <$>
      (RegistrationNativePlatformIdentityBundleContext.implementation (source := source) setup checks representation created writer request).run before =
      (target setup checks representation created writer request).run (attachP owners before) := by
  cases request with
  | inl request =>
    have native := RegistrationNativeIdentityMainOld.trusted_source setup checks representation created owners request before.1
    have law := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) native
    simp only [RegistrationNativePlatformIdentityBundleContext.implementation, target,
      RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.trusted,
      RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformMldsaProgram.lift_coins,
      RegistrationNativePlatformPackedState.pack, StateT.run, lift_apply,
      Functor.map_map, Prod.map, id_eq, attachP] at law ⊢
    exact law
  | inr request =>
    simp only [RegistrationNativePlatformIdentityBundleContext.implementation, target,
      RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
      RegistrationNativePlatformPackedState.pack, StateT.run, lift_apply, map_apply,
      Functor.map_map, Prod.map, id_eq, attachP]

private theorem native_bundle (owners : Owners) (before : Context n KemSK) (previous : Platform) (index : Nat) :
    closeSource <$>
      (simulateQ (RegistrationNativePlatformIdentityBundleContext.implementation (source := source) setup checks representation created writer)
        (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run
          (RegistrationWorldAgreementCompiler.erase before.server.world))).run (before, previous) =
      ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
        (attach owners before)).run previous := by
  let script := ((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run
    (RegistrationWorldAgreementCompiler.erase before.server.world)
  have coupled := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativePlatformIdentityBundleContext.implementation (source := source) setup checks representation created writer)
    (target setup checks representation created writer) (attachP owners)
    (query setup checks representation created writer owners) script (before, previous)
  have packed := congrFun (RegistrationNativePlatformPackedState.simulate_pack
    (RegistrationNativePlatformExperiment.bundleHandler RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer) script)
    (attachP owners (before, previous))
  change ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((simulateQ (RegistrationNativePlatformExperiment.bundleHandler RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer) script).run
      (attach owners before)).run previous) = (simulateQ (target setup checks representation created writer) script).run (attachP owners (before, previous)) at packed
  rw [← packed] at coupled
  have law := congrArg (fun distribution => closeNative <$> distribution) coupled
  simp only [Functor.map_map, Prod.map, id_eq, attachP, attach, closeNative,
    RegistrationNativePlatformExperiment.bundle, StateT.run,
    bind_pure_comp, map_apply, script, reply] at law ⊢
  exact law

/-- Closing the original interpreter recovers the literal same native source bundle, including its actual shared writer and every failed prefix. -/
theorem original_source (owners : Owners) (before : Context n KemSK) (previous : Platform) (index : Nat) :
    closeOld <$> RegistrationNativePlatformIdentityProgram.runOld setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.originalBundle setup index writer)
      (((owners, RegistrationWorldAgreementCompiler.erase before.server.world), before), previous) =
      ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
        (attach owners before)).run previous := by
  rw [RegistrationNativePlatformIdentityBundleContext.bundle, Functor.map_map]
  exact native_bundle setup checks representation created writer owners before previous index

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle.original_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityNativeBundle.original_source
