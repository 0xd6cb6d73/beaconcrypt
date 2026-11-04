-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps
/-! The literal shared-CTX compiler preserves indexed Ed creation and signing bills. Ambient hash/KEM/native sampling and independent platform coins cannot generate either capability. Counts refer to source requests, including rows born before a later failed owner installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {n : Nat} {I KemSK Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
inductive Kind where
  | create | sign
  deriving DecidableEq

def Target (kind : Kind) : Spec.Domain → Prop
  | .inl (.inl (.inr .create)) => kind = .create
  | .inl (.inl (.inr (.service _ (.sign _)))) => kind = .sign
  | _ => False
instance (kind : Kind) : DecidablePred (Target kind) := fun query => by
  unfold Target
  split <;> infer_instance

def Native (kind : Kind) : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain → Prop
  | .inr .create => kind = .create
  | .inr (.service _ (.sign _)) => kind = .sign
  | _ => False
instance (kind : Kind) : DecidablePred (Native (n := n) (KemSK := KemSK) kind) := fun query => by
  unfold Native
  split <;> infer_instance

def Program (kind : Kind) : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain → Prop
  | .inl _ => False
  | .inr query => Native (n := n) (KemSK := KemSK) kind query
instance (kind : Kind) : DecidablePred (Program (n := n) (KemSK := KemSK) kind) := fun query => by
  cases query <;> dsimp [Program] <;> infer_instance

theorem backend_zero (kind : Kind) (work : OracleComp RegistrationNativePlatformCtxBackend.Spec Value) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend work).IsQueryBoundP (Target kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationNativePlatformIdentityCtxCompiler.backend, Target, isQueryBoundP_query_iff]

private theorem query_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (kind : Kind) (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain)
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) query).run before).IsQueryBoundP
      (Target kind) (if Program (KemSK := KemSK) kind query then 1 else 0) := by
  rcases query with coin | ambient | query
  · cases kind <;> simp [RegistrationNativePlatformIdentityCtxCompiler.free,
      RegistrationNativePlatformIdentityCtxCompiler.implementation, StateT.run,
      RegistrationNativePlatformIdentityCtxCompiler.coins, Program, Target,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · exact backend_zero kind _
  · cases query with
    | create | reveal handle =>
      cases kind <;> simp [RegistrationNativePlatformIdentityCtxCompiler.free,
        RegistrationNativePlatformIdentityCtxCompiler.implementation, StateT.run,
        RegistrationNativePlatformIdentityCtxCompiler.joint, Program, Native, Target,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    | service handle request =>
      cases request <;> cases kind <;> simp [RegistrationNativePlatformIdentityCtxCompiler.free,
        RegistrationNativePlatformIdentityCtxCompiler.implementation, StateT.run,
        RegistrationNativePlatformIdentityCtxCompiler.joint, Program, Native, Target,
        isQueryBoundP_map_iff, isQueryBoundP_query_iff]

theorem program_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (kind : Kind) (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (Program (KemSK := KemSK) kind) cap)
    (before : RegistrationNativeIdentityWorld.Context n KemSK) :
    ((simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run before).IsQueryBoundP
      (Target kind) cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded (fun query current => query_bound setup checks representation created kind query current) before

theorem beacon_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (kind : Kind) (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (cap : Nat) (bounded : ∀ owners env previous, (((work.run owners).run env).run previous).IsQueryBoundP (Program (KemSK := KemSK) kind) cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work).run before).IsQueryBoundP (Target kind) cap := by
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon,
    StateT.run, isQueryBoundP_map_iff]
  exact program_bound setup checks representation created kind _ cap (bounded _ _ _) before.1.context

theorem native_bound (kind : Kind)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source Value)
    (cap : Nat) (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP (Native (KemSK := KemSK) kind) cap)
    (owners : RegistrationNativeIdentityFrontend.State source) (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform) :
    ((((RegistrationNativePlatformIdentityProgram.native work).run owners).run env).run previous).IsQueryBoundP (Program (KemSK := KemSK) kind) cap := by
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run, isQueryBoundP_map_iff]
  apply (bounded owners env).simulateQ_of_step
  · intro query counted
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, Program, counted, isQueryBoundP_query_iff]
  · intro query free
    simp [RegistrationNativePlatformIdentityProgram.nativeLift, Program, free, isQueryBoundP_query_iff]

theorem ordinary_zero (kind : Kind) (work : RegistrationNativePlatformCtxContext.M n KemSK Platform Value)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((RegistrationNativePlatformIdentityCtxOrdinary.ordinary (source := source) work).run before).IsQueryBoundP (Target kind) 0 := by
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary, RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run, isQueryBoundP_map_iff]
  exact backend_zero kind _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.backend_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.backend_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.beacon_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.ordinary_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEdCompilerBounds.ordinary_zero
