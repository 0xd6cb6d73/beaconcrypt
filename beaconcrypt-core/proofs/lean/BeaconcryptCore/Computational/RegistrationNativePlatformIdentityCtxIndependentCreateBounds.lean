-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependent
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds

/-! Reifying the actual physical CTX tree over independent uniforms preserves the exact generated-identity creation cap. Physical hash work cannot create a row. Typed and original full raw budget specializations retain every Main/platform/physical poststate and rows born before a later callback failure. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxIndependent (independent protocol reify)
open RegistrationNativeIdentityIndependentSource (IsCreate)
open RegistrationNativeIdentityIndependentSource renaming Spec → IndependentSpec
open RegistrationNativePlatformIdentityCtxEdCompilerBounds (Target)
variable {A : Type}

/-- Actual independent hash samplers never issue generated-identity creation. -/
theorem independent_zero (work : ProbComp A) :
    (simulateQ independent work).IsQueryBoundP IsCreate 0 := by
  apply RawCtxSourceOpen.simulate_bound independent (fun _ => False) IsCreate work 0 (isQueryBoundP_false work 0)
  intro coin
  simp [independent, IsCreate, isQueryBoundP_query_iff]

/-- Each literal source leaf preserves its one original generated-row charge, including every physical hash coin continuation. -/
theorem query_bound (query : Spec.Domain) (physical : RegistrationNativePlatformCtxBackend.State) :
    ((reify query).run physical).IsQueryBoundP IsCreate (if Target .create query then 1 else 0) := by
  cases query with
  | inr bytes => exact independent_zero ((RegistrationNativePlatformCtxBackend.physical bytes).run physical)
  | inl query => cases query with
    | inr report => simp [reify, protocol, Target, isQueryBoundP_pure]
    | inl query => cases query with
      | inl coin => simp [reify, protocol, StateT.run_lift, bind_pure_comp, Target, IsCreate, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      | inr request => cases request <;>
        simp [reify, protocol, StateT.run_lift, bind_pure_comp, Target, IsCreate, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Complete adaptive reification retains the original source creation cap with full result and physical cache/journal state. -/
theorem program_bound (work : OracleComp Spec A) (cap : Nat) (bounded : work.IsQueryBoundP (Target .create) cap)
    (physical : RegistrationNativePlatformCtxBackend.State) :
    ((simulateQ reify work).run physical).IsQueryBoundP IsCreate cap :=
  OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded query_bound physical

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- The literal current typed callback tree supplies the generated-row cap to the reified family client. -/
theorem typed_bound (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (physical : RegistrationNativePlatformCtxBackend.State) :
    ((simulateQ reify ((simulateQ frontend work).run before)).run physical).IsQueryBoundP IsCreate cap :=
  program_bound _ cap (RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer work cap bounded before) physical

/-- Original raw Respects bounds actual created rows, including generation before any later owner or writer failure. -/
theorem raw_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (physical : RegistrationNativePlatformCtxBackend.State) :
    ((simulateQ reify ((simulateQ frontend (RegistrationNativeFullCompiler.compile setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)).run before)).run physical).IsQueryBoundP IsCreate budget.create := by
  exact program_bound _ (budget.cap 1) (RegistrationNativePlatformIdentityCtxRawEdBounds.run_create_bound setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded before) physical

/-- An independently supplied full compiler wire needs no canonicality restriction: the original source create allowance is preserved by typed compilation and reification. -/
theorem full_bound (compilerWire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) (physical : RegistrationNativePlatformCtxBackend.State) :
    ((simulateQ reify ((simulateQ frontend (RegistrationNativeFullCompiler.compile setup.source.crypto
      compilerWire serverKeyId bounds mode work)).run before)).run physical).IsQueryBoundP IsCreate budget.create := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto compilerWire serverKeyId bounds mode work budget bounded 1
  simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact typed_bound setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    _ (budget.cap 1) bill before physical

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.independent_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.independent_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.query_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.typed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.typed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.raw_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.full_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds.full_bound
