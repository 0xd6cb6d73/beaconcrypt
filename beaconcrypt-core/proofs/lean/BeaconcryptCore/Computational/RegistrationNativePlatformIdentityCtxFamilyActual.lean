-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRawEdBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxIndependentCreateBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
variable {V : Type}
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend



def fullProject {count : Nat}
    (result : RegistrationNativePlatformIdentityCtxFamily.Result count
      ((V × RegistrationNativeLedger.State) × ((RegistrationNativeIdentityMain.State n KemSK source × Platform) × RegistrationNativePlatformIdentityCtxSigningLog.Trace))) :
    V × (RegistrationNativeLedger.State × (((RegistrationNativeIdentityMain.State n KemSK source × Platform) × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × RegistrationNativePlatformIdentityCtxSource.State)) :=
  let original := RegistrationNativePlatformIdentityCtxFamily.project result
  (original.1.1.1,(original.1.1.2,(original.1.2,original.2)))

/-- The original full raw compiler with the actual signing monitor is literally the compiled free source tree, retaining its original ledger, full Main/P state, signing trace, pool and physical hash state. -/
theorem full_run (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (physical : RegistrationNativePlatformCtxBackend.State) :
    RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds actual mode work
      ((before,{}),(PqxdhDynamicIdentityPool.initialState,physical)) =
    (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
        ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run (before,{}))).run
            (PqxdhDynamicIdentityPool.initialState,physical) := by
  rw [RegistrationNativeFullCompiler.compile_run,RegistrationNativePlatformIdentityCtxSigningSource.typedHandler,
    QueryImpl.Stateful.simulateQ_link_run,Functor.map_map]
  rfl


/-- The original raw command allowance bounds every actual generated row after the passthrough signing monitor; failed later owner installation is still charged. -/
theorem logged_create_bound (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run (before,{})).IsQueryBoundP
        (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire serverKeyId bounds mode work budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  have free := RegistrationNativePlatformIdentityCtxTypedEdBounds.program_create_bound setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer _ (budget.cap 1) bill before
  have equation := RegistrationNativePlatformIdentityCtxSigningTrace.program_erasure frontend
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) (before,{})
  have mapped : (Prod.map id Prod.fst <$> (simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run (before,{})).IsQueryBoundP
      (RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create) budget.create := by
    rw [equation]
    exact free
  exact (isQueryBoundP_map_iff _ _ _).mp mapped


/-- Original Respects yields the actual whole raw source marginal of one reserved family of size qCreate+1, without any source-representation or controller-correspondence premise. -/
theorem full_marginal (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (physical : RegistrationNativePlatformCtxBackend.State) :
    EvalDistEq (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds actual mode work
      ((before,{}),(PqxdhDynamicIdentityPool.initialState,physical)))
      (fullProject <$> RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1)
        ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run (before,{})) physical) := by
  have cap := RegistrationNativePlatformIdentityCtxIndependentCreateBounds.program_bound _ budget.create
    (logged_create_bound setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded before) physical
  have marginal := (RegistrationNativePlatformIdentityCtxFamily.source_marginal setup.joint (budget.create+1) _ physical
    (cap.mono (Nat.le_succ _))).map (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2))))
  rw [full_run setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before physical]
  simp only [Functor.map_map] at marginal
  exact marginal

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.full_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.full_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.logged_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.logged_create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.full_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual.full_marginal
