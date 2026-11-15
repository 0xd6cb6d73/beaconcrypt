-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler
/-! The literal free source compiler does not append raw ML receipt payloads. Clearing that one Context field commutes exactly with every actual source query and adaptive program, retaining physical hash/coin requests, indexed key creation, private KEM/auxiliary state and every native counter. Compact source Env receipts are joined separately by the enclosing owner controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformCtxBuildReceiptView (context)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem world_frame {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : StateT (PqxdhRecordLiftWorld.State n) m A) (before : Context n KemSK) :
    Prod.map id context <$> (RegistrationNativePlatformIdentityCtxAmbient.world work).run before =
      (RegistrationNativePlatformIdentityCtxAmbient.world work).run (context before) := by
  simp only [RegistrationNativePlatformIdentityCtxAmbient.world, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    context, RegistrationNativePlatformCtxSdkReceiptView.serverView, RegistrationNativePlatformIdentityReceiptView.view]

private theorem kem_frame (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) (before : Context n KemSK) :
    Prod.map id context <$> (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run before =
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run (context before) := by
  simp only [RegistrationNativeIdentityWorld.ambient, RegistrationNativeExperiment.trusted,
    RegistrationNativeIdentityWorld.embed, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view]
  rfl

private theorem ambient_frame (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeIdentityFrontend.Ambient n KemSK).Domain) (before : Context n KemSK) :
    Prod.map id context <$> (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created query).run before =
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created query).run (context before) := by
  cases query with
  | inl query => exact world_frame _ before
  | inr query =>
    have same := congrArg (simulateQ RegistrationNativePlatformCtxBackend.coin)
      (kem_frame (source := source) setup checks representation created query before)
    simpa only [RegistrationNativePlatformIdentityCtxAmbient.program, StateT.run, simulateQ_map] using same

/-- Every actual free compiler query is strongly equivariant under clearing only the raw Context ML receipt list; no physical/private operational coordinate is omitted. -/
theorem query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (request : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain) (before : Context n KemSK) :
    Prod.map id context <$>
      ((RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) request).run before) =
      (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) request).run (context before) := by
  cases request with
  | inl coin =>
    simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
      StateT.run, Functor.map_map, Prod.map_def, id_eq]
  | inr request => cases request with
    | inl request =>
      have same := congrArg (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend)
        (ambient_frame (source := source) setup checks representation created request before)
      simpa only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        StateT.run, simulateQ_map] using same
    | inr request =>
      cases request <;>
        simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
          StateT.run, Functor.map_map, Prod.map_def, id_eq, RegistrationNativeIdentityCompiler.advance,
          context, RegistrationNativePlatformCtxSdkReceiptView.serverView, RegistrationNativePlatformIdentityReceiptView.view]

/-- The exact same free source program commutes with raw receipt erasure throughout all adaptive continuations and retains every emitted backend and indexed protocol call. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) A) (before : Context n KemSK) :
    Prod.map id context <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run (context before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ context (query setup checks representation created) work before
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame.program
