-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame

/-! The actual publication leaves do not read the compact owner controller's independently threaded environment. The syntactic scope excludes the indexed KEM Other interface, which does read its role auxiliary field. Replacing that environment inside Context commutes with every admitted publication leaf and adaptive tree, retaining the complete World, private KEM pool, true counters and every indexed/hash request. This is a fact about the literal current ambient dictionary, not arbitrary ambient handlers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
abbrev Env := RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State

def Allowed : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain → Prop
  | .inr (.inl (.inr _)) => False
  | _ => True

def patch (environment : Env) (before : Context n KemSK) : Context n KemSK :=
  {before with server := {before.server with
    world := RegistrationWorldAgreementCompiler.join environment before.server.world.world.1}}

private theorem world_frame {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : StateT (PqxdhRecordLiftWorld.State n) m Value) (environment : Env) (before : Context n KemSK) :
    Prod.map id (patch environment) <$> (RegistrationNativePlatformIdentityCtxAmbient.world work).run before =
      (RegistrationNativePlatformIdentityCtxAmbient.world work).run (patch environment before) := by
  simp only [RegistrationNativePlatformIdentityCtxAmbient.world, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    patch, RegistrationWorldAgreementCompiler.join]

/-- Literal physical/hash/identity leaves within the syntactic publication scope are exactly equivariant under replacing the separately threaded compact environment. -/
theorem query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (request : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain) (allowed : Allowed (n := n) (KemSK := KemSK) request)
    (environment : Env) (before : Context n KemSK) :
    Prod.map id (patch environment) <$>
      ((RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) request).run before) =
      (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created) request).run (patch environment before) := by
  cases request with
  | inl coin =>
    simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
      StateT.run, Functor.map_map, Prod.map_def, id_eq]
  | inr request => cases request with
    | inl request =>
      cases request with
      | inl effect =>
        have same := congrArg (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend)
          (world_frame (RegistrationNativePlatformCtxEffects.program effect) environment before)
        simpa only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
          RegistrationNativePlatformIdentityCtxAmbient.program, StateT.run, simulateQ_map] using same
      | inr kem => exact False.elim allowed
    | inr request =>
      cases request <;>
        simp only [RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
          StateT.run, Functor.map_map, Prod.map_def, id_eq, RegistrationNativeIdentityCompiler.advance,
          patch, RegistrationWorldAgreementCompiler.join]

/-- Every source tree within the syntactic publication scope has the same environment-patch commutation with all emitted free requests preserved. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK))) (environment : Env) (before : Context n KemSK) :
    Prod.map id (patch environment) <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
        (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) work).run (patch environment before) :=
  by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← query setup checks representation created request allowed.1 environment before]
    simp only [bind_map_left]
    exact bind_congr (fun result => ih result.1 (allowed.2 result.1) result.2)

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxEnvPatch.program
