-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOrdinaryLens
/-! The corrected owner finish has no external platform request. Its literal new local syntax is the finite corrected reference AST embedded through the same public request language, leaving the persistent P value unchanged. This statement concerns syntax and all failed continuations, not an earlier finish controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishEmbedding
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem local_run (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (previous : Platform) :
    ((simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work) previous) =
      (fun value => (value, previous)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work := by
  change ((simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run previous) = _
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.localHandler,
      StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, ih, map_bind]

private theorem local_tree (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      (simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work) =
    simulateQ RegistrationNativePlatformPublicFrontend.old
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with message | message | query | query
  · rfl
  · rfl
  · cases query <;> rfl
  · cases query <;> rfl

private theorem finish_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (previous : Platform) :
    (RegistrationNativePlatformPublicFrontend.finish (n := n) setup wire source index packet) owners env previous =
      (fun value => (value, previous)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false)
        ((RegistrationNativePlatformPublicFinishRoster.finish setup wire source index packet) owners env) := by
  cases found : owners[index]? with
  | none => simp only [RegistrationNativePlatformPublicFrontend.finish, RegistrationNativePlatformPublicFinishRoster.finish,
      found, pure_apply, map_pure, simulateQ_pure]
  | some owner =>
    cases scalar : owner.scalar <;>
      simp only [RegistrationNativePlatformPublicFrontend.finish, RegistrationNativePlatformPublicFinishRoster.finish,
        StateT.run, found, scalar, RegistrationNativeOrdinaryFinishSourcePhase.adapt,
        simulateQ_id', map_apply, local_run, simulateQ_map, Functor.map_map, Prod.map_def, id_eq]

/-- Actual corrected public finishing is the exact local AST, with its complete P result retained. -/
theorem body (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformPublicFrontend.executeLocal
      (RegistrationNativePlatformPublicFrontend.beacon (RegistrationNativePlatformPublicFrontend.finish (n := n) (Platform := Platform) setup wire source index packet)) =
      RegistrationNativePlatformPublicSourceOrdinaryLens.oldProgram
        (RegistrationNativePublicFrontend.beacon (RegistrationNativePlatformPublicFinishRoster.finish setup wire source index packet)) := by
  funext before
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePlatformPublicSourceOrdinaryLens.oldProgram, RegistrationNativePublicFrontend.beacon,
    StateT.run, finish_run, simulateQ_map, Functor.map_map, local_tree]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishEmbedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishEmbedding.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishEmbedding.body
