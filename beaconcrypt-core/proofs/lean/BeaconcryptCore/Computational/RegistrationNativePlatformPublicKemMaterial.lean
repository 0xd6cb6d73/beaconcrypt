-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal
/-! Corrected OPEN acceptance, moved-token source build and assigned-ID finish have no indexed private birth or secret reveal. Bounds follow their literal common-platform execution trees and retain every failed prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicKemLocal (LocalPrivate native_program platform_zero)
open RegistrationNativeKemBeaconFootprint (Kind)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
private def acceptHandler (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (Base n KemSK Platform)
  | .inl query => localHandler selected query
  | .inr _ => platform reserve
private def SyntaxPrivate (kind : Kind) : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind query
  | .inr _ => False
private instance (kind : Kind) : DecidablePred (SyntaxPrivate (n := n) (KemSK := KemSK) kind) := fun query => by
  cases query <;> dsimp [SyntaxPrivate] <;> infer_instance

private theorem private_other (kind : Kind) (query : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain)
    (counted : SyntaxPrivate (KemSK := KemSK) kind query) :
    RegistrationNativePlatformServerOpenSyntaxBounds.queryKind query = .other := by
  rcases query with (message | (message | common) | kem) | reserve
  · exact counted.elim
  · exact counted.elim
  · exact counted.elim
  · rcases kem with other | (pool | key)
    · rfl
    · rfl
    · exact counted.elim
  · exact counted.elim

private theorem syntax_bound (kind : Kind) (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (SyntaxPrivate (KemSK := KemSK) kind) 0) (before : Platform) :
    ((simulateQ (acceptHandler selected reserve) work).run before).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) 0 := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    cases query with
    | inl query =>
      simpa only [acceptHandler, simulateQ_spec_query] using native_program kind selected
        (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 1
        (by rw [isQueryBoundP_query_iff]; intro _; exact Nat.zero_lt_one) current
    | inr query => exact counted.elim
  · intro query free current
    cases query with
    | inl query =>
      simpa only [acceptHandler, simulateQ_spec_query] using native_program kind selected
        (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) 0
        (by rw [isQueryBoundP_query_iff]; intro hit; exact (free hit).elim) current
    | inr query => exact platform_zero kind reserve current

attribute [local irreducible] RegistrationNativePlatformServerOpenSyntax.accept
  RegistrationNativePlatformServerOpenControl.afterPin

/-- The literal corrected OPEN controller has zero private-birth and reveal cost, including its actual reservation. -/
theorem accept_zero (kind : Kind) (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) selected) (platform reserve) setup checks verify packet).run front).run env).run before).IsQueryBoundP
      (LocalPrivate (KemSK := KemSK) kind) 0 := by
  have source := congrArg (fun work => ((work.run front).run env).run before)
    (RegistrationNativePlatformServerOpenSyntax.accept_source (acceptHandler (n := n) (KemSK := KemSK) selected reserve) setup checks verify packet)
  have implementation_eq : RegistrationNativePlatformServerOpenSyntax.implementation (acceptHandler (n := n) (KemSK := KemSK) selected reserve) = localHandler (n := n) (KemSK := KemSK) selected := by
    funext query
    rfl
  rw [implementation_eq] at source
  simp only [acceptHandler] at source
  rw [← source]
  apply syntax_bound kind selected reserve
  exact (RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound setup checks verify .other packet front env).of_imp (private_other kind)

private theorem ordinary_bound (kind : Kind) (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) 0) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeOpenKeyKemBeacon.IsPrivate, ite_false]
    split <;> simp [RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  | inr query =>
    simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff]
    intro counted
    rw [ite_eq_left counted]
    exact Nat.zero_lt_one

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Selected and ordinary corrected finish paths never create or reveal an indexed private key. -/
theorem finish_zero (kind : Kind) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) {source : RegistrationNativeMldsa.Source}
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run owners).run env).run before).IsQueryBoundP
      (LocalPrivate (KemSK := KemSK) kind) 0 := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
    simp only [map_apply, isQueryBoundP_map_iff]
    apply native_program
    cases own : owner.scalar with
    | none => exact RegistrationNativePlatformPublicFinishAllocationCaps.finish_free kind setup wire packet owner.view env
    | some scalar => exact ordinary_bound kind setup scalar _ (RegistrationNativePlatformPublicFinishAllocationCaps.finish_free kind setup wire packet owner.view env)

/-- Every request in the actual source build compiler excludes private indexed KEM access. -/
theorem build_embedding (kind : Kind) (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A) :
    (simulateQ (buildEmbedding (KemSK := KemSK)) work).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  rcases query with message | effect | coin
  · simp [buildEmbedding, localQuery, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]
  · simp [buildEmbedding, RegistrationNativePlatformPublicFrontend.effect, localQuery, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, isQueryBoundP_query_iff]
  · simp [buildEmbedding, localCoin, LocalPrivate, isQueryBoundP_query_iff]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.accept_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.accept_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.finish_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.finish_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.build_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemMaterial.build_embedding
