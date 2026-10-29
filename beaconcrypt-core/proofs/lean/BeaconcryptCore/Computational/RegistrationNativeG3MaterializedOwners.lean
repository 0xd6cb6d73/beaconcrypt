-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-! Ordinary owners materialize only their own root preparation coordinates. Every demand and Common callback remains literal, so this translation commutes with the concrete materialized interface by changing only its executable fallback. The full mixed owner roster therefore preserves all finish outcomes, current environment fields and the distinct private receipt/World frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG3MaterializedFrontend (ServiceSpec State)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK KeyState Auxiliary : Type} {base : OracleSpec ι}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

/-- Ordinary local DH changes only the fallback preparation callback; all material demands and Common effects retain their literal interface. -/
theorem ordinary_interface (full : Bool) (setup : Setup base KemSK) (scalar : ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp)) :
    localImpl full setup.source writer sign seeds service fallback ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar =
      localImpl full setup.source writer sign seeds service (fallback ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar) := by
  funext query
  rcases query with message | query | query
  · simp only [QueryImpl.compose, RegistrationNativePublicOwners.ordinary, localImpl]
    cases formed : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message <;>
      simp only [simulateQ_pure, simulateQ_spec_query, localImpl]
  · simp only [QueryImpl.compose, RegistrationNativePublicOwners.ordinary, localImpl, simulateQ_spec_query]
  · simp only [QueryImpl.compose, RegistrationNativePublicOwners.ordinary, localImpl, simulateQ_spec_query]

/-- The complete ordinary-owner finish retains every actual local failure and full reached state under the materialized service. -/
theorem ordinary_finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (scalar : ScalarBytes)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (packet : Option registration.ResponsePacket) (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (env : EnvState Auxiliary) (before : State n KeyState) :
    (simulateQ (localImpl true setup.source writer sign seeds service fallback)
      (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
        (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env))).run before =
      (simulateQ (localImpl false setup.source writer sign seeds service fallback)
        (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
          (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env))).run before := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ordinary_interface, ordinary_interface]
  exact RegistrationNativeG3MaterializedBeaconFinish.finish setup source writer sign seeds service
    (fallback ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar) packet owner env before

attribute [local irreducible] RegistrationBeaconReferenceFinish.finish

/-- Actual mixed roster dispatch selects the stored ordinary scalar or selected scalar-free controller and preserves every owner, environment and private receipt/World field. -/
theorem finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : EnvState Auxiliary) (before : State n KeyState) :
    (simulateQ (localImpl true setup.source writer sign seeds service fallback)
      (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run before =
      (simulateQ (localImpl false setup.source writer sign seeds service fallback)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run before := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [simulateQ_map, state_map_apply]
      cases scalarShape : owner.scalar with
      | none =>
          simp only []
          have same := RegistrationNativeG3MaterializedBeaconFinish.finish setup source writer sign seeds service fallback packet owner.view env before
          simp only [StateT.run] at same
          rw [same]
      | some scalar =>
          simp only []
          have same := ordinary_finish setup source scalar writer sign seeds service fallback packet owner.view env before
          simp only [StateT.run] at same
          rw [same]
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.ordinary_interface' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.ordinary_interface
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.ordinary_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.ordinary_finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOwners.finish
