-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter

/-! Restricted environment closure of the concrete thin native backend. Every local root, material, publication, coin and opaque KEM operation uses only EnvEffects. The total projection gives fixed unused replies to ongoing record requests; its source law is proved only on local callbacks, before any environment frontend uses it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec effectLift coinLift)
open RegistrationNativeHiddenInterpreter (State Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def project : QueryImpl (WorldSpec n) (OracleComp (EnvEffects n))
  | .inl _ => pure ()
  | .inr (.inl query) => (EnvEffects n).query query
  | .inr (.inr (.inl (.inl _))) => pure none
  | .inr (.inr (.inl (.inr _))) => pure .None
  | .inr (.inr (.inr (_, .inl _))) => pure none
  | .inr (.inr (.inr (_, .inr _))) => pure .None

/-- Closing the actual environment effect embedding recovers exactly its original primitive AST. -/
theorem effects_project (work : OracleComp (EnvEffects n) Value) :
    simulateQ project (simulateQ effectLift work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : project ∘ₛ effectLift = (fun query => ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) := by
    funext query
    simp only [QueryImpl.compose, effectLift, simulateQ_spec_query, project]
  rw [same]
  change simulateQ (QueryImpl.id' (EnvEffects n)) work = work
  exact simulateQ_id' work

/-- Local probability draws close through the same EnvEffects coin surface. -/
theorem coins_project (work : ProbComp Value) :
    simulateQ project (simulateQ (coinLift (n := n)) work) =
      simulateQ (fun query => ((EnvEffects n).query (.inl query) : OracleComp (EnvEffects n) _)) work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

abbrev M (n : Nat) (KemSK ProviderState Value : Type) :=
  StateT (State n KemSK ProviderState) (OracleComp (EnvEffects n)) Value

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (M n KemSK ProviderState) := fun query before =>
  simulateQ project ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider query).run before)

/-- Every actual local callback embeds back into precisely the same World AST and full thin-client state. -/
theorem local_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (RegistrationNativePublicFrontend.RoutedLocalSpec n KemSK).Domain)
    (before : State n KemSK ProviderState) :
    simulateQ effectLift ((handler setup wire sign seed scalar provider (.inl query)).run before) =
      (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inl query)).run before := by
  unfold handler
  rcases query with message | ((demand | publication | effect) | kem)
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.onKeys,
      StateT.run, simulateQ_map, effects_project]
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.onKeys,
      StateT.run, simulateQ_map, effects_project]
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
      StateT.run, simulateQ_map, effects_project]
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
      StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query, effectLift, project]
    simp only [StateT.run, simulateQ_map, simulateQ_spec_query]
    rfl
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.routed,
      StateT.run, simulateQ_map, coins_project]
    rw [← QueryImpl.simulateQ_compose]
    rfl

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.effects_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.effects_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.coins_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.coins_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler.local_query
