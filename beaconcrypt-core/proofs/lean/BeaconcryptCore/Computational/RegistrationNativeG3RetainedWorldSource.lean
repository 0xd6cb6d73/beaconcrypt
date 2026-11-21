-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks
import BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys

/-! The original ordinary retained callbacks and the actual thin World use the same environment programs. This exact closure preserves their cache, installations, kernels, frames and signing results, projecting only the three independently billed accounting coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource
open PqxdhRecordLiftInterface (Slot EnvEffects effectLift)
open PqxdhDeploymentHiddenLayout (Material)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3MetricWorld (mask)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem public_world_pure (value : Value) :
    RegistrationNativePublicInterpreter.world (n := n) (KemSK := KemSK) (pure value) = pure value := by
  funext before
  simp only [RegistrationNativePublicInterpreter.world, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

private theorem public_world_bind {Next : Type}
    (first : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (next : Value → StateT (PqxdhRecordLiftWorld.State n) ProbComp Next) :
    RegistrationNativePublicInterpreter.world (KemSK := KemSK) (first >>= next) =
      (RegistrationNativePublicInterpreter.world first >>= fun value => RegistrationNativePublicInterpreter.world (next value)) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, { before with world := result.2 })) <$>
    simulateQ RegistrationNativePublicInterpreter.coins ((first >>= next).run before.world) =
      ((RegistrationNativePublicInterpreter.world first >>= fun value => RegistrationNativePublicInterpreter.world (next value)).run before)
  rw [StateT.run_bind, StateT.run_bind]
  simp only [RegistrationNativePublicInterpreter.world, StateT.run, simulateQ_bind, map_bind, bind_map_left]

private theorem public_effect_program (work : OracleComp (EnvEffects n) Value) :
    simulateQ (RegistrationNativePublicInterpreter.effect (KemSK := KemSK)) work =
      RegistrationNativePublicInterpreter.world (simulateQ PqxdhRecordLiftWorld.effects work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, public_world_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, public_world_bind]
      congr 1
      funext reply
      exact ih reply

/-- The actual ordinary retained compiler closes every complete environment program with the same full public state and unchanged selective service. -/
theorem public_effects (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : OracleComp (EnvEffects n) Value) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (keys : RegistrationNativeSelectiveHiddenService.State n) :
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds)
      ((RegistrationNativePublicRetained.ordinary hmac
        (simulateQ RegistrationNativePublicInterpreter.effect work)).run before)).run keys =
      (fun result => ((result.1, { before with world := result.2 }), keys)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [public_effect_program]
  exact RegistrationNativeG3RetainedCallbacks.world_source source input inside candidate materials seeds hmac _ before keys

private theorem public_world_closed (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    simulateQ (RegistrationNativePublicRootCoins.localImpl hmac)
      ((RegistrationNativePublicInterpreter.world work).run before) =
      (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world := by
  simp only [RegistrationNativePublicInterpreter.world, StateT.run, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have same : RegistrationNativePublicRootCoins.localImpl hmac ∘ₛ RegistrationNativePublicInterpreter.coins =
      QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [same, simulateQ_ofLift_eq_self]

/-- The original signer/compiler preserves its exact environment and chronological receipt result under the actual direct selective service. -/
theorem public_publication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : RegistrationBoundPublication.Spec.Domain) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (keys : RegistrationNativeSelectiveHiddenService.State n) :
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source input inside candidate materials seeds)
      ((RegistrationNativePublicRetained.ordinary setup.hmac
        (RegistrationNativePublicInterpreter.publication setup wire sign query)).run before)).run keys =
      (fun result => ((result.1.1, { before with world := result.2, receipts := result.1.2 }), keys)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run before.receipts)).run before.world := by
  rw [RegistrationNativeG3RetainedCallbacks.ordinary_source]
  simp only [RegistrationNativePublicInterpreter.publication, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, simulateQ_map]
  rw [public_effect_program, public_world_closed]
  simp only [Functor.map_map]
  rfl

/-- The same literal environment program is the actual guarded World program after accounting erasure, retaining the actual cache and installation chronology. -/
theorem world_effects (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (EnvEffects n) Value)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (simulateQ PqxdhRecordLiftWorld.effects work).run before =
      (simulateQ (RegistrationNativeG3MetricWorld.handler setup codec route)
        (simulateQ effectLift work)).run (mask before) := by
  rw [← RegistrationNativeG3MetricWorld.program_source, ← QueryImpl.simulateQ_compose]
  have same : CborRecordWorldSimulation.guarded setup codec route ∘ₛ (effectLift (n := n)) = PqxdhRecordLiftWorld.effects := by
    funext query
    simp only [QueryImpl.compose, effectLift, simulateQ_spec_query]
    rfl
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.public_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.public_effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.world_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.world_effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.public_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedWorldSource.public_publication
