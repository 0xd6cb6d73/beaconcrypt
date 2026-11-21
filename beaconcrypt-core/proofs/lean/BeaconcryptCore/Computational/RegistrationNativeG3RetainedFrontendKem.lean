-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource

/-! The ordinary retained compiler and the thin interpreter call the identical actual KEM provider on the same generated-key pool and provider state. Its primitive coin accounting is removed only by the established bilateral metric projection; the reached pool and all semantic World/cache fields stay literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendKem
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot effectLift coinLift)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3RetainedFrontendSource (Frame project handler)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem sampled_metrics (work : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeG3MetricWorld.mask <$> (PqxdhRecordLiftWorld.sampled work).run before =
      (fun value => (value, RegistrationNativeG3MetricWorld.mask before)) <$> work := by
  have source := congrArg (Functor.map (Prod.map id RegistrationNativeWorldView.project))
    (RegistrationNativeKemWorldUniform.sampled_mask work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeG3MetricWorld.mask] using source

/-- The actual full KEM provider continuation has the same reply, reached opaque pool/provider state and semantic World in both original source layouts. -/
theorem routed_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds
      (.inl (.inr (.inr query)))).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds
        (.inl (.inr (.inr query)))).run (project before) := by
  rcases before with ⟨⟨ordinary, privateProvider⟩, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      ((fun result => (result.1.1, ({ ordinary with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        simulateQ RegistrationNativePublicRetained.coins
          ((PqxdhRecordLiftWorld.sampled ((provider query).run (ordinary.pool, privateProvider))).run ordinary.world))).run keys) = _
  rw [simulateQ_map, StateT.run_map, RegistrationNativeG3RetainedCallbacks.coins_source]
  have sampled := sampled_metrics ((provider query).run (ordinary.pool, privateProvider)) ordinary.world
  have thin := RegistrationNativeG3MetricCoins.program_source setup (RegistrationNativeWire.ledgerCodec wire) route
    ((provider query).run (ordinary.pool, privateProvider)) ordinary.world
  simp only [RegistrationNativeG3MetricCoins.program, ← QueryImpl.simulateQ_compose] at thin
  have same : effectLift (n := n) ∘ₛ RegistrationNativeHiddenService.coins = coinLift := rfl
  rw [same] at thin
  have source := sampled.trans thin.symm
  have mapped := congrArg (Functor.map (fun result => (result.1.1,
    (((⟨keys.1, result.1.2.1, result.1.2.2, ordinary.receipts⟩ : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState), keys.2), result.2)))) source
  simpa only [RegistrationNativeG3MaterializedDirectFrontend.handler,
    RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.routed,
    StateT.run, state_map_apply, simulateQ_map, ← QueryImpl.simulateQ_compose,
    project, Functor.map_map, Prod.map_def, id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendKem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendKem.routed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendKem.routed_source
