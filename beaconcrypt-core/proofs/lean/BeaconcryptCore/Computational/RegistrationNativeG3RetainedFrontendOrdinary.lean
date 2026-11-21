-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendSource

/-! The same original signing and ordinary environment continuations run under both state layouts. Their complete source equation uses the concrete guarded World and the actual pool/provider callbacks, retaining every semantic coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot EnvEffects effectLift)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3RetainedFrontendSource (Frame project handler)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- Actual publication retains its signing response, chronological receipts and reached shared World in both full source layouts. -/
theorem publication_source (query : RegistrationBoundPublication.Spec.Domain) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds
      (.inl (.inr (.inl (.inr (.inl query)))))).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds
        (.inl (.inr (.inl (.inr (.inl query)))))).run (project before) := by
  rcases before with ⟨⟨ordinary, privateProvider⟩, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      ((fun result => (result.1, (result.2, privateProvider))) <$>
        (RegistrationNativePublicRetained.ordinary setup.hmac
          (RegistrationNativePublicInterpreter.publication setup wire sign query)).run ordinary)).run keys) = _
  rw [simulateQ_map, StateT.run_map, RegistrationNativeG3RetainedWorldSource.public_publication]
  have source := RegistrationNativeG3RetainedWorldSource.world_effects setup (RegistrationNativeWire.ledgerCodec wire) route
    ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run ordinary.receipts) ordinary.world
  have mapped := congrArg (Functor.map (fun result => (result.1.1,
    (((⟨keys.1, ordinary.pool, privateProvider, result.1.2⟩ : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState), keys.2), result.2)))) source
  simpa only [RegistrationNativeG3MaterializedDirectFrontend.handler,
    RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
    StateT.run, state_map_apply, simulateQ_map, project, Functor.map_map, Prod.map_def, id_eq] using mapped

/-- Every actual environment callback keeps its installation result and complete reached World under the same service/source reassembly. -/
theorem effect_source (query : (EnvEffects n).Domain) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds
      (.inl (.inr (.inl (.inr (.inr query)))))).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds
        (.inl (.inr (.inl (.inr (.inr query)))))).run (project before) := by
  rcases before with ⟨⟨ordinary, privateProvider⟩, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      ((fun result => (result.1, (result.2, privateProvider))) <$>
        (RegistrationNativePublicRetained.ordinary setup.hmac
          (RegistrationNativePublicInterpreter.world (PqxdhRecordLiftWorld.effects query))).run ordinary)).run keys) = _
  rw [simulateQ_map, StateT.run_map, RegistrationNativeG3RetainedCallbacks.world_source]
  have source := RegistrationNativeG3RetainedWorldSource.world_effects setup (RegistrationNativeWire.ledgerCodec wire) route
    ((EnvEffects n).query query : OracleComp (EnvEffects n) ((EnvEffects n).Range query)) ordinary.world
  have mapped := congrArg (Functor.map (fun result => (result.1,
    (((⟨keys.1, ordinary.pool, privateProvider, ordinary.receipts⟩ : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState), keys.2), result.2)))) source
  simpa only [RegistrationNativeG3MaterializedDirectFrontend.handler,
    RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
    StateT.run, state_map_apply, state_lift_apply, simulateQ_map, simulateQ_spec_query,
    project, Functor.map_map, Prod.map_def, id_eq] using mapped

/-- Every admitted or refused established-record callback retains its original reply, kernels, frames and shared cache under the source reassembly. -/
theorem record_source (query : PqxdhRecordLiftInterface.RecordQuery) (before : Frame n KemSK ProviderState) :
    Prod.map id project <$> (handler setup wire route sign seed scalar candidate provider materials seeds (.inr query)).run before =
      (RegistrationNativeG3MaterializedDirectFrontend.handler materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds (.inr query)).run (project before) := by
  rcases before with ⟨⟨ordinary, privateProvider⟩, keys⟩
  simp only [handler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
      ((fun result => (result.1, (result.2, privateProvider))) <$>
        (RegistrationNativePublicRetained.ordinary setup.hmac
          (RegistrationNativePublicInterpreter.world (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))).run ordinary)).run keys) = _
  rw [simulateQ_map, StateT.run_map, RegistrationNativeG3RetainedCallbacks.world_source]
  have source : Prod.map id RegistrationNativeG3MetricWorld.mask <$>
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))).run ordinary.world =
      (RegistrationNativeG3MetricWorld.handler setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))).run
        (RegistrationNativeG3MetricWorld.mask ordinary.world) := by
    simpa only [RegistrationNativeG3MetricWorld.handler, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      RegistrationNativeG3MetricWorld.guarded_input setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query)) ordinary.world
  have mapped := congrArg (Functor.map (fun result => (result.1,
    (((⟨keys.1, ordinary.pool, privateProvider, ordinary.receipts⟩ : RegistrationNativeHiddenInterpreter.State n KemSK ProviderState), keys.2), result.2)))) source
  simp only [RegistrationNativeG3MaterializedDirectFrontend.handler,
    RegistrationNativeG3LocalKeys.actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,
    StateT.run, state_map_apply, state_lift_apply, simulateQ_map, simulateQ_spec_query,
    project, Functor.map_map, Prod.map_def, id_eq] at mapped ⊢
  convert mapped using 1; rfl

end BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.publication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.effect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendOrdinary.record_source
