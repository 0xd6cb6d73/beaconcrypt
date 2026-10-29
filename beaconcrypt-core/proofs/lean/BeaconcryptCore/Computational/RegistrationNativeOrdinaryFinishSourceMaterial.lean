-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCompletion

/-! Material demand and the Beacon's no-sign opening are interpreted on the reached literal-source World. These equations retain the private root memo and signing receipts and the complete indexed pool. They apply equally to an ordinary translated reference and to a selected owner's original reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeKemReferenceWorld (withWorld)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

noncomputable def service (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (StateT (Private n KemSK) ProbComp) :=
  fun query => implementation setup wire route sign seed scalar (.inr (.inl query))

noncomputable def common (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (StateT (Private n KemSK) ProbComp) :=
  fun query => service setup wire route sign seed scalar (.inr query)

/-- A material request reads only the actual returned reference's current memo cell. -/
theorem demand_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (before : Private n KemSK) :
    (service setup wire route sign seed scalar (.inl message)).run before =
      pure ((before.extra.1 message).map (fun root => RegistrationNativePairedChoice.Choice.known
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)), before) := by
  simp only [service, implementation, RegistrationNativeKemReferenceEffects.implementation,
    RegistrationNativeKemReferenceWorld.handler, RegistrationServerOpenReferenceSourceStage.callbacks,
    RegistrationNativePublicSourceCallbacks.services, RegistrationNativePublicInterpreter.handler]
  change Prod.map id RegistrationNativePublicSourceEffects.toPrivate <$>
    simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
      (((do
        let current ← get
        pure ((current.roots message).map (fun root => RegistrationNativePairedChoice.Choice.known
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root)))) : RegistrationNativePublicInterpreter.M n KemSK
            (Option (RegistrationNativePairedChoice.Choice n))).run
            (RegistrationNativePublicSourceEffects.fromPrivate before)) = _
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, simulateQ_pure, map_pure,
    RegistrationNativePublicSourceEffects.fromPrivate, RegistrationNativePublicSourceEffects.toPrivate,
    Prod.map, id_eq]

private theorem effect_program (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (simulateQ RegistrationNativePublicInterpreter.effect work).run before =
      (RegistrationNativePublicInterpreter.world (simulateQ PqxdhRecordLiftWorld.effects work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output =>
      simp only [simulateQ_pure, RegistrationNativePublicInterpreter.world,
        StateT.run, map_pure, StateT.monad_pure_def, StateT.pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [RegistrationNativePublicInterpreter.effect, RegistrationNativePublicInterpreter.world,
        StateT.run, StateT.monad_bind_def, StateT.bind, simulateQ_bind,
        map_bind, bind_map_left]
      apply bind_congr
      rintro ⟨reply, after⟩
      exact ih reply { before with world := after }

private theorem raw_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : RegistrationRawSealBridge.Spec.Domain) :
    common (n := n) setup wire route sign seed scalar (.inl (.inl query)) =
      withWorld (simulateQ PqxdhRecordLiftWorld.effects
        (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query)) := by
  have raw : RegistrationNativePublicInterpreter.publication (n := n) setup wire sign (.inl query) =
      RegistrationNativePublicInterpreter.world (simulateQ PqxdhRecordLiftWorld.effects
        (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query)) := by
    apply StateT.ext
    intro state
    change ((do
      let current ← get
      let result ← simulateQ RegistrationNativePublicInterpreter.effect
        ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign (.inl query)).run current.receipts)
      modify fun after => { after with receipts := result.2 }
      pure result.1) : RegistrationNativePublicInterpreter.M n KemSK _).run state = _
    rw [StateT.run_bind, StateT.run_get, pure_bind]
    simp only [RegistrationBoundSourceCompiler.compiler, StateT.run,
      simulateQ_map, bind_map_left]
    have programs : simulateQ (RegistrationNativePublicInterpreter.effect (n := n) (KemSK := KemSK))
        (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query) =
        RegistrationNativePublicInterpreter.world (simulateQ PqxdhRecordLiftWorld.effects
          (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query)) := by
      apply StateT.ext
      exact effect_program _
    rw [programs]
    simp only [RegistrationNativePublicInterpreter.world, StateT.run, StateT.monad_bind_def,
      StateT.bind, StateT.monad_pure_def, StateT.pure, bind_map_left]
    have modified (update : RegistrationNativePublicInterpreter.State n KemSK →
        RegistrationNativePublicInterpreter.State n KemSK)
        (current : RegistrationNativePublicInterpreter.State n KemSK) :
        (modify update : RegistrationNativePublicInterpreter.M n KemSK Unit) current =
          pure ((), update current) := rfl
    simp only [modified, map_pure, bind_pure_comp]
  apply StateT.ext
  intro before
  change Prod.map id RegistrationNativePublicSourceEffects.toPrivate <$>
    (RegistrationNativePublicSourceEffects.close setup seed scalar
      (RegistrationNativePublicInterpreter.publication setup wire sign (.inl query))).run
        (RegistrationNativePublicSourceEffects.fromPrivate before) = _
  rw [raw, RegistrationNativePublicSourceEffects.close_world]
  simp only [Functor.map_map, withWorld, StateT.run,
    RegistrationNativePublicSourceEffects.fromPrivate, RegistrationNativePublicSourceEffects.toPrivate,
    Prod.map, id_eq]
  rfl

/-- Every adaptive no-sign opening uses the same actual World program and retains all other private coordinates. -/
theorem raw_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp RegistrationRawSealBridge.Spec Value) (before : Private n KemSK) :
    (simulateQ (common setup wire route sign seed scalar)
      (simulateQ RegistrationNativePairedBeaconService.rawLift work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite) work)).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have step : common (n := n) setup wire route sign seed scalar ∘ₛ RegistrationNativePairedBeaconService.rawLift =
      fun query => withWorld (simulateQ PqxdhRecordLiftWorld.effects
        (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query)) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePairedBeaconService.rawLift, simulateQ_spec_query]
    exact raw_query setup wire route sign seed scalar query
  rw [step, RegistrationNativeKemReferenceWorld.world_program, ← QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial.demand_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial.demand_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial.raw_program
