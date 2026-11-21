-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution

/-! The mixed reference source and actual native model use one record World, cache and hidden-material table. Source reassembly preserves every semantic World field; the explicit output view omits only native/coin/record-log instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every concrete World computation has its exact full native source state and optional result after the explicitly named output view. -/
theorem world_source (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) (before : State n KemSK source) :
    (fun output => (output.1, project roots scalar before.1 output.2)) <$>
      (RegistrationNativePublicSourceEffects.close setup seed scalar
        (RegistrationNativePublicInterpreter.world work)).run before.2 =
      Prod.map id nativeView <$> (RegistrationNativeExperiment.world work).run (restore roots scalar before.1 before.2) := by
  rw [RegistrationNativePublicSourceEffects.close_world]
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    project, nativeView, restore, RegistrationServerMaterialSourceState.nativeView,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore,
    RegistrationWorldAgreementCompiler.join]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Forwarded ordinary environment effects execute the actual native World and retain its full cache, hidden seeds and source protocol state. -/
theorem effect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State n KemSK source) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
        (StateT.lift (RegistrationNativePublicFrontend.effect query))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects query)).run (restore roots scalar before.1 before.2) := by
  have closed := world_source setup seed scalar roots (PqxdhRecordLiftWorld.effects query) before
  simpa only [RegistrationNativePublicSourceExecution.execute, RegistrationNativePublicFrontend.effect,
    RegistrationNativePublicFrontend.liftLocal, RegistrationNativePublicInterpreter.handler,
    RegistrationNativePublicInterpreter.common, RegistrationNativePublicInterpreter.effect,
    RegistrationNativePublicSourceEffects.close, StateT.run_lift, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, StateT.run, state_map_apply,
    Functor.map_map, Prod.map_def, id_eq] using closed

private theorem direct_record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK source) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
        (fun frontend => (fun reply => (reply, frontend)) <$>
          ((RegistrationNativePublicFrontend.Spec n KemSK).query (.inr query) :
            OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.world (CborRecordWorldSimulation.guarded setup
          (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query)))).run (restore roots scalar before.1 before.2) := by
  have closed := world_source setup seed scalar roots
    (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))) before
  simp only [RegistrationNativePublicSourceExecution.execute,
    RegistrationNativePublicInterpreter.handler, RegistrationNativePublicSourceEffects.close,
    simulateQ_map, simulateQ_spec_query, StateT.run, state_map_apply,
    Functor.map_map, Prod.map_def, id_eq] at closed ⊢
  convert closed using 1 <;> rfl

/-- Actual record commands resolve each native public owner handle through its stored World handle before executing the same complete admitted World program. -/
theorem record_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK source) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
        (RegistrationNativePublicFrontend.record query)).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.record setup wire route query source).run (restore roots scalar before.1 before.2) := by
  cases query with
  | inl query => exact direct_record setup wire route sign seed scalar roots (.inl query) before
  | inr query =>
      rcases query with ⟨owner, request⟩
      cases request with
      | inl plaintext =>
          cases found : before.1.beacons[owner]? with
          | none =>
              simp only [RegistrationNativePublicFrontend.record, RegistrationNativeExperiment.record,
                RegistrationNativePublicSourceExecution.execute, found,
                RegistrationNativePublicSourceEffects.close, simulateQ_pure,
                StateT.run, map_pure, Prod.map_def, id_eq, restore,
                RegistrationNativePublicSourceState.owners, List.getElem?_map, Option.map_none]
              rfl
          | some owned =>
              have closed := direct_record setup wire route sign seed scalar roots
                (.inr (owned.view.worldOwner, .inl plaintext)) before
              simp only [RegistrationNativePublicFrontend.record, RegistrationNativeExperiment.record,
                RegistrationNativePublicSourceExecution.execute, StateT.run, restore,
                RegistrationNativePublicSourceState.owners, List.getElem?_map, found, Option.map_some,
                RegistrationNativePublicSourceState.owner, RegistrationBeaconReferenceCompiler.restoreOwner] at closed ⊢
              convert closed using 1 <;> rfl
      | inr raw =>
          cases found : before.1.beacons[owner]? with
          | none =>
              simp only [RegistrationNativePublicFrontend.record, RegistrationNativeExperiment.record,
                RegistrationNativePublicSourceExecution.execute, found,
                RegistrationNativePublicSourceEffects.close, simulateQ_pure,
                StateT.run, map_pure, Prod.map_def, id_eq, restore,
                RegistrationNativePublicSourceState.owners, List.getElem?_map, Option.map_none]
              rfl
          | some owned =>
              have closed := direct_record setup wire route sign seed scalar roots
                (.inr (owned.view.worldOwner, .inr raw)) before
              simp only [RegistrationNativePublicFrontend.record, RegistrationNativeExperiment.record,
                RegistrationNativePublicSourceExecution.execute, StateT.run, restore,
                RegistrationNativePublicSourceState.owners, List.getElem?_map, found, Option.map_some,
                RegistrationNativePublicSourceState.owner, RegistrationBeaconReferenceCompiler.restoreOwner] at closed ⊢
              convert closed using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.world_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.effect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceWorld.record_source
