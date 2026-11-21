-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects
/-! Literal ordinary routing is reified through one shared CTX backend, retaining the same stateful writer, source records, produced-frame journal and all private/public poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State produce)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxCacheFrame (replace)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

noncomputable def serverStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    M (State n) Platform (RawCtxServerMixed.SourceSpec.Range query) := fun before =>
  match before.server with
  | none => match query with
      | .inl _ => pure (none, before)
      | .inr _ => pure (.None, before)
  | some server => do
      let result ← (simulateQ (RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve)
        (PqxdhDeploymentNative.logged
          ((MldsaServerRouting.handler PqxdhRefinement.absBytes
            (fun _ => server.sender) route codec.frameRead query).run server.records))).run before.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.serverTag query) result.1.2
        {before with server := some {server with records := result.1.1.2}, primitive := result.2})

noncomputable def beaconStep (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    M (State n) Platform (RawCtxMixedOwner.SourceSpec.Range query) := fun before =>
  match before.owners[owner]? with
  | none => pure (PqxdhDeploymentNative.absent query, before)
  | some phase => do
      let result ← (simulateQ (RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve)
        (PqxdhDeploymentNative.logged
          ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, before.ownerRaw owner⟩))).run before.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
        {before with
          owners := before.owners.set owner result.1.1.2.phase
          ownerRaw := Function.update before.ownerRaw owner result.1.1.2.rawAttempts
          primitive := result.2})

def realize (before : Full (State n) Platform) : State n × Platform :=
  (replace before.2.1 before.1.1, before.1.2)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

theorem server_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (serverStep setup codec reserve route query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.serverStep setup codec reserve route query)).run (realize before) := by
  cases found : before.1.1.server with
  | none =>
    cases query <;> simp only [serverStep, RegistrationNativePlatformOrdinaryWorld.serverStep,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      realize, replace, StateT.run, state_pure_apply, simulateQ_pure, map_pure, Prod.map_def, id_eq, found]
  | some server =>
    let work := PqxdhDeploymentNative.logged
      ((MldsaServerRouting.handler PqxdhRefinement.absBytes
        (fun _ => server.sender) route codec.frameRead query).run server.records)
    have same := RegistrationNativePlatformCtxOrdinaryPrimitives.complete setup codec reserve work
      ((before.1.1.primitive, before.1.2), before.2)
    have mapped := congrArg (fun action => (fun result =>
      (result.1.1.1, (produce (PqxdhDeploymentNative.serverTag query) result.1.2
        { (realize before).1 with server := some {server with records := result.1.1.2}, primitive := result.2.1}, result.2.2))) <$> action) same
    simpa only [serverStep, RegistrationNativePlatformOrdinaryWorld.serverStep,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      work, realize, replace, StateT.run, found, simulateQ_map, state_map_apply,
      state_lift_apply, bind_pure_comp, Functor.map_map, produce,
      RegistrationNativePlatformCtxOrdinaryPrimitives.realize, Prod.map_def, id_eq] using mapped
theorem beacon_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (beaconStep setup codec reserve owner query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.beaconStep setup codec reserve owner query)).run (realize before) := by
  cases found : before.1.1.owners[owner]? with
  | none =>
    simp only [beaconStep, RegistrationNativePlatformOrdinaryWorld.beaconStep,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      realize, replace, StateT.run, state_pure_apply, simulateQ_pure, map_pure, Prod.map_def, id_eq, found]
  | some phase =>
    let work := PqxdhDeploymentNative.logged
      ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, before.1.1.ownerRaw owner⟩)
    have same := RegistrationNativePlatformCtxOrdinaryPrimitives.complete setup codec reserve work
      ((before.1.1.primitive, before.1.2), before.2)
    have mapped := congrArg (fun action => (fun result =>
      (result.1.1.1, (produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
        { (realize before).1 with
          owners := before.1.1.owners.set owner result.1.1.2.phase
          ownerRaw := Function.update before.1.1.ownerRaw owner result.1.1.2.rawAttempts
          primitive := result.2.1}, result.2.2))) <$> action) same
    simpa only [beaconStep, RegistrationNativePlatformOrdinaryWorld.beaconStep,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      work, realize, replace, StateT.run, found, simulateQ_map, state_map_apply,
      state_lift_apply, bind_pure_comp, Functor.map_map, produce,
      RegistrationNativePlatformCtxOrdinaryPrimitives.realize, Prod.map_def, id_eq] using mapped
noncomputable def initializeWorld (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) : M (State n) Platform Unit :=
  fun before => match before.server with
  | some _ => pure ((), before)
  | none => pure ((), {before with server := some (PqxdhRecordLiftWorld.importedServer created)})

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (M (State n) Platform)
  | .inl created => initializeWorld created
  | .inr (.inl query) => privateWork (RegistrationNativePlatformCtxEffects.program query)
  | .inr (.inr (.inl (.inl input))) => serverStep setup codec reserve route (.inl input)
  | .inr (.inr (.inl (.inr raw))) => serverStep setup codec reserve route (.inr raw)
  | .inr (.inr (.inr (owner, .inl plaintext))) => beaconStep setup codec reserve owner (.inl plaintext)
  | .inr (.inr (.inr (owner, .inr raw))) => beaconStep setup codec reserve owner (.inr raw)

noncomputable def guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (M (State n) Platform) :=
  fun query before => match CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => pure (reply, before)
  | none => (handler setup codec reserve route query).run before

theorem initialize_source (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (initializeWorld created)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.liftWorld (PqxdhRecordLiftWorld.initializeServer created))).run (realize before) := by
  cases found : before.1.1.server <;>
    simp only [initializeWorld, RegistrationNativePlatformOrdinaryWorld.liftWorld, PqxdhRecordLiftWorld.initializeServer,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      realize, replace, StateT.run, state_pure_apply, state_lift_apply, simulateQ_pure,
      bind_pure_comp, map_pure, Prod.map_def, id_eq, found]

theorem effects_source (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (privateWork (RegistrationNativePlatformCtxEffects.program query))).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.liftWorld (PqxdhRecordLiftWorld.effects query))).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have source := RegistrationNativePlatformCtxEffects.query query (before.1.1, before.2)
  have mapped := congrArg (fun action => (fun result => (result.1, (result.2, before.1.2))) <$> action) source
  simpa only [RegistrationNativePlatformCtxEffects.implementation, StateT.run,
    RegistrationAgreementNestedState.flatten, RegistrationNativePlatformOrdinaryWorld.liftWorld,
    state_lift_apply, bind_pure_comp, Functor.map_map, realize, RegistrationNativePlatformCtxEffects.realize,
    Prod.map_def, id_eq] using mapped

theorem handler_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (request : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (handler setup codec reserve route request)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.handler setup codec reserve route request)).run (realize before) := by
  rcases request with created | query | query | ⟨owner, query⟩
  · exact initialize_source created before
  · exact effects_source query before
  · cases query with
    | inl input => exact server_source setup codec reserve route (.inl input) before
    | inr input => exact server_source setup codec reserve route (.inr input) before
  · cases query with
    | inl input => exact beacon_source setup codec reserve owner (.inl input) before
    | inr input => exact beacon_source setup codec reserve owner (.inr input) before
theorem guarded_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (request : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (guarded setup codec reserve route request)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route request)).run (realize before) := by
  have cursor : CborRecordWorldCursor.worldShell (replace before.2.1 before.1.1) =
      CborRecordWorldCursor.worldShell before.1.1 := rfl
  cases refused : CborRecordWorldClient.refusal request (CborRecordWorldCursor.worldShell before.1.1) with
  | none =>
    have source := handler_source setup codec reserve route request before
    simpa only [guarded, RegistrationNativePlatformOrdinaryWorld.guarded,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      StateT.run, realize, cursor, refused] using source
  | some reply =>
    simp only [guarded, RegistrationNativePlatformOrdinaryWorld.guarded,
      RegistrationNativePlatformCtxRunner.interpret, RegistrationAgreementNestedState.flatten,
      StateT.run, realize, cursor, refused, state_pure_apply, simulateQ_pure, map_pure, Prod.map_def, id_eq]

/-- The complete actual guarded ordinary World, including all four record routes and stateful failures, executes under one substitutable CTX backend with its exact full native/platform marginal. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) A)
    (before : Full (State n) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (guarded setup codec reserve route) work)).run before =
      (RegistrationAgreementNestedState.flatten
        (simulateQ (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have same := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun request => interpret (guarded setup codec reserve route request))
    (RegistrationAgreementNestedState.implementation (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route))
    realize (guarded_source setup codec reserve route) work before
  rw [RegistrationAgreementNestedState.program] at same
  exact same
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.beacon_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.initialize_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.initialize_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.guarded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.guarded_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryWorld.complete
