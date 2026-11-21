-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldGuarded
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySendGate (liftState)
variable {I KemSK Reader Response Platform E A B : Type} {base : OracleSpec I}
private theorem run_lift (work : StateT Primitive ProbComp A) (before : Primitive) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl
private theorem lift_pure (value : A) :
    liftState (S := Primitive) (Platform := Platform) (pure value : StateT Primitive ProbComp A) = pure value := by
  ext before previous
  simp only [run_lift, StateT.run_lift, StateT.run_pure, pure_bind]
private theorem lift_bind (work : StateT Primitive ProbComp A) (next : A → StateT Primitive ProbComp B) :
    liftState (Platform := Platform) (work >>= next) = (liftState work >>= fun value => liftState (next value)) := by
  ext before previous
  simp only [StateT.run_bind, run_lift, StateT.run_lift, bind_assoc, pure_bind]

theorem no_writer (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A)
    (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .writer) 0) :
    simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve) work =
      liftState (simulateQ (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec)) work) := by
  have allowed : work.AllQueriesSatisfy (fun query => RawCtxMixedOwner.callKind query ≠ .writer) :=
    (isQueryBoundP_zero_iff work _).mp (by simpa only [not_not] using bounded)
  clear bounded
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lift_pure]
  | query_bind query next ih =>
      obtain ⟨localAllowed, rest⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      have leaf : RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve query =
          liftState (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec) query) := by
        rcases query with request | (input | (input | (bytes | frame)))
        all_goals first | rfl | exact False.elim (localAllowed rfl)
      simp only [simulateQ_bind, simulateQ_spec_query, leaf, lift_bind]
      apply bind_congr
      intro reply
      exact ih reply (rest reply)

private theorem lift_map (f : A → B) (work : ProbComp A) :
    (StateT.lift (f <$> work) : StateT Platform ProbComp B) = f <$> StateT.lift work := by
  ext previous
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]

private theorem outer_pure {V : Type} (value : V) :
    (StateT.lift (pure value : ProbComp V) : StateT Platform ProbComp V) = pure value := by
  funext previous
  change (pure value >>= fun result => pure (result, previous) : ProbComp _) = pure (value, previous)
  exact pure_bind _ _

variable {n : Nat}
theorem beacon (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (owner : Nat) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.beaconStep (n := n) setup codec reserve owner (.inr raw) =
      RegistrationNativePlatformOrdinaryWorld.liftWorld
        (PqxdhRecordLiftWorld.beaconStep setup (CborRawCanonicalBuild.canonical codec) owner (.inr raw)) := by
  funext before
  cases found : before.owners[owner]? with
  | none =>
      simp only [RegistrationNativePlatformOrdinaryWorld.beaconStep, PqxdhRecordLiftWorld.beaconStep,
        RegistrationNativePlatformOrdinaryWorld.liftWorld, found, StateT.run, outer_pure]
  | some phase =>
      let work := ((PqxdhRecordLiftBeacon.handler codec.frameRead (.inr raw)).run ⟨phase, before.ownerRaw owner⟩)
      have bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .writer) 0 :=
        PqxdhRecordLiftBeacon.handler_bound codec.frameRead (.inr raw) _ .writer
      have same := congrFun (no_writer setup codec reserve (PqxdhDeploymentNative.logged work)
        (PqxdhDeploymentCompileBudget.logged_bound _ work 0 [] bounded)) before.primitive
      simp only [RegistrationNativePlatformOrdinaryWorld.beaconStep, PqxdhRecordLiftWorld.beaconStep,
        RegistrationNativePlatformOrdinaryWorld.liftWorld, found, StateT.run, bind_pure_comp]
      change (fun result => _) <$> ((simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (PqxdhDeploymentNative.logged work)).run before.primitive) = StateT.lift ((fun result => _) <$>
          ((simulateQ (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))
            (PqxdhDeploymentNative.logged work)).run before.primitive))
      exact (congrArg (Functor.map _) same).trans (lift_map _ _).symm

theorem server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.serverStep (n := n) setup codec reserve route (.inr raw) =
      RegistrationNativePlatformOrdinaryWorld.liftWorld
        (PqxdhRecordLiftWorld.serverStep setup (CborRawCanonicalBuild.canonical codec) route (.inr raw)) := by
  funext before
  cases found : before.server with
  | none =>
      simp only [RegistrationNativePlatformOrdinaryWorld.serverStep, PqxdhRecordLiftWorld.serverStep,
        RegistrationNativePlatformOrdinaryWorld.liftWorld, found, StateT.run, outer_pure]
  | some server =>
      let work := ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _ => server.sender)
        route codec.frameRead (.inr raw)).run server.records)
      have bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .writer) 0 :=
        MldsaServerRouting.raw_bound PqxdhRefinement.absBytes route codec.frameRead raw server.records .writer
      have same := congrFun (no_writer setup codec reserve (PqxdhDeploymentNative.logged work)
        (PqxdhDeploymentCompileBudget.logged_bound _ work 0 [] bounded)) before.primitive
      simp only [RegistrationNativePlatformOrdinaryWorld.serverStep, PqxdhRecordLiftWorld.serverStep,
        RegistrationNativePlatformOrdinaryWorld.liftWorld, found, StateT.run, bind_pure_comp]
      change (fun result => _) <$> ((simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (PqxdhDeploymentNative.logged work)).run before.primitive) = StateT.lift ((fun result => _) <$>
          ((simulateQ (PqxdhRecordLiftWorld.primitives setup (CborRawCanonicalBuild.canonical codec))
            (PqxdhDeploymentNative.logged work)).run before.primitive))
      exact (congrArg (Functor.map _) same).trans (lift_map _ _).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.no_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.no_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive.server
