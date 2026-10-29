-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentNative
import BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord

/-! Concrete lowering of an actual stateful World client onto its complete local state, cursor, Protocol control and private interpreter. This reassociates the actual state and effects; it does not assume an ideal-world or whole-game relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld
open PqxdhServerAuthExperiment (Codec)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {Reader Response E Secret Index Value Next : Type} {spec : OracleSpec Index}

abbrev State (n : Nat) (E Secret : Type) := ((E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret

noncomputable def lower (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) Value) : StateT (State n E Secret) ProbComp Value := fun before =>
  (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
    CborRawRecordOriginFlatten.interpret service codec route (work.run before.1.1.1) before.1.1.2 before.1.2 before.2

/-- The actual lowered execution retains the exact local, cursor, control and private poststates. -/
theorem lower_run (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) Value) (before : State n E Secret) :
    (lower service codec route work).run before =
      (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
        CborRawRecordOriginFlatten.interpret service codec route (work.run before.1.1.1)
          before.1.1.2 before.1.2 before.2 := rfl

/-- Observing a literal World result leaves the actual cursor, control and private state unchanged. -/
theorem interpret_map (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (observe : Value → Next)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    CborRawRecordOriginFlatten.interpret service codec route (observe <$> work) shell control secret =
      (fun result => (((observe result.1.1.1, result.1.1.2), result.1.2), result.2)) <$>
        CborRawRecordOriginFlatten.interpret service codec route work shell control secret := by
  simp only [CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map]

/-- A lifted World operation preserves the local frontend and thin-service state while retaining all real World poststates. -/
theorem lower_lift (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (before : State n E Secret) :
    (lower service codec route (StateT.lift work)).run before =
      (fun result => (result.1.1.1, (((before.1.1.1, result.1.1.2), result.1.2), result.2))) <$>
        CborRawRecordOriginFlatten.interpret service codec route work before.1.1.2 before.1.2 before.2 := by
  rw [lower_run, StateT.run_lift, bind_pure_comp, interpret_map]
  simp only [Functor.map_map]

/-- Lowering pure work retains the complete reached World state. -/
theorem lower_pure (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (value : Value) :
    lower (E := E) service codec route (pure value) = pure value := by
  apply StateT.ext
  intro before
  change (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
    CborRawRecordOriginFlatten.interpret service codec route
      ((pure value : StateT E (OracleComp (WorldSpec n)) Value).run before.1.1.1) before.1.1.2 before.1.2 before.2 = _
  simp only [StateT.run_pure, CborRawRecordOriginFlatten.interpret_pure, map_pure]

/-- Sequential lowering preserves the actual callback order and the full joint state at the continuation. -/
theorem lower_bind (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) Value) (next : Value → StateT E (OracleComp (WorldSpec n)) Next) :
    lower service codec route (work >>= next) =
      (lower service codec route work >>= fun value => lower service codec route (next value)) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
    CborRawRecordOriginFlatten.interpret service codec route ((work >>= next).run before.1.1.1)
      before.1.1.2 before.1.2 before.2 = _
  simp only [StateT.run_bind, CborRawRecordOriginFlatten.interpret_bind, map_bind]
  change _ = ((lower service codec route work >>= fun value => lower service codec route (next value))).run before
  rw [StateT.run_bind]
  change _ = ((fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
    CborRawRecordOriginFlatten.interpret service codec route (work.run before.1.1.1)
      before.1.1.2 before.1.2 before.2 >>= fun middle => (lower service codec route (next middle.1)).run middle.2)
  rw [bind_map_left]
  rfl

/-- Every adaptive raw continuation lowers through the same concrete per-query interpreter. -/
theorem program_lower (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (implementation : QueryImpl spec (StateT E (OracleComp (WorldSpec n)))) (work : OracleComp spec Value) :
    lower service codec route (simulateQ implementation work) =
      simulateQ (fun query => lower service codec route (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lower_bind]
      congr 1
      funext value
      exact ih value

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.program_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.program_lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.interpret_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.interpret_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld.lower_lift
