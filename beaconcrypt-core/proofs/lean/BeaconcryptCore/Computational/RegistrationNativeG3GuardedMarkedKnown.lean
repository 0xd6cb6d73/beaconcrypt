-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorldProgram

/-! The private repeated-role audit leaves the actual guarded known-side result unchanged. Its role history and sticky flag are retained for the bad-event estimate; only their final observation is forgotten when relating that game to the literal materialized known source. This source equation does not supply any probability bound for the flag. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open RegistrationNativeG3AuditedWorld (Spec Seeds seeded)
open RegistrationNativeG3GuardedWorld (step marked)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def forget (before : State n × Bool) : State n := view before.1

noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) : QueryImpl (Spec n) (StateT (State n) ProbComp) :=
  fun query before => Prod.map id view <$> (step setup codec route seeds true query).run before

/-- The actual known-side audit and full role-use history are private bookkeeping for each concrete guarded callback. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (query : (Spec n).Domain) (before : State n × Bool) :
    Prod.map id forget <$> (marked setup codec route seeds true query).run before =
      (normalized setup codec route seeds query).run (forget before) := by
  have actual := RegistrationNativeG3GuardedMaterializedWorldProgram.step_input setup codec route seeds query (seeded seeds before.1)
  simpa only [marked, normalized, StateT.run, forget, Functor.map_map, Prod.map_def, id_eq,
    view, RegistrationNativeG3AuditedInstall.view, seeded] using actual

/-- Full adaptive audit instrumentation keeps the actual known-side result and semantic World under the displayed seed/use observation. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n × Bool) :
    Prod.map id forget <$> (simulateQ (marked setup codec route seeds true) work).run before =
      (simulateQ (normalized setup codec route seeds) work).run (forget before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ forget (query_source setup codec route seeds) work before

private theorem unmarked (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (step setup codec route seeds true) work).run before =
      (simulateQ (normalized setup codec route seeds) work).run (view before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ view
    (RegistrationNativeG3GuardedMaterializedWorldProgram.step_input setup codec route seeds) work before

/-- Erasing only private audit state gives the literal actual guarded known-side output for any adaptive tagged continuation. -/
theorem value_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n) (flag : Bool) :
    Prod.fst <$> (simulateQ (marked setup codec route seeds true) work).run (before, flag) =
      Prod.fst <$> (simulateQ (step setup codec route seeds true) work).run before := by
  have actual := (program_source setup codec route seeds work (before, flag)).trans
    (unmarked setup codec route seeds work before).symm
  have observed := congrArg (fun distribution => Prod.fst <$> distribution) actual
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed

/-- The actual guarded fixed-table World source is the known marked game after only its internal audit state is erased. -/
theorem materialized_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) Value) (before : State n) :
    Prod.fst <$> (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds) work).run before =
      Prod.fst <$> (simulateQ (marked setup codec route seeds true)
        (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false) := by
  have source := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeG3GuardedMaterializedWorldProgram.program_project setup codec route seeds work before)
  simp only [Functor.map_map, Prod.map_def, id_eq] at source
  exact source.trans (value_source setup codec route seeds _ before false).symm

end BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.value_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.value_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.materialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown.materialized_source
