-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorld

/-! The actual fixed-table World interpreter and the known materialized Tag program have the same complete adaptive source law under the full seed/use view, from the same initial World. Tag audits are derived private bookkeeping; their concrete known callbacks do not read the erased coordinates. This projection does not give a probability bound for repeated roles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftWorld (State)
open RegistrationNativeG3AuditedWorld (Spec Seeds step)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

private theorem audit_forget (role : PqxdhRecordLiftInterface.Role) (slot : PqxdhRecordLiftInterface.Slot n)
    (result : Bool × State n) :
    Prod.map id view (RegistrationNativeG3AuditedInstall.audit role slot result) = Prod.map id view result := by
  apply Prod.ext
  · exact (RegistrationNativeG3AuditedInstall.audit_fields role slot result).1
  · exact (RegistrationNativeG3AuditedInstall.audit_fields role slot result).2

private theorem audit_map (role : PqxdhRecordLiftInterface.Role) (slot : PqxdhRecordLiftInterface.Slot n) :
    (fun result => Prod.map id view (RegistrationNativeG3AuditedInstall.audit role slot result)) = Prod.map id view :=
  funext (audit_forget role slot)

/-- Every actual known Tag callback ignores the erased private seed/use coordinates while retaining its complete native result and World fields. -/
theorem step_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain) (before : State n) :
    Prod.map id view <$> (step setup codec route seeds true query).run before =
      Prod.map id view <$> (step setup codec route seeds true query).run (view before) := by
  cases query with
  | ordinary query allowed => exact RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route query allowed before
  | server keyId binding slot =>
      have actual := RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route
        (.inr (.inl (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot))))))) (by exact id) before
      simpa only [step, ite_true, StateT.run, Functor.map_map, Function.comp_def, audit_map,
        PqxdhRecordLiftWorld.handler] using actual
  | beacon owner shell slot =>
      have actual := RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route
        (.inr (.inl (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot))))))) (by exact id) before
      simpa only [step, ite_true, StateT.run, Functor.map_map, Function.comp_def, audit_map,
        PqxdhRecordLiftWorld.handler] using actual

private noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) : QueryImpl (Spec n) (StateT (State n) ProbComp) :=
  fun query before => Prod.map id view <$> (step setup codec route seeds true query).run before

private theorem tag_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (work : OracleComp (Spec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (step setup codec route seeds true) work).run before =
      (simulateQ (normalized setup codec route seeds) work).run (view before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ view (step_input setup codec route seeds) work before

/-- Arbitrary adaptive known Tag programs preserve the same semantic result when their full seed/use input view is applied first. -/
theorem tag_program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (work : OracleComp (Spec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (step setup codec route seeds true) work).run before =
      Prod.map id view <$> (simulateQ (step setup codec route seeds true) work).run (view before) := by
  have first := tag_normalized setup codec route seeds work before
  have second := tag_normalized setup codec route seeds work (view before)
  exact first.trans second.symm

private noncomputable def materialized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  normalized setup codec route seeds ∘ₛ RegistrationNativeG3Materialize.materialize

private theorem source_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (RegistrationNativeG3MaterializedWorld.source setup codec route seeds) work).run before =
      (simulateQ (materialized setup codec route seeds) work).run (view before) := by
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query current
  have actual := RegistrationNativeG3MaterializedWorld.query_project setup codec route seeds query current
  have tagged := tag_normalized setup codec route seeds (RegistrationNativeG3Materialize.materialize query) (view current)
  exact actual.trans tagged

/-- The entire actual fixed-table World program equals its materialized known Tag interpretation from the same initial World under the full seed/use projection. -/
theorem program_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id view <$> (simulateQ (RegistrationNativeG3MaterializedWorld.source setup codec route seeds) work).run before =
      Prod.map id view <$>
        (simulateQ (step setup codec route seeds true) (simulateQ RegistrationNativeG3Materialize.materialize work)).run before := by
  rw [source_normalized, tag_normalized, ← QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.step_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.step_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.tag_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.tag_program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorldProgram.program_project
