-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceStage

/-! The actual reference frontend's replay insertion reconstructs the exact native SDK consumed token and complete poststate. Root values appear only in this private interpretation map; the public frontend retains only Ready references. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceSourceRetain
open RegistrationServerReferenceRoot (Ready atRoot)
open RegistrationServerReferenceRestore (Roots restore)
variable {n : Nat}
abbrev State (n : Nat) := RegistrationServerMaterialFrontend.State × RegistrationServerRootCompiler.Local n

def project (roots : Roots) (before : State n) : RegistrationServerFrontendCompiler.State n :=
  restore roots before.1 before.2

def retain (ready : Ready) : StateT (State n) ProbComp (RustM (Option Nat)) := fun before =>
  match RegistrationServerMaterialFrontend.retain ready before.1 with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, (after, before.2))

/-- Native replay insertion consumes exactly the restored source token before returning the original public handle, including repeated-ID refusals. -/
theorem retain_native (roots : Roots) (ready : Ready) (before : State n)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    Prod.map id (project roots) <$> (retain ready).run before =
      (RegistrationServerNativeSource.retain created (atRoot ready (roots ready.reference))).run (project roots before) := by
  by_cases present : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = true
  · simp only [retain, RegistrationServerMaterialFrontend.retain,
      RegistrationReplaySchedule.consume_replayed (atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed present,
      RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
      RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
      project, restore, RegistrationServerReferenceRestore.sessions,
      RegistrationReplaySchedule.consume_replayed (atRoot ready (roots ready.reference)) before.1.consumed present,
      StateT.run, map_pure]
    rfl
  · have absent : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = false :=
      Bool.eq_false_iff.mpr present
    simp only [retain, RegistrationServerMaterialFrontend.retain,
      RegistrationReplaySchedule.consume_fresh (atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed absent,
      RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
      RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
      project, restore, RegistrationServerReferenceRestore.sessions,
      RegistrationReplaySchedule.consume_fresh (atRoot ready (roots ready.reference)) before.1.consumed absent,
      StateT.run, map_pure, List.length_map]
    simp only [Prod.map_def, id_eq, project, restore, RegistrationServerReferenceRestore.sessions,
      List.map_append, List.map_cons, List.map_nil, Option.map_some]
    rfl

end BeaconcryptCore.Computational.RegistrationServerReferenceSourceRetain

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceRetain.retain_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceRetain.retain_native
