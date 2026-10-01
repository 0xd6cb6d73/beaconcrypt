import BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter

/-! The mixed publication reference reads the same operational fields as the original source and never reads its private source-analysis ghost. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhJointKdfGame PqxdhServerAuthCtxCalls PqxdhServerAuthPublicationGhost
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- The mixed reference's literal pending lookup, marked writer selection and ordinary builder settlement do not read prior ghost contents. -/
theorem build_project (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks) (rest : Residual)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    Prod.map id PqxdhServerAuthPublicationGhost.project <$> (PqxdhServerAuthPublicationReference.build source codec checks rest session payload).run.run state =
      Prod.map id PqxdhServerAuthPublicationGhost.project <$> (PqxdhServerAuthPublicationReference.build source codec checks rest session payload).run.run (PqxdhServerAuthPublicationGhost.project state) := by
  simp only [PqxdhServerAuthPublicationReference.build, OptionT.run_mk, StateT.run, PqxdhServerAuthPublicationGhost.project, flat, game]
  cases state.1.1.pending session with
  | none => rfl
  | some token =>
      simp only []
      split <;> exact build_after session _ state

/-- Every complete reference API route preserves the same public reply and ghost-erased operational state, with identical component requests. -/
theorem route_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.map id PqxdhServerAuthPublicationGhost.project <$>
      (PqxdhServerAuthPublicationReference.route setup codec checks context rest select query).run.run state =
        Prod.map id PqxdhServerAuthPublicationGhost.project <$>
          (PqxdhServerAuthPublicationReference.route setup codec checks context rest select query).run.run
            (PqxdhServerAuthPublicationGhost.project state) := by
  cases query with
  | inl coin => exact PqxdhServerAuthPublicationGhost.route_project setup codec checks context rest select (.inl coin) state
  | inr query =>
      cases query with
      | build session payload => exact build_project setup.source codec checks rest session payload state
      | _ => exact PqxdhServerAuthPublicationGhost.route_project setup codec checks context rest select _ state

/-- The mixed reference's complete designation and sticky-refusal settlement do not read analysis history. -/
theorem handler_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    Prod.map id PqxdhServerAuthPublicationGhost.project <$>
      (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run state =
        Prod.map id PqxdhServerAuthPublicationGhost.project <$>
          (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run
            (PqxdhServerAuthPublicationGhost.project state) := by
  have same := congrArg (Functor.map (PqxdhServerAuthCtxHandler.settle Q j query
    (PqxdhServerAuthPublicationGhost.project state)))
      (route_project setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state)
  simpa only [PqxdhServerAuthPublicationReference.handler, OptionT.run_mk, StateT.run,
    Functor.map_map, settle_project, designated_project, project_idempotent,
    show (PqxdhServerAuthPublicationGhost.project state).2 = state.2 from rfl] using same

/-- The full reference stop wrapper retains identical public replies, operational poststates and monitor coordinates under ghost projection. -/
theorem stopped_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    Prod.map id tracked <$>
      (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j query).run.run state =
        Prod.map id tracked <$>
          (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j query).run.run (tracked state) := by
  have same := congrArg (Functor.map (PqxdhServerAuthCtxStop.observe
    (fun current : Local KemSK => current.1.1.sessions) (fun current => current.1.2.1) query (tracked state)))
      (handler_project setup codec checks context rest Q j query state.1)
  simpa only [PqxdhServerAuthPublicationReference.stopped, PqxdhServerAuthCtxReserve.stopped,
    PqxdhServerAuthCtxStop.stopped, OptionT.run_mk, StateT.run, bind_pure_comp, Functor.map_map,
    observe_project, tracked_idempotent,
    show (tracked state).1 = PqxdhServerAuthPublicationGhost.project state.1 from rfl] using same

/-- The complete adaptive reference program has identical component requests and projected final output from either original or ghost-erased initial state. -/
theorem program_project (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    Prod.map id tracked <$>
      (simulateQ (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j) work).run.run state =
        Prod.map id tracked <$>
          (simulateQ (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j) work).run.run (tracked state) :=
  optional_project tracked tracked_idempotent _ (stopped_project setup codec checks context rest Q j) work state

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.build_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.build_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.route_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.route_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.handler_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.handler_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.stopped_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.stopped_project
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceGhost.program_project
