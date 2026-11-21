-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotNeutral
/-! Actual CBOR cursor admission and opaque-slot observation commute. Refused sends retain their real failure and unchanged slot state; every administrative query is forwarded once. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {A : Type}
local notation "Ghost" => RegistrationNativePlatformRecordSlotGhost.State n

private theorem refused_quiet (request : (WorldSpec n).Domain) (before : CborRecordWorldClient.Shell)
    (reply : (WorldSpec n).Range request) (refused : CborRecordWorldClient.refusal request before=some reply) :
    RegistrationNativePlatformRecordSlotNeutral.Quiet request := by
  rcases request with created | ((coin | capability) | record)
  · simp only [CborRecordWorldClient.refusal,reduceCtorEq] at refused
  · trivial
  · cases capability <;> simp_all [CborRecordWorldClient.refusal]
  · trivial

/-- The cursor's actual refusal decision cannot change a slot receipt, and its forwarded replies remain literal. -/
theorem query (request : (WorldSpec n).Domain) (ghost : Ghost) (before : CborRecordWorldClient.Shell) :
    RegistrationNativePlatformRecordSlotGhost.program ((CborRecordWorldClient.handler request).run before) ghost =
      (fun result => ((result.1.1,result.2),result.1.2)) <$>
        (simulateQ CborRecordWorldClient.handler ((RegistrationNativePlatformRecordSlotGhost.handler request).run ghost)).run before := by
  have interpreted :
      (simulateQ CborRecordWorldClient.handler ((RegistrationNativePlatformRecordSlotGhost.handler request).run ghost)).run before =
        (fun result => ((result.1,RegistrationNativePlatformRecordSlotGhost.next request result.1 ghost),result.2)) <$>
          (CborRecordWorldClient.handler request).run before := by
    simp only [RegistrationNativePlatformRecordSlotGhost.handler,StateT.run,simulateQ_map,simulateQ_spec_query]
    change ((fun reply => (reply,RegistrationNativePlatformRecordSlotGhost.next request reply ghost)) <$> CborRecordWorldClient.handler request).run before = _
    rw [StateT.run_map]
    rfl
  rw [interpreted]
  simp only [CborRecordWorldClient.handler,StateT.run]
  cases refused : CborRecordWorldClient.refusal request before with
  | none =>
    simp only [CborRecordWorldClient.forward,RegistrationNativePlatformRecordSlotGhost.program,
      simulateQ_map,StateT.run_map,simulateQ_spec_query,Functor.map_map]
    change ((fun reply => (reply,CborRecordWorldClient.next request reply before)) <$> RegistrationNativePlatformRecordSlotGhost.handler request).run ghost = _
    rw [StateT.run_map]
    simp only [RegistrationNativePlatformRecordSlotGhost.handler,StateT.run,Functor.map_map]
  | some reply =>
    simp only [RegistrationNativePlatformRecordSlotGhost.program,simulateQ_pure,StateT.run_pure,map_pure]
    rw [RegistrationNativePlatformRecordSlotNeutral.next_quiet request (refused_quiet request before reply refused) reply ghost]

/-- Full adaptive cursor admission commutes with the transparent slot observer while preserving every real shell poststate. -/
theorem program (work : OracleComp (WorldSpec n) A) (ghost : Ghost) (before : CborRecordWorldClient.Shell) :
    RegistrationNativePlatformRecordSlotGhost.program ((simulateQ CborRecordWorldClient.handler work).run before) ghost =
      (fun result => ((result.1.1,result.2),result.1.2)) <$>
        (simulateQ CborRecordWorldClient.handler ((simulateQ RegistrationNativePlatformRecordSlotGhost.handler work).run ghost)).run before := by
  let left := QueryImpl.Stateful.link (RegistrationNativePlatformRecordSlotGhost.handler (n := n)) CborRecordWorldClient.handler
  let right := QueryImpl.Stateful.link (CborRecordWorldClient.handler (n := n)) RegistrationNativePlatformRecordSlotGhost.handler
  have step (request : (WorldSpec n).Domain) (state : Ghost × CborRecordWorldClient.Shell) :
      Prod.map id Prod.swap <$> (left request).run state=(right request).run state.swap := by
    have source := QueryImpl.Stateful.simulateQ_link_run RegistrationNativePlatformRecordSlotGhost.handler CborRecordWorldClient.handler
      ((WorldSpec n).query request : OracleComp (WorldSpec n) _) state.1 state.2
    have target := QueryImpl.Stateful.simulateQ_link_run CborRecordWorldClient.handler RegistrationNativePlatformRecordSlotGhost.handler
      ((WorldSpec n).query request : OracleComp (WorldSpec n) _) state.2 state.1
    simp only [simulateQ_spec_query] at source target
    change Prod.map id Prod.swap <$> (QueryImpl.Stateful.link RegistrationNativePlatformRecordSlotGhost.handler CborRecordWorldClient.handler request).run (state.1,state.2) =
      (QueryImpl.Stateful.link CborRecordWorldClient.handler RegistrationNativePlatformRecordSlotGhost.handler request).run (state.2,state.1)
    rw [source,target]
    simp only [QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst,PFunctor.Lens.State.snd]
    change Prod.map id Prod.swap <$> ((fun result : ((WorldSpec n).Range request × Ghost) × CborRecordWorldClient.Shell => (result.1.1,(result.1.2,result.2))) <$> _) =
      (fun result : ((WorldSpec n).Range request × CborRecordWorldClient.Shell) × Ghost => (result.1.1,(result.1.2,result.2))) <$> RegistrationNativePlatformRecordSlotGhost.program _ _
    rw [query request state.1 state.2]
    simp only [Functor.map_map,Prod.map_def,id_eq,Prod.swap]
  have whole := map_run_simulateQ_eq_of_query_map_eq left right Prod.swap step work (ghost,before)
  rw [QueryImpl.Stateful.simulateQ_link_run,QueryImpl.Stateful.simulateQ_link_run] at whole
  simp only [QueryImpl.Stateful.Frame.prod,PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,
    Functor.map_map,Prod.map_def,id_eq,Prod.swap] at whole
  have mapped := congrArg (Functor.map (fun result : A × (CborRecordWorldClient.Shell × Ghost) => ((result.1,result.2.1),result.2.2))) whole
  simpa only [Functor.map_map,RegistrationNativePlatformRecordSlotGhost.program,PFunctor.Lens.State.mk_put,id_map'] using mapped.symm


end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource.program
