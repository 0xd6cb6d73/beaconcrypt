-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
/-! Full closed-source call snapshots project to an executable free-controller journal while the complete private backend remains outside that journal and is preserved in the live state. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (handler mapCall)
variable {Q I S P A : Type} {spec : OracleSpec Q} {source : OracleSpec I}

def associate (before : (S × P) × List (Call spec S)) : (S × List (Call spec S)) × P :=
  ((before.1.1,before.2),before.1.2)

private theorem handler_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : S → A) (implementation : QueryImpl spec (StateT S m))
    (query : spec.Domain) (before : S × List (Call spec A)) :
    (handler observe implementation query).run before =
      (fun result => (result.1,(result.2,before.2 ++ [⟨query,observe before.1,result.1,observe result.2⟩]))) <$>
        (implementation query).run before.1 := rfl

private theorem linked_run
    (frontend : QueryImpl spec (StateT S (OracleComp source))) (backend : QueryImpl source (StateT P ProbComp))
    (query : spec.Domain) (before : S) (privateBefore : P) :
    (QueryImpl.Stateful.link frontend backend query).run (before,privateBefore) =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ backend ((frontend query).run before)).run privateBefore := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  rfl

/-- One real callback retains the same public snapshot journal and complete source-private backend poststate after reassociation. -/
theorem query (frontend : QueryImpl spec (StateT S (OracleComp source))) (backend : QueryImpl source (StateT P ProbComp))
    (request : spec.Domain) (before : (S × P) × List (Call spec S)) :
    Prod.map id associate <$>
      (handler Prod.fst (QueryImpl.Stateful.link frontend backend) request).run before =
      (QueryImpl.Stateful.link (handler id frontend) backend request).run (associate before) := by
  rcases before with ⟨⟨current,privateBefore⟩,calls⟩
  rw [handler_run,linked_run,linked_run]
  simp only [handler_run,simulateQ_map,StateT.run_map,Functor.map_map,Prod.map_def,id_eq,associate]

/-- The complete adaptive source preserves every observed callback and all backend state in the free-controller journal interpretation. -/
theorem program (frontend : QueryImpl spec (StateT S (OracleComp source))) (backend : QueryImpl source (StateT P ProbComp))
    (work : OracleComp spec A) (before : (S × P) × List (Call spec S)) :
    Prod.map id associate <$>
      (simulateQ (handler Prod.fst (QueryImpl.Stateful.link frontend backend)) work).run before =
      (simulateQ (QueryImpl.Stateful.link (handler id frontend) backend) work).run (associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ associate (query frontend backend) work before

def projectFull (before : (S × P) × List (Call spec (S × P))) : (S × List (Call spec S)) × P :=
  ((before.1.1,before.2.map (mapCall Prod.fst)),before.1.2)

/-- The original full private call snapshots have this same exact free source marginal after only their backend snapshots are forgotten. The live backend, public replies and all later calls are preserved. -/
theorem full_program (frontend : QueryImpl spec (StateT S (OracleComp source))) (backend : QueryImpl source (StateT P ProbComp))
    (work : OracleComp spec A) (before : (S × P) × List (Call spec (S × P))) :
    Prod.map id projectFull <$>
      (simulateQ (RegistrationNativeStageTrace.handler (QueryImpl.Stateful.link frontend backend)) work).run before =
      (simulateQ (QueryImpl.Stateful.link (handler id frontend) backend) work).run (projectFull before) := by
  have projected := RegistrationNativeObservedStageTrace.full_project Prod.fst (QueryImpl.Stateful.link frontend backend) work before
  have observed := congrArg (Functor.map (Prod.map id associate)) projected
  rw [program] at observed
  simpa only [Functor.map_map,Prod.map_def,id_eq,projectFull,associate] using observed

end BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.full_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace.full_program
