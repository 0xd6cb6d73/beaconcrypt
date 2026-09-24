import BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer
import BeaconcryptCore.Computational.PqxdhServerRootQueryBounds

/-! The complete Server source helper pays one family request, at most three ordinary post-prefix effects, and every earlier callback at its actual source position. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds
open PqxdhServerRelatedRootConsumer PqxdhServerRootPreparation PqxdhServerStaticDhSource
open PqxdhJointIdentity PqxdhJointDhExtractRoot
open PqxdhBeaconPhase2Preparation (Word32)

def isFamily : PqxdhServerRelatedRootConsumer.Spec.Domain → Bool
  | .inl _ => true
  | .inr _ => false

set_option backward.isDefEq.respectTransparency false in
/-- Full root processing has at most one family request and three actual erase/consume callbacks, including every failed branch. -/
theorem client_class {Reader E : Type} (kind : Bool) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : Inputs Reader E PeerEncoding) :
    (client binding input).IsQueryBoundP (fun query => isFamily query = kind) (if kind then 1 else 3) := by
  classical
  cases kind <;> unfold client
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [isFamily])
    | intro answer; cases answer
    | split
  all_goals simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

set_option backward.isDefEq.respectTransparency false in
/-- Every family and ordinary post-prefix implementation pays its complete uniform allowance, on both successful and rejected requests. -/
theorem client_uniform {A Reader E : Type}
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (qFamily qAux : Nat)
    (familyBound : ∀ query state, ((family query).run state).IsTotalQueryBound qFamily)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (input : Inputs Reader E PeerEncoding) (state : State A) :
    ((simulateQ (impl family aux) (client binding input)).run state).IsTotalQueryBound (qFamily + 3 * qAux) := by
  have step (query : PqxdhServerRelatedRootConsumer.Spec.Domain) (before : State A) :
      ((impl family aux query).run before).IsQueryBoundP (fun _ => True)
        (if isFamily query then qFamily else qAux) := by
    cases query <;> simp only [impl, familyImpl, auxImpl, StateT.run, isFamily, Bool.false_eq_true, if_false, if_true, isQueryBoundP_map_iff]
    · exact (familyBound _ _).isQueryBoundP
    · exact (auxBound _ _).isQueryBoundP
  apply (isQueryBoundP_true_iff _ _).mp
  simpa [Fintype.sum_bool, Nat.mul_comm] using
    FinitePartitionQueryBounds.weighted_bound isFamily
      (fun kind => if kind then qFamily else qAux) (fun kind => if kind then 1 else 3)
      (impl family aux) (fun _ => True) (client binding input) (fun kind => client_class kind binding input) step state

set_option backward.isDefEq.respectTransparency false in
/-- The whole raw source helper bills the actual ordered prefix, selected static-call instrumentation, root family service and all clearing/consumption effects. -/
theorem stage_uniform {A Reader E : Type} {joint : Primitives} (domain : PublicDomain joint)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (qPre qVisit qFamily qAux : Nat)
    (preBound : ∀ query state, ((preImpl query).run state).IsTotalQueryBound qPre)
    (visitBound : ∀ input state, ((visit input).run state).IsTotalQueryBound qVisit)
    (familyBound : ∀ query state, ((family query).run state).IsTotalQueryBound qFamily)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) (raw : Pqxdh.Bytes) (state : State A) :
    ((stage domain preImpl visit family aux binding raw).run state).IsTotalQueryBound
      ((21 * qPre + qVisit) + (qFamily + 3 * qAux)) := by
  simp only [stage, StateT.run_bind]
  apply isTotalQueryBound_bind
  · exact (isQueryBoundP_true_iff _ _).mp (PqxdhServerRootQueryBounds.interpreted_bound domain preImpl visit
      (fun _ => True) qPre qVisit (fun query state => (preBound query state).isQueryBoundP)
      (fun input state => (visitBound input state).isQueryBoundP) raw state)
  · rintro ⟨input, final⟩
    cases input with
    | none => trivial
    | some input => exact client_uniform family aux qFamily qAux familyBound auxBound binding input final

end BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.client_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.client_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.stage_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRelatedRootBounds.stage_uniform
