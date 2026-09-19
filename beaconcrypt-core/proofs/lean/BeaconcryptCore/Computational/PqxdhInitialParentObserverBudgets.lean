import BeaconcryptCore.Computational.PqxdhInitialParentObserver

/-!
The full pending observer counts its actual callback syntax. Candidate accounting retains the entire initial list and charges every typed initializer input and returned chain, including repeated and failed requests. Uniform work of the source preparation, application, initializer, selector and publication callbacks is supplied separately at each actual callback and every ambient state. Primitive/open/seal/public work is derived from the existing concrete interpreter. No whole-observer budget or evaluated-distribution cost transfer is used.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι}

/-- Every supported full candidate trace retains its complete starting ledger and charges at most three values for each original extended callback. -/
theorem trace_length {Work : Type}
    (handler : QueryImpl (Spec extra I D K X Response Shared) (StateT Work ProbComp))
    (client : OracleComp (Spec extra I D K X Response Shared) Result) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget)
    (state : (Work × List RootOutput) × Bool) (result : Result × ((Work × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ (RawCtxFlaggedQueryTrace.trace handler inputs direct) client).run state)) :
    result.2.1.2.length ≤ state.1.2.length + 3 * budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      simp only [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [RawCtxFlaggedQueryTrace.trace, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, tailSupport⟩ := supported
      have tail := ih reply.1 (budget - 1) (bounded.2 reply.1) _ result tailSupport
      have head := PqxdhInitialParentObserver.inputs_length query
      simp only [List.length_append] at tail
      omega

structure Costs where
  qPre : Nat
  qApplication : Nat
  qInitial : Nat
  qSelector : Nat
  qAux : Nat

def Costs.cap (costs : Costs) : Nat :=
  64 + costs.qPre + costs.qApplication + costs.qInitial + costs.qSelector + costs.qAux

def cost (costs : Costs) : (Spec extra I D K X Response Shared).Domain → Nat
  | .inl query => RawCtxFamilyObservationBudgets.uniformCost (RawCtxFamilyPrimitiveBudgets.liveClass query)
  | .inr (.inl (.inl _)) => costs.qPre
  | .inr (.inl (.inr (.inl _))) => costs.qApplication
  | .inr (.inl (.inr (.inr (.inl _)))) => costs.qInitial
  | .inr (.inl (.inr (.inr (.inr (.inl _))))) => costs.qSelector
  | .inr (.inl (.inr (.inr (.inr (.inr _))))) => costs.qAux
  | .inr (.inr _) => 0

/-- The conservative common callback cap includes every external cost as well as the concrete at-most64 primitive coins. -/
theorem cost_cap (costs : Costs) (query : (Spec extra I D K X Response Shared).Domain) :
    cost costs query ≤ costs.cap := by
  rcases query with query | (query | reply)
  · cases classified : RawCtxFamilyPrimitiveBudgets.liveClass query
    all_goals simp only [cost, classified, RawCtxFamilyObservationBudgets.uniformCost, Costs.cap]
    all_goals omega
  · rcases query with query | (reply | (secrets | (query | query)))
    all_goals simp only [cost, Costs.cap]
    all_goals omega
  · simp only [cost]
    exact Nat.zero_le _

structure ExternalUniform (costs : Costs)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
    (selector : QueryImpl extra (Ambient A N C))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C)) : Prop where
  pre : ∀ query state cache, (pre query state cache).IsTotalQueryBound costs.qPre
  application : ∀ query state cache, (application query state cache).IsTotalQueryBound costs.qApplication
  initial : ∀ query state cache, (initial query state cache).IsTotalQueryBound costs.qInitial
  selector : ∀ query state cache, (selector query state cache).IsTotalQueryBound costs.qSelector
  aux : ∀ query state cache, (aux query state cache).IsTotalQueryBound costs.qAux

/-- Reassociation of the complete source state preserves the literal random-query bill, with no distribution equality involved. -/
theorem flatten_uniform {Value : Type} (work : Ambient A N C Value) (state : State A N C) (budget : Nat) :
    ((flatten work).run state).IsTotalQueryBound budget ↔ (work state.1 state.2).IsTotalQueryBound budget := by
  simp only [flatten, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]

private theorem lift_uniform {Value : Type} (work : Base A Value)
    (state : RawCtxSharedPrimitive.SharedState A × N) (cache : C) (budget : Nat) :
    (PqxdhInitialBeaconAmbient.lift work state cache).IsTotalQueryBound budget ↔
      (work state.1).IsTotalQueryBound budget := by
  simp only [PqxdhInitialBeaconAmbient.lift, IsTotalQueryBound, isQueryBound_map_iff]

section Handler
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (costs : Costs) (external : ExternalUniform costs pre application initial selector aux)

include external in
/-- Each full-interface callback pays the concrete old primitive bill or its own original external computation, including unsuccessful replies. -/
theorem handler_uniform (reader : RawCtxSelectedLiveTrace.Reader)
    (query : (Spec extra I D K X Response Shared).Domain) (state : State A N C) :
    ((PqxdhInitialParentObserver.handler source writer prior entry output pre application initial selector aux reader query).run state).IsTotalQueryBound
      (cost costs query) := by
  rcases query with query | (query | reply)
  · exact (flatten_uniform _ state _).mpr ((lift_uniform _ state.1 state.2 _).mpr
      (RawCtxFamilyObservationBudgets.handler_uniform source writer prior entry output reader
        (RawCtxSelectedParentPrivateRealization.realView source) query state.1.1))
  · rcases query with query | (reply | (secrets | (query | query)))
    all_goals first
      | exact (flatten_uniform _ state _).mpr (external.pre _ _ _)
      | exact (flatten_uniform _ state _).mpr (external.application _ _ _)
      | exact (flatten_uniform _ state _).mpr (external.initial _ _ _)
      | exact (flatten_uniform _ state _).mpr (external.selector _ _ _)
      | exact (flatten_uniform _ state _).mpr (external.aux _ _ _)
  · trivial

include external in
/-- Recording actual candidate values and the sticky direct-read bit adds no uniform query to any original source callback. -/
theorem observed_uniform (reader : RawCtxSelectedLiveTrace.Reader)
    (query : (Spec extra I D K X Response Shared).Domain) (state : (State A N C × List RootOutput) × Bool) :
    ((PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader query).run state).IsTotalQueryBound
      (cost costs query) := by
  simpa only [PqxdhInitialParentObserver.observed, RawCtxFlaggedQueryTrace.trace, StateT.run,
    bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    handler_uniform source writer prior entry output pre application initial selector aux costs external reader query state.1.1

include external in
/-- The complete adaptive observer pays the literal callback count times the displayed callback cap, retaining all state and all failed attempts. -/
theorem complete_uniform (reader : RawCtxSelectedLiveTrace.Reader)
    (client : OracleComp (Spec extra I D K X Response Shared) Result) (budget : Nat)
    (bounded : client.IsTotalQueryBound budget) (state : (State A N C × List RootOutput) × Bool) :
    ((simulateQ (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader) client).run state).IsTotalQueryBound
      (budget * costs.cap) := by
  have partitionBound : ∀ selected : Unit,
      client.IsQueryBoundP (fun _ => () = selected) budget := by
    intro selected
    cases selected
    simpa using bounded.isQueryBoundP
  have bound := FinitePartitionQueryBounds.weighted_bound
    (fun _ : (Spec extra I D K X Response Shared).Domain => ()) (fun _ : Unit => costs.cap) (fun _ : Unit => budget)
    (PqxdhInitialParentObserver.observed source writer prior entry output pre application initial selector aux reader)
    (fun _ => True) client partitionBound
    (fun query state => ((observed_uniform source writer prior entry output pre application initial selector aux costs external reader query state).mono
      (cost_cap costs query)).isQueryBoundP) state
  simpa only [Finset.univ_unique, Finset.sum_singleton, Nat.mul_comm, isQueryBoundP_true_iff] using bound

end Handler
end BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.trace_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.trace_length
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.cost_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.cost_cap
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.flatten_uniform' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.flatten_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.handler_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.observed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.observed_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.complete_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverBudgets.complete_uniform
