-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhJointIdentity

/-! One-sided comparison of adaptive source executions and publication-suppressed executions. A guarded real execution discards trajectories at the first selected publication. A complete modified execution may have additional trajectories. Local shared-draw transports, rather than a global event inclusion assumption, establish the comparison; arbitrary related states permit removal of private signing observations while retaining physical protocol state. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination

variable {ι σ τ Result : Type} {spec : OracleSpec ι}

/-- Execute every real source draw, retaining a trajectory only while every selected attempt has the designated failed reply. -/
def guardedRun (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (client : OracleComp spec Result) : σ → ProbComp (Option (Result × σ)) :=
  OracleComp.construct (C := fun _ => σ → ProbComp (Option (Result × σ)))
    (fun value state => pure (some (value, state)))
    (fun query _ next state => do
      let outcome ← (real query).run state
      if allowed query state outcome then next outcome.1 outcome.2 else pure none)
    client

private theorem guardedRun_pure (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (value : Result) (state : σ) :
    guardedRun real allowed (pure value) state = pure (some (value, state)) := rfl

private theorem guardedRun_query_bind (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) (state : σ) :
    guardedRun real allowed (spec.query query >>= next) state = (do
      let outcome ← (real query).run state
      if allowed query state outcome then guardedRun real allowed (next outcome.1) outcome.2 else pure none) := rfl

/-- A successful guarded observation includes its actual terminal physical state. -/
def Observed (event : Result × σ → Prop) (reply : Option (Result × σ)) : Prop :=
  ∃ outcome, reply = some outcome ∧ event outcome

/-- Actual adaptive probability domination follows from per-step shared-draw transports. Every allowed real step has the same reply and a related successor; no equality is required on excluded real branches. -/
theorem adaptive_domination
    (real : QueryImpl spec (StateT σ ProbComp)) (modified : QueryImpl spec (StateT τ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (related : σ → τ → Prop)
    (transport : (query : spec.Domain) → σ → τ → (spec.Range query × σ) → (spec.Range query × τ))
    (marginal : ∀ query source target, related source target →
      transport query source target <$> (real query).run source = (modified query).run target)
    (step : ∀ query source target, related source target →
      ∀ outcome ∈ support ((real query).run source), allowed query source outcome = true →
        outcome.1 = (transport query source target outcome).1 ∧
          related outcome.2 (transport query source target outcome).2)
    (event : Result × σ → Prop) (modifiedEvent : Result × τ → Prop)
    (post : ∀ value source target, related source target → event (value, source) → modifiedEvent (value, target))
    (client : OracleComp spec Result) (source : σ) (target : τ) (initial : related source target) :
    Pr{let reply ← guardedRun real allowed client source}[Observed event reply] ≤
      Pr{let reply ← (simulateQ modified client).run target}[modifiedEvent reply] := by
  classical
  induction client using OracleComp.inductionOn generalizing source target with
  | pure value =>
      by_cases held : event (value, source)
      · have transferred := post value source target initial held
        simp only [guardedRun_pure, simulateQ_pure, StateT.run_pure, prEvent_pure,
          Observed, Option.some.injEq, exists_eq_left', held, transferred, ite_true]
        exact le_rfl
      · simp only [guardedRun_pure, prEvent_pure, Observed, Option.some.injEq,
          exists_eq_left', held, ite_false, zero_le]
  | query_bind query next ih =>
      simp only [guardedRun_query_bind, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [← marginal query source target initial, bind_map_left]
      apply prEvent_bind_mono_of_forall_le_of_support
      intro outcome supported
      by_cases admitted : allowed query source outcome = true
      · simp only [admitted, ite_true]
        obtain ⟨sameReply, successor⟩ := step query source target initial outcome supported admitted
        rw [← sameReply]
        exact ih outcome.1 outcome.2 (transport query source target outcome).2 successor
      · simp [admitted, Observed]

/-- Instrument the real execution with a sticky record of the same branch condition. Every source operation still executes, including operations after an excluded publication. -/
def monitoredRun (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (client : OracleComp spec Result) : σ → Bool → ProbComp ((Result × σ) × Bool) :=
  OracleComp.construct (C := fun _ => σ → Bool → ProbComp ((Result × σ) × Bool))
    (fun value state clean => pure ((value, state), clean))
    (fun query _ next state clean => do
      let outcome ← (real query).run state
      next outcome.1 outcome.2 (clean && allowed query state outcome))
    client

private theorem monitoredRun_pure (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (value : Result) (state : σ) (clean : Bool) :
    monitoredRun real allowed (pure value) state clean = pure ((value, state), clean) := rfl

private theorem monitoredRun_query_bind (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) (state : σ) (clean : Bool) :
    monitoredRun real allowed (spec.query query >>= next) state clean = (do
      let outcome ← (real query).run state
      monitoredRun real allowed (next outcome.1) outcome.2 (clean && allowed query state outcome)) := rfl

/-- Erasing only the sticky analysis bit recovers the complete original adaptive computation. -/
theorem monitoredRun_erasure (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (client : OracleComp spec Result) (source : σ) (clean : Bool) :
    Prod.fst <$> monitoredRun real allowed client source clean = (simulateQ real client).run source := by
  induction client using OracleComp.inductionOn generalizing source clean with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [monitoredRun_query_bind, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      congr 1
      funext outcome
      exact ih outcome.1 outcome.2 _

private theorem monitoredRun_false (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (client : OracleComp spec Result) (source : σ) :
    ∀ outcome ∈ support (monitoredRun real allowed client source false), outcome.2 = false := by
  induction client using OracleComp.inductionOn generalizing source with
  | pure value =>
      intro outcome supported
      simp only [monitoredRun_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      intro outcome supported
      simp only [monitoredRun_query_bind, Bool.false_and, mem_support_bind_iff] at supported
      obtain ⟨middle, _, tail⟩ := supported
      exact ih middle.1 middle.2 outcome tail

/-- Guarding discards exactly the real trajectories marked by the sticky monitor, without changing the mass of any retained terminal observation. -/
theorem guardedRun_probability (real : QueryImpl spec (StateT σ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (client : OracleComp spec Result) (source : σ) (event : Result × σ → Prop) :
    Pr{let reply ← guardedRun real allowed client source}[Observed event reply] =
      Pr{let reply ← monitoredRun real allowed client source true}[reply.2 = true ∧ event reply.1] := by
  classical
  induction client using OracleComp.inductionOn generalizing source with
  | pure value => simp [guardedRun_pure, monitoredRun_pure, Observed]
  | query_bind query next ih =>
      simp only [guardedRun_query_bind, monitoredRun_query_bind, Bool.true_and]
      apply prEvent_bind_congr
      intro outcome
      by_cases admitted : allowed query source outcome = true
      · simp only [admitted, ite_true]
        exact ih outcome.1 outcome.2
      · have rejected : allowed query source outcome = false := Bool.eq_false_iff.mpr admitted
        simp only [rejected, Bool.false_eq_true, ite_false]
        have absent : Pr{let reply ← monitoredRun real allowed (next outcome.1) outcome.2 false}[reply.2 = true ∧ event reply.1] = 0 := by
          apply prEvent_eq_zero_of_forall_mem_support
          intro reply supported
          rw [monitoredRun_false real allowed (next outcome.1) outcome.2 reply supported]
          simp
        simp [Observed, absent]

/-- The sticky monitor measures exactly the allowed real trajectories whose probabilities are dominated by the complete modified execution. -/
theorem monitored_domination
    (real : QueryImpl spec (StateT σ ProbComp)) (modified : QueryImpl spec (StateT τ ProbComp))
    (allowed : (query : spec.Domain) → σ → (spec.Range query × σ) → Bool)
    (related : σ → τ → Prop)
    (transport : (query : spec.Domain) → σ → τ → (spec.Range query × σ) → (spec.Range query × τ))
    (marginal : ∀ query source target, related source target →
      transport query source target <$> (real query).run source = (modified query).run target)
    (step : ∀ query source target, related source target →
      ∀ outcome ∈ support ((real query).run source), allowed query source outcome = true →
        outcome.1 = (transport query source target outcome).1 ∧
          related outcome.2 (transport query source target outcome).2)
    (event : Result × σ → Prop) (modifiedEvent : Result × τ → Prop)
    (post : ∀ value source target, related source target → event (value, source) → modifiedEvent (value, target))
    (client : OracleComp spec Result) (source : σ) (target : τ) (initial : related source target) :
    Pr{let reply ← monitoredRun real allowed client source true}[reply.2 = true ∧ event reply.1] ≤
      Pr{let reply ← (simulateQ modified client).run target}[modifiedEvent reply] := by
  rw [← guardedRun_probability]
  exact adaptive_domination real modified allowed related transport marginal step event modifiedEvent post client
    source target initial

/-- A message that occurred in a bounded attempt list has a first occurrence below the same public attempt budget, even when its later occurrences repeat. -/
theorem first_occurrence {Entry : Type} (attempts : List Entry) (matchesMessage : Entry → Bool)
    (count : Nat) (bounded : attempts.length ≤ count)
    (present : ∃ entry ∈ attempts, matchesMessage entry = true) :
    ∃ (index : Fin count) (entry : Entry), attempts[index.val]? = some entry ∧ matchesMessage entry = true ∧
      ∀ earlier < index.val, ∀ previous, attempts[earlier]? = some previous → matchesMessage previous = false := by
  have within := List.findIdx_lt_length_of_exists present
  refine ⟨⟨attempts.findIdx matchesMessage, by omega⟩, attempts[attempts.findIdx matchesMessage],
    List.getElem?_eq_getElem within, List.findIdx_getElem, ?_⟩
  intro earlier before previous found
  change earlier < attempts.findIdx matchesMessage at before
  have beforeLength : earlier < attempts.length := by omega
  have same : attempts[earlier] = previous :=
    Option.some.inj ((List.getElem?_eq_getElem beforeLength).symm.trans found)
  have rejected := List.not_of_lt_findIdx before
  simpa only [same] using rejected

/-- A bounded family of deterministically selected suppression clients costs a finite sum of their actual success probabilities; it makes no uncharged random guess. -/
theorem finite_selection_bound {Source Target : Type} (count : Nat)
    (original : ProbComp Source) (event : Source → Prop) (selected : Fin count → Source → Prop)
    (cover : ∀ outcome ∈ support original, event outcome → ∃ index, selected index outcome)
    (modified : Fin count → ProbComp Target) (modifiedEvent : Fin count → Target → Prop)
    (dominated : ∀ index, Pr{let outcome ← original}[selected index outcome] ≤
      Pr{let outcome ← modified index}[modifiedEvent index outcome]) :
    Pr{let outcome ← original}[event outcome] ≤
      ∑ index, Pr{let outcome ← modified index}[modifiedEvent index outcome] := by
  calc
    Pr{let outcome ← original}[event outcome] ≤
        Pr{let outcome ← original}[∃ index, selected index outcome] :=
      prEvent_mono_of_support original event _ cover
    _ ≤ ∑ index, Pr{let outcome ← original}[selected index outcome] :=
      prEvent_exists_le original selected
    _ ≤ ∑ index, Pr{let outcome ← modified index}[modifiedEvent index outcome] :=
      Finset.sum_le_sum fun index _ => dominated index

/-- The never-issued-message case can retain its existing A2 reduction, with only the issued-but-unpublished cases charged to the bounded suppression family. -/
theorem finite_or_selection_bound {Source Target : Type} (count : Nat)
    (original : ProbComp Source) (event ordinary : Source → Prop) (selected : Fin count → Source → Prop)
    (cover : ∀ outcome ∈ support original, event outcome → ordinary outcome ∨ ∃ index, selected index outcome)
    (modified : Fin count → ProbComp Target) (modifiedEvent : Fin count → Target → Prop)
    (dominated : ∀ index, Pr{let outcome ← original}[selected index outcome] ≤
      Pr{let outcome ← modified index}[modifiedEvent index outcome]) :
    Pr{let outcome ← original}[event outcome] ≤ Pr{let outcome ← original}[ordinary outcome] +
      ∑ index, Pr{let outcome ← modified index}[modifiedEvent index outcome] := by
  calc
    Pr{let outcome ← original}[event outcome] ≤
        Pr{let outcome ← original}[ordinary outcome ∨ ∃ index, selected index outcome] :=
      prEvent_mono_of_support original event _ cover
    _ ≤ Pr{let outcome ← original}[ordinary outcome] +
        Pr{let outcome ← original}[∃ index, selected index outcome] :=
      prEvent_or_le original ordinary _
    _ ≤ Pr{let outcome ← original}[ordinary outcome] +
        ∑ index, Pr{let outcome ← modified index}[modifiedEvent index outcome] := by
      exact add_le_add le_rfl (finite_selection_bound count original
        (fun outcome => ∃ index, selected index outcome) selected
        (fun _ _ held => held) modified modifiedEvent dominated)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.adaptive_domination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.adaptive_domination

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.monitoredRun_erasure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.monitoredRun_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.guardedRun_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.guardedRun_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.monitored_domination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.monitored_domination

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.first_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.first_occurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.finite_selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.finite_selection_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.finite_or_selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationDomination.finite_or_selection_bound
