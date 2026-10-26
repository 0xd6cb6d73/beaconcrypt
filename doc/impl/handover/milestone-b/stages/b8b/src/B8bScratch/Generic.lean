import BeaconcryptCore.Computational.PqxdhServerAuthExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule
import VCVio.ProgramLogic.Relational.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-! ## Generic simulation lemmas: couplings until a bad event and eager sampling -/

section Generic
variable {ι : Type} {spec : OracleSpec ι}

set_option linter.deprecated false in
/-- Two continuations with equal output distributions on the support of a common first computation give equal output distributions after it. -/
theorem evalSPMF_bind_congr_support {α β : Type} (first : ProbComp α) (left right : α → ProbComp β)
    (same : ∀ value ∈ support first, 𝒮[left value] = 𝒮[right value]) :
    𝒮[first >>= left] = 𝒮[first >>= right] := by
  apply evalSPMF_eq_of_relTriple_eqRel
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support first)
    (relTriple_refl_of_mem_support first fun value member => ⟨rfl, member⟩) fun a b related => ?_
  obtain ⟨rfl, member⟩ := related
  exact relTriple_eqRel_of_evalSPMF_eq (same a member)

/-- Two images of one computation are coupled by any relation that holds between the two images of each supported value. -/
theorem relTriple_map_same {α β γ : Type} (work : ProbComp α) (left : α → β) (right : α → γ)
    (relation : β → γ → Prop) (related : ∀ value ∈ support work, relation (left value) (right value)) :
    RelTriple (left <$> work) (right <$> work) relation := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support work)
    (relTriple_refl_of_mem_support work fun value member => ⟨rfl, member⟩) fun a b same => ?_
  obtain ⟨rfl, member⟩ := same
  exact relTriple_pure_pure (related a member)

set_option linter.deprecated false in
/-- Two support properties combine into a coupling of any two computations (the product coupling; the same statement as VCVio's `relTriple_prod`, whose module is not built in this workspace). -/
theorem relTriple_support {α β : Type} (left : ProbComp α) (right : ProbComp β) (first : α → Prop)
    (second : β → Prop) (leftHolds : ∀ value ∈ support left, first value)
    (rightHolds : ∀ value ∈ support right, second value) :
    RelTriple left right (fun a b => first a ∧ second b) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost]
  have leftMass : (𝒮[left]).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := left)
  have rightMass : (𝒮[right]).toPMF none = 0 := by
    simpa only [← SPMF.run_eq_toPMF, probFailure_def] using probFailure_eq_zero (mx := right)
  refine ⟨_root_.SPMF.Coupling.prod leftMass rightMass, ?_⟩
  intro pair member
  rcases (mem_spmf_support_bind_iff (𝒮[left])
    (fun a => 𝒮[right] >>= fun b => (pure (a, b) : SPMF (α × β))) pair).1 member with ⟨a, aMember, rest⟩
  have aSupport : a ∈ support left :=
    (mem_support_iff_evalSPMF_apply_ne_zero left a).2 ((SPMF.mem_support_iff _ _).1 aMember)
  rcases (mem_spmf_support_bind_iff (𝒮[right]) (fun b => (pure (a, b) : SPMF (α × β))) pair).1 rest with
    ⟨b, bMember, last⟩
  have bSupport : b ∈ support right :=
    (mem_support_iff_evalSPMF_apply_ne_zero right b).2 ((SPMF.mem_support_iff _ _).1 bMember)
  obtain rfl : pair = (a, b) := by simpa using last
  exact ⟨leftHolds a aSupport, rightHolds b bSupport⟩

/-- The coupling postcondition of an identical-until-bad argument: equal answers with related states, or both runs bad. -/
def UntilBad {α σ₁ σ₂ : Type} (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (left : α × σ₁) (right : α × σ₂) : Prop :=
  (left.1 = right.1 ∧ related left.2 right.2) ∨ (bad₁ left.2 ∧ bad₂ right.2)

/-- A bad predicate that every step keeps holds on every final state of a simulation that starts bad. -/
theorem support_run_bad {α σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (keeps : ∀ query state, bad state → ∀ result ∈ support ((impl query).run state), bad result.2)
    (work : OracleComp spec α) (state : σ) (start : bad state) :
    ∀ result ∈ support ((simulateQ impl work).run state), bad result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact start
  | query_bind query next ih =>
      intro result member
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      exact ih step.1 step.2 (keeps query state start step stepMember) result member

/-- Identical until bad, as a coupling of two stateful simulations of the same program: if from related states every query is coupled so that the answers agree and the states stay related, or both runs become bad, and bad states are kept by both handlers, then the whole simulations are coupled in the same way. -/
theorem relTriple_until_bad {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (keeps₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (keeps₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilBad related bad₁ bad₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂)
    (start : related state₁ state₂ ∨ (bad₁ state₁ ∧ bad₂ state₂)) :
    RelTriple ((simulateQ impl₁ work).run state₁) ((simulateQ impl₂ work).run state₂)
      (UntilBad related bad₁ bad₂) := by
  have bothBad : ∀ (left right : OracleComp spec α) (first : σ₁) (second : σ₂), bad₁ first → bad₂ second →
      RelTriple ((simulateQ impl₁ left).run first) ((simulateQ impl₂ right).run second)
        (UntilBad related bad₁ bad₂) := fun left right first second firstBad secondBad =>
    relTriple_post_mono (relTriple_support _ _ _ _ (support_run_bad impl₁ bad₁ keeps₁ left first firstBad)
      (support_run_bad impl₂ bad₂ keeps₂ right second secondBad)) fun _ _ both => Or.inr both
  rcases start with start | start
  swap
  · exact bothBad work work state₁ state₂ start.1 start.2
  induction work using OracleComp.inductionOn generalizing state₁ state₂ with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, start⟩)
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine relTriple_bind (step query state₁ state₂ start) fun left right post => ?_
      rcases post with ⟨same, rel⟩ | ⟨leftBad, rightBad⟩
      · rw [same]
        exact ih right.1 left.2 right.2 rel
      · exact bothBad _ _ left.2 right.2 leftBad rightBad

set_option linter.deprecated false in
/-- Transport of an event through an identical-until-bad coupling: an event of the first run that excludes the first bad predicate, and that implies an event of the second run on related final states with equal outputs, has at most the probability of the second event. -/
theorem probEvent_le_until_bad {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (keeps₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (keeps₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilBad related bad₁ bad₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂) (start : related state₁ state₂)
    (event₁ : α × σ₁ → Prop) (event₂ : α × σ₂ → Prop)
    (excludes : ∀ result, event₁ result → ¬ bad₁ result.2)
    (implies : ∀ left right, left.1 = right.1 → related left.2 right.2 → event₁ left → event₂ right) :
    Pr[event₁ | (simulateQ impl₁ work).run state₁] ≤ Pr[event₂ | (simulateQ impl₂ work).run state₂] :=
  probEvent_le_of_relTriple
    (relTriple_until_bad impl₁ impl₂ related bad₁ bad₂ keeps₁ keeps₂ step work state₁ state₂ (Or.inl start))
    fun left right post holds => by
      rcases post with ⟨same, rel⟩ | ⟨leftBad, _⟩
      · exact implies left right same rel holds
      · exact absurd leftBad (excludes left holds)

/-- Once the eager value has been consumed, the eager and lazy handlers agree on every simulation. -/
theorem done_run {α σ V : Type} (lazy : QueryImpl spec (StateT σ ProbComp))
    (eager : V → QueryImpl spec (StateT σ ProbComp)) (done : σ → Prop)
    (doneStep : ∀ query state, done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∧
        ∀ result ∈ support ((lazy query).run state), done result.2)
    (work : OracleComp spec α) (state : σ) (finished : done state) (value : V) :
    (simulateQ (eager value) work).run state = (simulateQ lazy work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rw [(doneStep query state finished).1 value]
      exact OracleComp.bind_congr_of_forall_mem_support _ fun step member =>
        ih step.1 step.2 ((doneStep query state finished).2 step member)

set_option linter.deprecated false in
/-- Eager sampling of one value: a lazy handler that, at a single designated step, samples a value and runs the eager step with it has the output distribution of sampling the value first and running the eager handler throughout. At every other step the eager handler does not use its value, and after the designated step (`done`) it never does again. -/
theorem eager_run {α σ V : Type} (sampler : ProbComp V) (lazy : QueryImpl spec (StateT σ ProbComp))
    (eager : V → QueryImpl spec (StateT σ ProbComp)) (done : σ → Prop)
    (doneStep : ∀ query state, done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∧
        ∀ result ∈ support ((lazy query).run state), done result.2)
    (freshStep : ∀ query state, ¬ done state →
      (∀ value, (eager value query).run state = (lazy query).run state) ∨
        (𝒮[(lazy query).run state] = 𝒮[do let value ← sampler; (eager value query).run state] ∧
          ∀ value, ∀ result ∈ support ((eager value query).run state), done result.2))
    (work : OracleComp spec α) (state : σ) :
    𝒮[(simulateQ lazy work).run state] = 𝒮[do let value ← sampler; (simulateQ (eager value) work).run state] := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (DeferredSampling.evalSPMF_bind_const_neverFails sampler (probFailure_eq_zero) _).symm
  | query_bind query next ih =>
      by_cases finished : done state
      · have same : ∀ value, (simulateQ (eager value) (liftM (spec.query query) >>= next)).run state =
            (simulateQ lazy (liftM (spec.query query) >>= next)).run state := fun value =>
          done_run lazy eager done doneStep _ state finished value
        simp only [same]
        exact (DeferredSampling.evalSPMF_bind_const_neverFails sampler (probFailure_eq_zero) _).symm
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      rcases freshStep query state finished with independent | ⟨designated, consumed⟩
      · simp only [independent]
        rw [DeferredSampling.evalSPMF_bind_comm]
        exact DeferredSampling.evalSPMF_bind_congr_left _ _ _ fun step => ih step.1 step.2
      · have after : ∀ value, (eager value query).run state >>= (fun step =>
            (simulateQ (eager value) (next step.1)).run step.2) =
            (eager value query).run state >>= (fun step => (simulateQ lazy (next step.1)).run step.2) :=
          fun value => OracleComp.bind_congr_of_forall_mem_support _ fun step member =>
            done_run lazy eager done doneStep _ step.2 (consumed value step member) value
        simp only [after]
        rw [show (sampler >>= fun value => (eager value query).run state >>= fun step =>
            (simulateQ lazy (next step.1)).run step.2) =
            ((sampler >>= fun value => (eager value query).run state) >>= fun step =>
              (simulateQ lazy (next step.1)).run step.2) from (bind_assoc _ _ _).symm]
        rw [evalSPMF_bind, evalSPMF_bind, designated]

end Generic

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
