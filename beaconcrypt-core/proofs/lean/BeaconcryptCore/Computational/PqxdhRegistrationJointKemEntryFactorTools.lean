import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonTools

/-!
# Relabelled value reads and invariant-gated projections (item 2, stage S3b, generic tools)

This module is generic and contains no protocol code. Stage S3b of the item 2 plan compares two instances of one client program: one whose value reads return values of a type `V` (in item 2: uniform 32-byte roots), and one whose value reads return values of a type `W` (in item 2: the 108-byte key-schedule outputs), where the second answer is a function `f` of the first. The tools are:

- `relabel f` answers a value read with values in `W` by a value read with values in `V` followed by `f`, and forwards every other query unchanged. `relabel_liftComp`, `relabel_fwd` and `relabel_fwdOption` show that it commutes with lifting and with the forwarding interpreters `fwd` and `fwdOption` of `PqxdhRegistrationJointKemPostSkeletonTools`, so a relabelling at the bottom of an interpreter stack moves to its top.
- `mapRun` post-composes every step of a stateful handler with an interpreter of its base interface, and `simulateQ_mapRun` shows that this is the interpreter applied to the whole run.
- `map_run_inv` is the invariant-gated state-projection transport (the statement of VCVio's `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'` together with invariant preservation), for handlers over any oracle interface: it uses only the structural support of oracle programs, so it needs no probabilistic semantics of the base interface.
- `support_simulateQ_subset`: an interpreted program has no outputs that the program itself cannot produce.

These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

open PqxdhRegistrationJointKemPostSkeleton (fwd fwdOption)

/-! ### Structural support and invariant-gated projections -/

section Projection

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

/-- Interpreting a program cannot add outputs: every output of the interpreted program is an output of the program for some answers. -/
theorem support_simulateQ_subset {α : Type} (impl : QueryImpl spec (OracleComp spec')) (work : OracleComp spec α) :
    support (simulateQ impl work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      intro result member
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at member
      obtain ⟨reply, -, member⟩ := member
      simp only [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply member⟩

/-- Invariant-gated state projection with invariant preservation, for handlers over any oracle interface. -/
theorem map_run_inv {σ₁ σ₂ α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec'))) (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ query state, inv state → ∀ result ∈ support ((impl₁ query).run state), inv result.2)
    (hproj : ∀ query state, inv state →
      Prod.map id proj <$> (impl₁ query).run state = (impl₂ query).run (proj state))
    (work : OracleComp spec α) (state : σ₁) (holds : inv state) :
    Prod.map id proj <$> (simulateQ impl₁ work).run state = (simulateQ impl₂ work).run (proj state) ∧
      ∀ result ∈ support ((simulateQ impl₁ work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      refine ⟨by simp, ?_⟩
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact holds
  | query_bind query next ih =>
      refine ⟨?_, ?_⟩
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
        rw [← hproj query state holds, bind_map_left]
        exact bind_congr_of_forall_mem_support _ fun step member =>
          (ih step.1 step.2 (hinv query state holds step member)).1
      · intro result member
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
        obtain ⟨step, stepMember, member⟩ := member
        exact (ih step.1 step.2 (hinv query state holds step stepMember)).2 result member

end Projection

/-! ### Post-composing a stateful handler with an interpreter -/

section MapRun

variable {ιS ιA ιB : Type} {spec : OracleSpec ιS} {A : OracleSpec ιA} {B : OracleSpec ιB} {σ : Type}

/-- Every step of a stateful handler, followed by an interpreter of its base interface. -/
def mapRun (interpret : QueryImpl A (OracleComp B)) (impl : QueryImpl spec (StateT σ (OracleComp A))) :
    QueryImpl spec (StateT σ (OracleComp B)) :=
  fun query => StateT.mk fun state => simulateQ interpret ((impl query).run state)

theorem mapRun_run (interpret : QueryImpl A (OracleComp B)) (impl : QueryImpl spec (StateT σ (OracleComp A)))
    (query : spec.Domain) (state : σ) :
    (mapRun interpret impl query).run state = simulateQ interpret ((impl query).run state) := rfl

/-- Interpreting a stateful run is running the post-composed handler. -/
theorem simulateQ_mapRun {α : Type} (interpret : QueryImpl A (OracleComp B))
    (impl : QueryImpl spec (StateT σ (OracleComp A))) (work : OracleComp spec α) (state : σ) :
    simulateQ interpret ((simulateQ impl work).run state) = (simulateQ (mapRun interpret impl) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mapRun_run]
      exact bind_congr fun step => ih step.1 step.2

end MapRun

/-! ### Relabelled value reads -/

section Relabel

variable {ιA ιB ιT : Type} {A : OracleSpec ιA} {B : OracleSpec ιB} {T : OracleSpec ιT} {D V W : Type}

/-- Answer a value read with values in `W` by the value read with values in `V` at the same point, mapped by `f`; every other query is forwarded unchanged. -/
def relabel (f : V → W) : QueryImpl (B + ((D →ₒ W) + T)) (OracleComp (B + ((D →ₒ V) + T))) :=
  (fun query => ((B + ((D →ₒ V) + T)).query (.inl query) : OracleComp (B + ((D →ₒ V) + T)) _) :
      QueryImpl B (OracleComp (B + ((D →ₒ V) + T)))) +
    ((fun point => f <$> ((B + ((D →ₒ V) + T)).query (.inr (.inl point)) : OracleComp (B + ((D →ₒ V) + T)) V) :
        QueryImpl (D →ₒ W) (OracleComp (B + ((D →ₒ V) + T)))) +
      (fun query => ((B + ((D →ₒ V) + T)).query (.inr (.inr query)) : OracleComp (B + ((D →ₒ V) + T)) _) :
        QueryImpl T (OracleComp (B + ((D →ₒ V) + T)))))

theorem relabel_inl (f : V → W) (query : ιB) :
    relabel (B := B) (D := D) (T := T) f (.inl query) =
      ((B + ((D →ₒ V) + T)).query (.inl query) : OracleComp (B + ((D →ₒ V) + T)) _) := rfl

theorem relabel_value (f : V → W) (point : D) :
    relabel (B := B) (D := D) (T := T) f (.inr (.inl point)) =
      f <$> ((B + ((D →ₒ V) + T)).query (.inr (.inl point)) : OracleComp (B + ((D →ₒ V) + T)) V) := rfl

theorem relabel_direct (f : V → W) (query : ιT) :
    relabel (B := B) (D := D) (T := T) f (.inr (.inr query)) =
      ((B + ((D →ₒ V) + T)).query (.inr (.inr query)) : OracleComp (B + ((D →ₒ V) + T)) _) := rfl

/-- A lifted base program is unchanged by relabelling. -/
theorem relabel_liftComp {α : Type} (f : V → W) (work : OracleComp B α) :
    simulateQ (relabel (B := B) (D := D) (T := T) f) (OracleComp.liftComp work (B + ((D →ₒ W) + T))) =
      OracleComp.liftComp work (B + ((D →ₒ V) + T)) := by
  rw [relabel, QueryImpl.simulateQ_add_liftComp_left, OracleComp.liftComp_def]
  rfl

/-- A direct query is unchanged by relabelling. -/
theorem relabel_query_direct (f : V → W) (query : ιT) :
    simulateQ (relabel (B := B) (D := D) (T := T) f)
        ((B + ((D →ₒ W) + T)).query (.inr (.inr query)) : OracleComp (B + ((D →ₒ W) + T)) _) =
      ((B + ((D →ₒ V) + T)).query (.inr (.inr query)) : OracleComp (B + ((D →ₒ V) + T)) _) := by
  rw [simulateQ_spec_query]
  rfl

/-- A value read is relabelled. -/
theorem relabel_query_value (f : V → W) (point : D) :
    simulateQ (relabel (B := B) (D := D) (T := T) f)
        ((B + ((D →ₒ W) + T)).query (.inr (.inl point)) : OracleComp (B + ((D →ₒ W) + T)) W) =
      f <$> ((B + ((D →ₒ V) + T)).query (.inr (.inl point)) : OracleComp (B + ((D →ₒ V) + T)) V) := by
  rw [simulateQ_spec_query]
  rfl

/-- A base query is unchanged by relabelling. -/
theorem relabel_query_base (f : V → W) (query : ιB) :
    simulateQ (relabel (B := B) (D := D) (T := T) f)
        ((B + ((D →ₒ W) + T)).query (.inl query) : OracleComp (B + ((D →ₒ W) + T)) _) =
      ((B + ((D →ₒ V) + T)).query (.inl query) : OracleComp (B + ((D →ₒ V) + T)) _) := by
  rw [simulateQ_spec_query]
  rfl

/-- Relabelling commutes with a stateless forwarding interpreter: relabelling below the interpreter is relabelling above it. -/
theorem relabel_fwd {α : Type} (f : V → W) (layer : QueryImpl A (OracleComp B))
    (work : OracleComp (A + ((D →ₒ W) + T)) α) :
    simulateQ (relabel (B := B) (D := D) (T := T) f) (simulateQ (fwd (T := (D →ₒ W) + T) layer) work) =
      simulateQ (fwd (T := (D →ₒ V) + T) layer) (simulateQ (relabel (B := A) (D := D) (T := T) f) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with query | (point | query)
  · simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inl, relabel_liftComp,
      relabel_inl, simulateQ_spec_query]
  · simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inr,
      relabel_value, simulateQ_map, simulateQ_spec_query]
  · simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inr,
      relabel_direct, simulateQ_spec_query]

/-- Relabelling commutes with an optional stateful forwarding interpreter. -/
theorem relabel_fwdOption {J α : Type} (f : V → W) (layer : QueryImpl A (OptionT (StateT J (OracleComp B))))
    (work : OracleComp (A + ((D →ₒ W) + T)) α) (state : J) :
    simulateQ (relabel (B := B) (D := D) (T := T) f)
        (((simulateQ (fwdOption (T := (D →ₒ W) + T) layer) work).run).run state) =
      ((simulateQ (fwdOption (T := (D →ₒ V) + T) layer)
        (simulateQ (relabel (B := A) (D := D) (T := T) f) work)).run).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      rcases query with query | (point | query)
      · simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
          PqxdhRegistrationJointKemPostSkeleton.fwdOption_inl, relabel_inl, relabel_liftComp]
        refine bind_congr fun result => ?_
        rcases result with ⟨_ | reply, after⟩
        · simp
        · simpa using ih reply after
      · simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
          PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr, relabel_value, bind_map_left]
        rw [PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr]
        simp only [bind_map_left, Option.elim_some]
        refine bind_congr fun reply => ?_
        exact ih (f reply) state
      · simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
          PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr, relabel_direct, bind_map_left]
        refine bind_congr fun reply => ?_
        simpa using ih reply state

end Relabel

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.support_simulateQ_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.support_simulateQ_subset

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.map_run_inv' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.map_run_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapRun_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapRun_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_value' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_direct' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_direct

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_liftComp' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_liftComp

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_direct' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_direct

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_value' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_base' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_query_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_fwd' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_fwd

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_fwdOption' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabel_fwdOption
