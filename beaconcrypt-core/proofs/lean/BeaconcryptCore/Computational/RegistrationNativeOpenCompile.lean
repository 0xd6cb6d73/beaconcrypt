-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKey

/-! Stateful compilation commutes with closing an independent external probability service when the compiler forwards its actual uniform queries. The service sees only its own state. The theorem derives the whole adaptive program equation from literal callback equations and retains both state coordinates. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenCompile
variable {OldIndex NewIndex ServiceIndex CompilerState ServiceState Value : Type}
variable {old : OracleSpec OldIndex} {target : OracleSpec NewIndex} {service : OracleSpec ServiceIndex}

def liftBase : QueryImpl target (OracleComp (target + service)) := fun query => (target + service).query (.inl query)

def extend (compiler : QueryImpl old (StateT CompilerState (OracleComp target))) :
    QueryImpl (old + service) (StateT CompilerState (OracleComp (target + service)))
  | .inl query => fun before => simulateQ liftBase ((compiler query).run before)
  | .inr query => StateT.lift ((target + service).query (.inr query))

def close (coins : QueryImpl unifSpec (OracleComp target))
    (provider : QueryImpl service (StateT ServiceState ProbComp)) :
    QueryImpl (target + service) (StateT ServiceState (OracleComp target))
  | .inl query => StateT.lift (target.query query)
  | .inr query => fun before => simulateQ coins ((provider query).run before)

private theorem base_program (coins : QueryImpl unifSpec (OracleComp target))
    (provider : QueryImpl service (StateT ServiceState ProbComp))
    (work : OracleComp target Value) (before : ServiceState) :
    (simulateQ (close coins provider) (simulateQ liftBase work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : close coins provider ∘ₛ liftBase =
      (QueryImpl.ofLift target (OracleComp target)).liftTarget (StateT ServiceState (OracleComp target)) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- Forwarding actual coin callbacks suffices to commute an arbitrary probability program with compilation. -/
theorem coin_program (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (oldCoins : QueryImpl unifSpec (OracleComp old)) (newCoins : QueryImpl unifSpec (OracleComp target))
    (forward : ∀ query before, (simulateQ compiler (oldCoins query)).run before =
      (fun reply => (reply, before)) <$> newCoins query)
    (work : ProbComp Value) (before : CompilerState) :
    (simulateQ compiler (simulateQ oldCoins work)).run before =
      (fun value => (value, before)) <$> simulateQ newCoins work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [forward query before, bind_map_left]
      simp only [ih, ← map_bind]

def source (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (oldCoins : QueryImpl unifSpec (OracleComp old))
    (provider : QueryImpl service (StateT ServiceState ProbComp)) :
    QueryImpl (old + service) (StateT (ServiceState × CompilerState) (OracleComp target)) :=
  (compiler.mapStateTBase (close oldCoins provider)).flattenStateT

def reference (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (newCoins : QueryImpl unifSpec (OracleComp target))
    (provider : QueryImpl service (StateT ServiceState ProbComp)) :
    QueryImpl (old + service) (StateT (CompilerState × ServiceState) (OracleComp target)) :=
  ((close newCoins provider).mapStateTBase (extend compiler)).flattenStateT

/-- Independent service closure and the actual stateful compiler commute at every callback, retaining the full two-state outcome. -/
theorem query_swap (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (oldCoins : QueryImpl unifSpec (OracleComp old)) (newCoins : QueryImpl unifSpec (OracleComp target))
    (forward : ∀ query before, (simulateQ compiler (oldCoins query)).run before =
      (fun reply => (reply, before)) <$> newCoins query)
    (provider : QueryImpl service (StateT ServiceState ProbComp))
    (query : (old + service).Domain) (before : ServiceState × CompilerState) :
    Prod.map id Prod.swap <$> (source compiler oldCoins provider query).run before =
      (reference compiler newCoins provider query).run before.swap := by
  rcases before with ⟨external, internal⟩
  simp only [source, reference, Prod.swap_prod_mk, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  cases query with
  | inl query =>
      change Prod.map id Prod.swap <$>
        ((fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ compiler ((fun value => (value, external)) <$> old.query query)).run internal) =
        (fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ (close newCoins provider) (simulateQ liftBase ((compiler query).run internal))).run external
      rw [base_program]
      simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map, Prod.map_def, id_eq]
      rfl
  | inr query =>
      change Prod.map id Prod.swap <$>
        ((fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ compiler (simulateQ oldCoins ((provider query).run external))).run internal) =
        (fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ (close newCoins provider)
            ((fun reply => (reply, internal)) <$> (target + service).query (.inr query))).run external
      rw [coin_program compiler oldCoins newCoins forward]
      rw [simulateQ_map, StateT.run_map]
      simp only [simulateQ_spec_query, close, StateT.run, Functor.map_map, Prod.map_def, id_eq]
      rfl

/-- The derived callback equation commutes the complete adaptive client, including all stateful compiler and service failures. -/
theorem program_swap (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (oldCoins : QueryImpl unifSpec (OracleComp old)) (newCoins : QueryImpl unifSpec (OracleComp target))
    (forward : ∀ query before, (simulateQ compiler (oldCoins query)).run before =
      (fun reply => (reply, before)) <$> newCoins query)
    (provider : QueryImpl service (StateT ServiceState ProbComp))
    (work : OracleComp (old + service) Value) (before : ServiceState × CompilerState) :
    Prod.map id Prod.swap <$> (simulateQ (source compiler oldCoins provider) work).run before =
      (simulateQ (reference compiler newCoins provider) work).run before.swap :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.swap
    (query_swap compiler oldCoins newCoins forward provider) work before

/-- Discarding compiler/service bookkeeping yields the exact order-independent closed value, not a caller-supplied whole-program equivalence. -/
theorem client_swap (compiler : QueryImpl old (StateT CompilerState (OracleComp target)))
    (oldCoins : QueryImpl unifSpec (OracleComp old)) (newCoins : QueryImpl unifSpec (OracleComp target))
    (forward : ∀ query before, (simulateQ compiler (oldCoins query)).run before =
      (fun reply => (reply, before)) <$> newCoins query)
    (provider : QueryImpl service (StateT ServiceState ProbComp))
    (work : OracleComp (old + service) Value) (external : ServiceState) (internal : CompilerState) :
    (simulateQ compiler ((simulateQ (close oldCoins provider) work).run' external)).run' internal =
      (simulateQ (close newCoins provider) ((simulateQ (extend compiler) work).run' internal)).run' external := by
  have whole := program_swap compiler oldCoins newCoins forward provider work (external, internal)
  have observed := congrArg (fun experiment => Prod.fst <$> experiment) whole
  simp only [Functor.map_map, Prod.map_def, id_eq] at observed
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map]
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [source, reference, Functor.map_map, Prod.swap_prod_mk] using observed

end BeaconcryptCore.Computational.RegistrationNativeOpenCompile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenCompile.coin_program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenCompile.coin_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenCompile.query_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenCompile.query_swap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenCompile.program_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenCompile.program_swap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenCompile.client_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenCompile.client_swap
