import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.Coercions.Add

/-!
# Moving a lazily sampled table below a stack of interpreters (item 2, stage S1b, generic tools)

This module is generic and contains no protocol code. It concerns a program whose top-level handler keeps a table state `C` (in item 2: the cache of the shared zero-key 192-byte Extract table) beside its own state, below which further interpreters run. Stage S1b needs the same program with the table moved to the bottom of the interpreter stack, where it becomes an oracle of the final client: G1's `sharedGame` answers the table reads of its client from a table held by the challenger.

- `tableAt coins op` answers a table interface `T` by a stateful operation `op` on `C` whose uniform coins are lifted into the base interface by `coins`, and forwards every base query unchanged.
- `split_run` (state splitting): if every step of a top-level handler on the joined state `join c g` is the step of a table-free handler on `g` followed by the table at `c`, then so is every program.
- `push_stateless` and `push_option`: a table at the top of a stateless interpreter, or of an optional stateful interpreter, equals the same interpreter with table queries forwarded (`fwd`, `fwdOption`) and the table one level lower, provided the interpreter maps lifted coins to lifted coins (`faithful`). For the optional interpreter the table state of a stopped run is dropped, as the original drops it.

These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

section Tools

variable {ιA ιB ιT : Type} {A : OracleSpec ιA} {B : OracleSpec ιB} {T : OracleSpec ιT} {C : Type}

/-- Forward base queries with the table unchanged. -/
def keep (A : OracleSpec ιA) (C : Type) : QueryImpl A (StateT C (OracleComp A)) :=
  fun query => StateT.mk fun cache => (fun reply => (reply, cache)) <$> (A.query query : OracleComp A _)

/-- Answer the table interface by a stateful table operation whose coins are lifted into the base interface; forward every base query with the table unchanged. -/
def tableAt (coins : ∀ {α : Type}, ProbComp α → OracleComp A α) (op : QueryImpl T (StateT C ProbComp)) :
    QueryImpl (A + T) (StateT C (OracleComp A)) :=
  keep A C + (fun query => StateT.mk fun cache => coins ((op query).run cache) :
    QueryImpl T (StateT C (OracleComp A)))

/-- Forward table queries through a stateless interpreter. -/
def fwd (layer : QueryImpl A (OracleComp B)) : QueryImpl (A + T) (OracleComp (B + T)) :=
  (fun query => OracleComp.liftComp (layer query) (B + T) : QueryImpl A (OracleComp (B + T))) +
    (fun query => ((B + T).query (.inr query) : OracleComp (B + T) _) : QueryImpl T (OracleComp (B + T)))

/-- Forward table queries through an optional stateful interpreter. -/
def fwdOption {J : Type} (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) :
    QueryImpl (A + T) (OptionT (StateT J (OracleComp (B + T)))) :=
  (fun query => OptionT.mk (StateT.mk fun state => OracleComp.liftComp (((layer query).run).run state) (B + T)) :
      QueryImpl A (OptionT (StateT J (OracleComp (B + T))))) +
    (fun query => OptionT.mk (StateT.mk fun state =>
      (fun reply => (some reply, state)) <$> ((B + T).query (.inr query) : OracleComp (B + T) _)) :
      QueryImpl T (OptionT (StateT J (OracleComp (B + T)))))

theorem tableAt_inl (coins : ∀ {α : Type}, ProbComp α → OracleComp A α) (op : QueryImpl T (StateT C ProbComp))
    (query : ιA) (cache : C) :
    (tableAt coins op (.inl query)).run cache = (fun reply => (reply, cache)) <$> (A.query query : OracleComp A _) :=
  rfl

theorem tableAt_inr (coins : ∀ {α : Type}, ProbComp α → OracleComp A α) (op : QueryImpl T (StateT C ProbComp))
    (query : ιT) (cache : C) :
    (tableAt coins op (.inr query)).run cache = coins ((op query).run cache) :=
  rfl

theorem fwd_inl (layer : QueryImpl A (OracleComp B)) (query : ιA) :
    fwd (T := T) layer (.inl query) = OracleComp.liftComp (layer query) (B + T) :=
  rfl

theorem fwd_inr (layer : QueryImpl A (OracleComp B)) (query : ιT) :
    fwd (T := T) layer (.inr query) = ((B + T).query (.inr query) : OracleComp (B + T) _) :=
  rfl

theorem fwdOption_inl {J : Type} (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) (query : ιA)
    (state : J) :
    ((fwdOption (T := T) layer (.inl query)).run).run state =
      OracleComp.liftComp (((layer query).run).run state) (B + T) :=
  rfl

theorem fwdOption_inr {J : Type} (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) (query : ιT)
    (state : J) :
    ((fwdOption (T := T) layer (.inr query)).run).run state =
      (fun reply => (some reply, state)) <$> ((B + T).query (.inr query) : OracleComp (B + T) _) :=
  rfl

/-- Forwarding base queries leaves the table untouched. -/
theorem keep_run {α : Type} (work : OracleComp A α) (cache : C) :
    (simulateQ (keep A C) work).run cache = (fun reply => (reply, cache)) <$> work := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, keep, StateT.run_mk, bind_map_left, ih,
        map_bind]

/-- A lifted base program leaves the table untouched. -/
theorem tableAt_lift (coins : ∀ {α : Type}, ProbComp α → OracleComp A α) (op : QueryImpl T (StateT C ProbComp))
    {α : Type} (work : OracleComp A α) (cache : C) :
    (simulateQ (tableAt coins op) (OracleComp.liftComp work (A + T))).run cache =
      (fun reply => (reply, cache)) <$> work := by
  rw [tableAt, QueryImpl.simulateQ_add_liftComp_left, keep_run]

/-- State splitting. If every step of a handler on the joined state is a table-free step followed by the table, every program is. -/
theorem split_run {ιS : Type} {spec : OracleSpec ιS} {S G : Type}
    (handler : QueryImpl spec (StateT S (OracleComp A))) (free : QueryImpl spec (StateT G (OracleComp (A + T))))
    (table : QueryImpl (A + T) (StateT C (OracleComp A))) (join : C → G → S)
    (step : ∀ query cache state, (handler query).run (join cache state) =
      (fun result : (spec.Range query × G) × C => (result.1.1, join result.2 result.1.2)) <$>
        (simulateQ table ((free query).run state)).run cache)
    {α : Type} (work : OracleComp spec α) (cache : C) (state : G) :
    (simulateQ handler work).run (join cache state) =
      (fun result : (α × G) × C => (result.1.1, join result.2 result.1.2)) <$>
        (simulateQ table ((simulateQ free work).run state)).run cache := by
  induction work using OracleComp.inductionOn generalizing cache state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1.1 result.2 result.1.2

/-- The table moves below a stateless interpreter that maps lifted coins to lifted coins. -/
theorem push_stateless (layer : QueryImpl A (OracleComp B))
    (coinsA : ∀ {α : Type}, ProbComp α → OracleComp A α) (coinsB : ∀ {α : Type}, ProbComp α → OracleComp B α)
    (op : QueryImpl T (StateT C ProbComp))
    (faithful : ∀ {α : Type} (work : ProbComp α), simulateQ layer (coinsA work) = coinsB work)
    {α : Type} (work : OracleComp (A + T) α) (cache : C) :
    simulateQ layer ((simulateQ (tableAt coinsA op) work).run cache) =
      (simulateQ (tableAt coinsB op) (simulateQ (fwd layer) work)).run cache := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rcases query with query | query
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableAt_inl, fwd_inl, tableAt_lift,
          bind_map_left, ih]
        rfl
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableAt_inr, fwd_inr, faithful, ih]

/-- The table moves below an optional stateful interpreter that maps lifted coins to lifted coins without stopping or changing its state. The table state of a stopped run is dropped. -/
theorem push_option {J : Type} (layer : QueryImpl A (OptionT (StateT J (OracleComp B))))
    (coinsA : ∀ {α : Type}, ProbComp α → OracleComp A α) (coinsB : ∀ {α : Type}, ProbComp α → OracleComp B α)
    (op : QueryImpl T (StateT C ProbComp))
    (faithful : ∀ {α : Type} (work : ProbComp α) (state : J),
      ((simulateQ layer (coinsA work)).run).run state = (fun reply => (some reply, state)) <$> coinsB work)
    {α : Type} (work : OracleComp (A + T) α) (state : J) (cache : C) :
    (fun result : (Option α × J) × C => (result.1.1.map (fun value => (value, result.2)), result.1.2)) <$>
        (simulateQ (tableAt coinsB op) (((simulateQ (fwdOption layer) work).run).run state)).run cache =
      ((simulateQ layer ((simulateQ (tableAt coinsA op) work).run cache)).run).run state := by
  induction work using OracleComp.inductionOn generalizing state cache with
  | pure value => simp
  | query_bind query next ih =>
      rcases query with query | query
      · simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
          fwdOption_inl, tableAt_inl, tableAt_lift, bind_map_left, map_bind]
        refine bind_congr fun result => ?_
        rcases result with ⟨_ | reply, after⟩
        · simp
        · simpa using ih reply after cache
      · simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
          fwdOption_inr, tableAt_inr, faithful, bind_map_left, map_bind]
        refine bind_congr fun result => ?_
        simpa using ih result.1 state result.2

end Tools

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_inr' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwd_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwd_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwd_inr' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwd_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwdOption_inl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwdOption_inl

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.keep_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.keep_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_lift' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tableAt_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.split_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.push_stateless' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.push_stateless

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.push_option' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.push_option
