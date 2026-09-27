import BeaconcryptCore.Computational.RawCtxSelectedSendEvents

/-!
The ordinary native interpreter retains the same private audit without an outer compiler stop. Its operational connection to the existing optional observer preserves every source reply and both full states. Concrete source consumers use this form to transport source-event provenance through the original family frontend.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceEventRecorder
open RawCtxSelectedDriverAudit
variable {ι Owner State Result : Type} {base : OracleSpec ι}

def record (source : QueryImpl base (StateT State ProbComp)) :
    QueryImpl (base + Audit Owner) (StateT (List (Event Owner) × State) ProbComp) :=
  fun query state => match query with
  | .inl request => (fun result => (result.1, (state.1, result.2))) <$> (source request).run state.2
  | .inr event => pure ((), (state.1 ++ [event], state.2))

def lifted (source : QueryImpl base (StateT State ProbComp)) :
    QueryImpl base (OptionT (StateT State ProbComp)) := fun query => monadLift (source query)

/-- The ordinary recorder and optional source observer retain identical replies and full audit/primitive state; native optional values remain inside the outer success. -/
theorem query (source : QueryImpl base (StateT State ProbComp))
    (request : (base + Audit Owner).Domain) (history : List (Event Owner)) (state : State) :
    ((observed (lifted source) request).run).run (history, state) =
      (fun result => (some result.1, result.2)) <$> (record source request).run (history, state) := by
  cases request with
  | inl request =>
      simp only [observed, lifted, OptionT.run_mk, OptionT.run_monadLift, monadLift_self]
      change (fun reply => (reply.1, (history, reply.2))) <$> (some <$> source request).run state =
        (fun result => (some result.1, result.2)) <$>
          ((fun result => (result.1, (history, result.2))) <$> (source request).run state)
      simp only [StateT.run_map, Functor.map_map]
  | inr event => rfl

/-- Every adaptive source program retains exactly the same optional output, audit list and private poststate in both interpreters. -/
theorem program (source : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (base + Audit Owner) Result) (history : List (Event Owner)) (state : State) :
    ((simulateQ (observed (lifted source)) work).run).run (history, state) =
      (fun result => (some result.1, result.2)) <$> (simulateQ (record source) work).run (history, state) := by
  induction work using OracleComp.inductionOn generalizing history state with
  | pure value => rfl
  | query_bind request continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, map_bind]
      rw [query, bind_map_left]
      simp only [Option.elim_some]
      exact bind_congr fun result => ih result.1 result.2.1 result.2.2

def seals (history : List (Event Owner)) : List (RawCtxSelectedSendTrace.Occurrence Owner) :=
  history.filterMap fun event => match event with
  | .derived _ _ _ _ _ => none
  | .sealing occurrence => some occurrence

/-- Filtering the audit retains every seal occurrence, including repeated equal entries. -/
theorem mem_seals (history : List (Event Owner)) (occurrence : RawCtxSelectedSendTrace.Occurrence Owner) :
    occurrence ∈ seals history ↔ Event.sealing occurrence ∈ history := by
  induction history with
  | nil => simp [seals]
  | cons event history ih => cases event <;> simp_all [seals]

def IsSeal : (base + Audit Owner).Domain → Prop
  | .inl _ => False
  | .inr (.derived _ _ _ _ _) => False
  | .inr (.sealing _) => True

instance : DecidablePred (IsSeal (base := base) (Owner := Owner)) :=
  fun query => match query with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr (.derived _ _ _ _ _) => inferInstanceAs (Decidable False)
  | .inr (.sealing _) => inferInstanceAs (Decidable True)

/-- Forwarding any original source program emits no private seal event; its original source queries remain present. -/
theorem source_queries (work : OracleComp base Result) :
    IsQueryBoundP (simulateQ (fun query => (base + Audit Owner).query (.inl query) : QueryImpl base (OracleComp (base + Audit Owner))) work)
      (IsSeal (base := base)) 0 := by
  exact (isQueryBoundP_false work 0).simulateQ_of_step
    (fun _ impossible => False.elim impossible)
    (fun query _ => (isQueryBoundP_query_iff (spec := base + Audit Owner) (p := IsSeal (base := base)) (.inl query) 0).mpr
      (by simp [IsSeal]))

/-- An original source query or private derivation event cannot add, delete or reorder a recorded send occurrence, irrespective of its complete primitive reply. -/
theorem nonseal_query (source : QueryImpl base (StateT State ProbComp))
    (request : (base + Audit Owner).Domain) (quiet : ¬ IsSeal (base := base) request)
    (history : List (Event Owner)) (state : State)
    (result : (base + Audit Owner).Range request × (List (Event Owner) × State))
    (supported : result ∈ support ((record source request).run (history, state))) :
    seals result.2.1 = seals history := by
  cases request with
  | inl request =>
      simp only [record, StateT.run, support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      rfl
  | inr event =>
      cases event with
      | derived owner sending entry request response =>
          simp only [record, StateT.run, mem_support_pure_iff] at supported
          subst result
          simp [seals, List.filterMap_append]
      | sealing occurrence => exact False.elim (quiet True.intro)

/-- Every adaptive source program that emits no sealing event preserves the entire prior send-occurrence list; ordinary failures and all source state effects remain part of the execution. -/
theorem nonseal_program (source : QueryImpl base (StateT State ProbComp))
    (work : OracleComp (base + Audit Owner) Result) (quiet : work.IsQueryBoundP (IsSeal (base := base)) 0)
    (history : List (Event Owner)) (state : State) (result : Result × (List (Event Owner) × State))
    (supported : result ∈ support ((simulateQ (record source) work).run (history, state))) :
    seals result.2.1 = seals history := by
  induction work using OracleComp.inductionOn generalizing history state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind request continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have first : ¬ IsSeal (base := base) request := by simpa using quiet.1
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact (ih reply.1 (by simpa using quiet.2 reply.1) reply.2.1 reply.2.2 result tail).trans
        (nonseal_query source request first history state reply reached)

end BeaconcryptCore.Computational.RawCtxSourceEventRecorder

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.query

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.program

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.mem_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.mem_seals

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.source_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.source_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.nonseal_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.nonseal_query

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceEventRecorder.nonseal_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceEventRecorder.nonseal_program
