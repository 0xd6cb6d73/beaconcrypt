import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The private transcript records only successful original send API replies, with their original owner and returned sequence. It forwards every original request and reply before continuing the original client. An initial publication prefix can retain the actual first registration ciphertext, whose publication must be established by its source builder. No cursor, secret chain value or synthesized checker output is used to decide whether the target record was published.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPublishedRecords
open RawCtxProtocolReveals
variable {S B : Nat} {Result : Type}

abbrev Publication (S B : Nat) := Owner S B × Std.U64

def record (query : (SourceSpec S B).Domain) : (SourceSpec S B).Range query → List (Publication S B) :=
  match query with
  | .inl (.inl ⟨index, .inl (_, peer)⟩) => fun reply =>
      match reply with | none => [] | some sent => [(.server index peer, sent.sequence)]
  | .inl (.inr (.inl ⟨index, .inl _⟩)) => fun reply =>
      match reply with | none => [] | some sent => [(.beacon index, sent.sequence)]
  | _ => fun _ => []

def track (client : OracleComp (SourceSpec S B) Result) (initial : List (Publication S B)) :
    OracleComp (SourceSpec S B) (Result × List (Publication S B)) :=
  OracleComp.construct (C := fun _ => List (Publication S B) → OracleComp (SourceSpec S B) (Result × List (Publication S B)))
    (fun value history => pure (value, history))
    (fun query _ recurse history => do
      let reply ← (liftM ((SourceSpec S B).query query) : OracleComp (SourceSpec S B) _)
      recurse reply (history ++ record query reply)) client initial

/-- Removing only the private publication transcript recovers the literal original adaptive client. -/
theorem erase (client : OracleComp (SourceSpec S B) Result) (initial : List (Publication S B)) :
    Prod.fst <$> track client initial = client := by
  induction client using OracleComp.inductionOn generalizing initial with
  | pure value => simp [track]
  | query_bind query next ih =>
    simp only [track, OracleComp.construct_query_bind, map_bind]
    congr 1
    funext reply
    exact ih reply _

/-- The private transcript preserves each original structural source-budget coordinate exactly. -/
theorem bounded (client : OracleComp (SourceSpec S B) Result) (initial : List (Publication S B))
    (budget : RawCtxRevealBudgets.Budget) :
    RawCtxRevealBudgets.Bounded (track client initial) budget ↔ RawCtxRevealBudgets.Bounded client budget := by
  change IsQueryBound _ budget _ _ ↔ IsQueryBound _ budget _ _
  calc
    _ ↔ IsQueryBound (Prod.fst <$> track client initial) budget RawCtxRevealBudgets.permitted RawCtxRevealBudgets.remaining :=
      (isQueryBound_map_iff _ _ _ _ _).symm
    _ ↔ _ := by rw [erase]

def target (client : OracleComp (SourceSpec S B) Bool) (initial : List (Publication S B))
    (owner : Owner S B) (sequence : Std.U64) : OracleComp (SourceSpec S B) Bool :=
  (fun result => result.1 && decide ((owner, sequence) ∈ result.2)) <$> track client initial

/-- The target gate pays exactly the original all-reply source budget; the given initial publication prefix is retained without manufacturing an operation. -/
theorem target_bounded (client : OracleComp (SourceSpec S B) Bool) (initial : List (Publication S B))
    (owner : Owner S B) (sequence : Std.U64) (budget : RawCtxRevealBudgets.Budget) :
    RawCtxRevealBudgets.Bounded (target client initial owner sequence) budget ↔ RawCtxRevealBudgets.Bounded client budget := by
  simp only [target, RawCtxRevealBudgets.Bounded, isQueryBound_map_iff]
  exact bounded client initial budget

/-- An actual source trace retains each original request, supported optional reply and complete intermediate state. -/
inductive Trace {State : Type} (impl : QueryImpl (SourceSpec S B) (StateT State ProbComp)) :
    OracleComp (SourceSpec S B) Result → State → (Result × State) → List (Publication S B) → Prop where
  | pure (value : Result) (state : State) : Trace impl (pure value) state (value, state) []
  | query (query : (SourceSpec S B).Domain) (next : (SourceSpec S B).Range query → OracleComp (SourceSpec S B) Result)
      (state : State) (reply : (SourceSpec S B).Range query × State) (result : Result × State) (later : List (Publication S B))
      (actual : reply ∈ support ((impl query).run state))
      (tail : Trace impl (next reply.1) reply.2 result later) :
      Trace impl (((SourceSpec S B).query query : OracleComp (SourceSpec S B) _) >>= next) state result (record query reply.1 ++ later)

/-- Every transcript result comes from the original complete source execution and its actual supported optional replies, retaining the given initial publication prefix. -/
theorem track_trace {State : Type} (impl : QueryImpl (SourceSpec S B) (StateT State ProbComp))
    (client : OracleComp (SourceSpec S B) Result) (initial : List (Publication S B)) (state : State)
    (result : (Result × List (Publication S B)) × State)
    (supported : result ∈ support ((simulateQ impl (track client initial)).run state)) :
    ∃ later, result.1.2 = initial ++ later ∧ Trace impl client state (result.1.1, result.2) later := by
  induction client using OracleComp.inductionOn generalizing initial state result with
  | pure value =>
    simp only [track, OracleComp.construct_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], by simp, .pure value state⟩
  | query_bind query next ih =>
    simp only [track, OracleComp.construct_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, actual, rest⟩ := supported
    obtain ⟨later, recorded, traced⟩ := ih reply.1 (initial ++ record query reply.1) reply.2 result rest
    exact ⟨record query reply.1 ++ later, by simpa only [List.append_assoc] using recorded,
      .query query next state reply (result.1.1, result.2) later actual traced⟩

/-- A true target-gated source result has an actual successful-send trace (or the explicitly retained initial publication), never a synthetic checker-created record. -/
theorem target_source {State : Type} (impl : QueryImpl (SourceSpec S B) (StateT State ProbComp))
    (client : OracleComp (SourceSpec S B) Bool) (initial : List (Publication S B))
    (owner : Owner S B) (sequence : Std.U64) (state : State) (result : Bool × State)
    (supported : result ∈ support ((simulateQ impl (target client initial owner sequence)).run state))
    (accepted : result.1 = true) :
    ∃ later, Trace impl client state (true, result.2) later ∧ (owner, sequence) ∈ initial ++ later := by
  simp only [target, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨returned, actual, rfl⟩ := supported
  have decision : returned.1.1 = true ∧ (owner, sequence) ∈ returned.1.2 := by
    simpa only [Prod.map_apply, id_eq, Bool.and_eq_true, decide_eq_true_eq] using accepted
  obtain ⟨later, recorded, traced⟩ := track_trace impl client initial state returned actual
  exact ⟨later, by simpa only [decision.1] using traced, recorded ▸ decision.2⟩

/-- Erasing the private transcript after any original source interpreter preserves its complete result and final state. -/
theorem interpreted_erase {State : Type} (impl : QueryImpl (SourceSpec S B) (StateT State ProbComp))
    (client : OracleComp (SourceSpec S B) Result) (initial : List (Publication S B)) (state : State) :
    Prod.map Prod.fst id <$> (simulateQ impl (track client initial)).run state =
      (simulateQ impl client).run state := by
  change (fun result => (result.1.1, result.2)) <$> (simulateQ impl (track client initial)).run state = _
  rw [← StateT.run_map, ← simulateQ_map, erase]

end BeaconcryptCore.Computational.RawCtxPublishedRecords

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.bounded

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.target_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.target_bounded

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.track_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.track_trace

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.target_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.target_source

/-- info: 'BeaconcryptCore.Computational.RawCtxPublishedRecords.interpreted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPublishedRecords.interpreted_erase
