-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-! Public candidate instrumentation preserves the actual adaptive service syntax. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace
open CtxRomAuth
open PqxdhRecordLiftProtocol (Service ServiceSpec)
variable {n : Nat} {X : Type}

/-- Forward the actual source request and reply, appending only the public candidate extracted from that request. -/
def logger (extract : Service n → Option CtxDigest) :
    QueryImpl (ServiceSpec n) (StateT (List CtxDigest) (OracleComp (ServiceSpec n))) :=
  fun query past => (fun reply => (reply, past ++ (extract query).toList)) <$>
    (liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _)

/-- The original adaptive service program with its candidate list returned as analysis output. -/
def traced (extract : Service n → Option CtxDigest) (work : OracleComp (ServiceSpec n) X)
    (past : List CtxDigest) : OracleComp (ServiceSpec n) (X × List CtxDigest) :=
  (simulateQ (logger extract) work).run past

/-- A pure return adds no candidate. -/
theorem traced_pure (extract : Service n → Option CtxDigest) (value : X) (past : List CtxDigest) :
    traced extract (pure value) past = pure (value, past) := by
  simp only [traced, simulateQ_pure, StateT.run_pure]

/-- Instrumentation forwards this exact service query and passes its unchanged reply to the original continuation. -/
theorem traced_query_bind (extract : Service n → Option CtxDigest) (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X) (past : List CtxDigest) :
    traced extract ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= next) past =
      ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= fun reply =>
        traced extract (next reply) (past ++ (extract query).toList)) := by
  simp only [traced, simulateQ_bind, simulateQ_spec_query]
  change ((logger extract query past) >>= fun result =>
    (simulateQ (logger extract) (next result.1)).run result.2) = _
  simp only [logger, bind_map_left]

/-- Candidate recording preserves the exact source attempted-seal freshness rule on every reply branch. -/
theorem traced_fresh (extract : Service n → Option CtxDigest)
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest)
    (seals : List (PqxdhRecordLiftWorldCompiler.Label n))
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated work seals).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh) :
    (PqxdhRecordLiftProtocolHistory.annotated (traced extract work past) seals).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh := by
  induction work using OracleComp.inductionOn generalizing past seals with
  | pure value => simp only [traced_pure, PqxdhRecordLiftProtocolHistory.annotated_pure, allQueriesSatisfy_pure]
  | query_bind query next ih =>
      simp only [traced_query_bind, PqxdhRecordLiftProtocolHistory.annotated_query_bind,
        allQueriesSatisfy_query_bind_iff] at fresh ⊢
      exact ⟨fresh.1, fun reply => ih reply _ _ (fresh.2 reply)⟩

/-- Every original source query bound remains valid for the instrumented syntax, including a zero selected-seal cap. -/
theorem traced_queries (extract : Service n → Option CtxDigest)
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest)
    (counted : Service n → Prop) [DecidablePred counted] (cap : Nat) (bound : work.IsQueryBoundP counted cap) :
    (traced extract work past).IsQueryBoundP counted cap := by
  induction work using OracleComp.inductionOn generalizing past cap with
  | pure value => simpa only [traced_pure] using isQueryBoundP_pure counted (value, past) cap
  | query_bind query next ih =>
      simp only [traced_query_bind, isQueryBoundP_query_bind_iff] at bound ⊢
      exact ⟨bound.1, fun reply => ih reply _ _ (bound.2 reply)⟩

/-- Forgetting only the analysis list recovers the complete original adaptive program. -/
theorem traced_erase (extract : Service n → Option CtxDigest)
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest) :
    Prod.fst <$> traced extract work past = work := by
  induction work using OracleComp.inductionOn generalizing past <;>
    simp [traced_pure, traced_query_bind, map_bind, *]

/-- Each extracted candidate consumes a counted original request, on every possible service reply path. -/
theorem traced_length (extract : Service n → Option CtxDigest)
    (counted : Service n → Prop) [DecidablePred counted]
    (charged : ∀ query digest, extract query = some digest → counted query)
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest) (cap : Nat)
    (bound : work.IsQueryBoundP counted cap)
    (result : X × List CtxDigest) (supported : result ∈ support (traced extract work past)) :
    result.2.length ≤ past.length + cap := by
  induction work using OracleComp.inductionOn generalizing past cap result with
  | pure value =>
      simpa only [traced_pure, support_pure, Set.mem_singleton_iff] using
        supported ▸ Nat.le_add_right past.length cap
  | query_bind query next ih =>
      rw [traced_query_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      rw [isQueryBoundP_query_bind_iff] at bound
      have tailBound := ih reply _ _ (bound.2 reply) result continued
      cases extracted : extract query with
      | none =>
          simp only [extracted, Option.toList_none, List.append_nil] at tailBound
          split_ifs at tailBound <;> omega
      | some digest =>
          have countedQuery := charged query digest extracted
          simp only [countedQuery, ↓reduceIte, not_true_eq_false, false_or, extracted,
            Option.toList_some, List.length_append, List.length_singleton] at bound tailBound
          omega

/-- Every complete continuation retains the entire existing candidate trace. -/
theorem traced_prefix (extract : Service n → Option CtxDigest)
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest)
    (result : X × List CtxDigest) (supported : result ∈ support (traced extract work past)) :
    past.IsPrefix result.2 := by
  induction work using OracleComp.inductionOn generalizing past result with
  | pure value =>
      simpa only [traced_pure, support_pure, Set.mem_singleton_iff] using
        supported ▸ List.prefix_refl past
  | query_bind query next ih =>
      rw [traced_query_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      exact (List.prefix_append past (extract query).toList).trans (ih reply _ result continued)

/-- The current public candidate appears in every supported completed trace, regardless of the actual reply and continuation. -/
theorem traced_candidate (extract : Service n → Option CtxDigest) (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (past : List CtxDigest) (digest : CtxDigest) (extracted : extract query = some digest)
    (result : X × List CtxDigest)
    (supported : result ∈ support (traced extract
      ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= next) past)) :
    digest ∈ result.2 := by
  rw [traced_query_bind, mem_support_bind_iff] at supported
  obtain ⟨reply, _, continued⟩ := supported
  apply (traced_prefix extract (next reply) _ result continued).sublist.subset
  simp only [extracted, Option.toList_some, List.mem_append, List.mem_singleton, or_true]

/-- Fixed-width guessing interface: unused indices return none and require no extra source requests. -/
def guess (cap : Nat) (index : Fin cap) (result : X × List CtxDigest) : Option CtxDigest :=
  result.2[index.val]?

/-- Every recorded digest occurs at one of the charged finite indices; padding cannot erase a candidate. -/
theorem guess_complete (cap : Nat) (result : X × List CtxDigest)
    (length : result.2.length ≤ cap) (digest : CtxDigest) (present : digest ∈ result.2) :
    ∃ index : Fin cap, guess cap index result = some digest := by
  obtain ⟨index, within, value⟩ := List.mem_iff_getElem.mp present
  exact ⟨⟨index, Nat.lt_of_lt_of_le within length⟩, List.getElem?_eq_some_iff.mpr ⟨within, value⟩⟩

/-- Erasure also retains the entire interpreter state, including hidden caches, dictionaries and counters. -/
theorem interpreted_erase {State : Type} (extract : Service n → Option CtxDigest)
    (impl : QueryImpl (ServiceSpec n) (StateT State ProbComp))
    (work : OracleComp (ServiceSpec n) X) (past : List CtxDigest) (state : State) :
    Prod.map Prod.fst id <$> (simulateQ impl (traced extract work past)).run state =
      (simulateQ impl work).run state := by
  have same := congrArg (fun program => (simulateQ impl program).run state)
    (traced_erase extract work past)
  rw [simulateQ_map, StateT.run_map] at same
  exact (congrArg (fun f => f <$> (simulateQ impl (traced extract work past)).run state)
    (show Prod.map Prod.fst id = (fun p : (X × List CtxDigest) × State => (p.1.1, p.2)) from rfl)).trans same

/-- The original source cap supplies every fixed-width index needed to cover its complete public candidate trace. -/
theorem source_guess_complete (extract : Service n → Option CtxDigest)
    (counted : Service n → Prop) [DecidablePred counted]
    (charged : ∀ query digest, extract query = some digest → counted query)
    (work : OracleComp (ServiceSpec n) X) (cap : Nat) (bound : work.IsQueryBoundP counted cap)
    (result : X × List CtxDigest) (supported : result ∈ support (traced extract work []))
    (digest : CtxDigest) (present : digest ∈ result.2) :
    ∃ index : Fin cap, guess cap index result = some digest := by
  exact guess_complete cap result (by
    simpa only [List.length_nil, Nat.zero_add] using
      (traced_length extract counted charged work [] cap bound result supported)) digest present

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_query_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_length
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.traced_candidate
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.guess_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.guess_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.interpreted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.interpreted_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.source_guess_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace.source_guess_complete
