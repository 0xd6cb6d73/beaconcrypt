-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteAdaptive

/-! Literal support paths for the actual adaptive selected-match marker. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath
open AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open PqxdhRecordFactsOriginOrdinalPath (Path Prefix cutAt)
open PqxdhRecordLiftWorldProvenance (sealingCoordinates)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginMuteUntilBad (serviceBad)
variable {n : Nat} {X : Type}

/-- The same literal supported callback replies and complete states as `Path`, retaining the exact selected-match flag at each step. -/
inductive Flagged (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
    OracleComp (ServiceSpec n) X → CtxPrivate n → List (Label n) → Result n X → Bool → Bool → Prop
  | done (value : X) (state : CtxPrivate n) (past : List (Label n)) (flag : Bool) :
      Flagged target decode service (pure value) state past ([], (value, state)) flag flag
  | step {query : Service n} {next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X}
      {state : CtxPrivate n} {past : List (Label n)}
      {reply : (ServiceSpec n).Range query × CtxPrivate n} {result : Result n X} {before after : Bool}
      (supported : reply ∈ support ((service query).run state))
      (tail : Flagged target decode service (next reply.1) reply.2 (past ++ sealingCoordinates query) result
        (before || serviceBad target decode query state) after) :
      Flagged target decode service ((ServiceSpec n).query query >>= next) state past
        (cutAt query next state past ++ result.1, result.2) before after

/-- Forget only the exact analysis flag: all original path replies, state, chronology and the complete final result remain. -/
theorem erase (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)}
    {result : Result n X} {before after : Bool}
    (path : Flagged target decode service work state past result before after) :
    Path service work state past result := by
  induction path with
  | done value state past flag => exact .done value state past
  | step supported tail ih => exact .step supported ih

/-- Decorate this literal original path with its actual sticky flag without changing any callback reply or state. -/
theorem lift (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)}
    {result : Result n X} (path : Path service work state past result) (before : Bool) :
    ∃ after, Flagged target decode service work state past result before after := by
  induction path generalizing before with
  | done value state past => exact ⟨before, .done value state past before⟩
  | @step query next state past reply result supported tail ih =>
    exact (ih (before || serviceBad target decode query state)).imp (fun _ followed => Flagged.step supported followed)

private theorem marked_query (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (before : Bool) :
    (simulateQ (marked target decode service) ((ServiceSpec n).query query >>= next)).run (state, before) =
      (do let reply ← (service query).run state
          (simulateQ (marked target decode service) (next reply.1)).run
            (reply.2, before || serviceBad target decode query state)) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [marked, StateT.run, bind_assoc, pure_bind]

/-- This exact flagged path gives its literal complete marked output, with every callback state and reply retained. -/
theorem flagged_support (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)}
    {result : Result n X} {before after : Bool}
    (path : Flagged target decode service work state past result before after) :
    (result.2.1, (result.2.2, after)) ∈ support ((simulateQ (marked target decode service) work).run (state, before)) := by
  induction path with
  | done value state past flag =>
    change (value, (state, flag)) ∈ support (pure (value, (state, flag)) : ProbComp _)
    simp only [support_pure, Set.mem_singleton_iff]
  | @step query next state past reply result before after supported tail ih =>
    rw [marked_query]
    exact (mem_support_bind_iff _ _ _).mpr ⟨reply, supported, ih⟩

/-- Every supported marked output has a literal path with exactly that complete output/state and flag, rather than merely a sibling unmarked outcome. -/
theorem support_flagged (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (before : Bool) (result : X × CtxPrivate n × Bool)
    (supported : result ∈ support ((simulateQ (marked target decode service) work).run (state, before))) :
    ∃ cuts, Flagged target decode service work state past (cuts, (result.1, result.2.1)) before result.2.2 := by
  induction work using OracleComp.inductionOn generalizing state past before result with
  | pure value =>
    change result ∈ support (pure (value, (state, before)) : ProbComp _) at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ ⟨[], Flagged.done value state past before⟩
  | query_bind query next ih =>
    rw [marked_query, mem_support_bind_iff] at supported
    obtain ⟨reply, answered, continued⟩ := supported
    obtain ⟨cuts, tail⟩ := ih reply.1 reply.2 (past ++ sealingCoordinates query) (before || serviceBad target decode query state) result continued
    exact ⟨cutAt query next state past ++ cuts, Flagged.step answered tail⟩

/-- Marked support is exactly the existence of a literal same-output flagged path, retaining a concrete chronological cut list. -/
theorem support_iff (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (before : Bool) (result : X × CtxPrivate n × Bool) :
    result ∈ support ((simulateQ (marked target decode service) work).run (state, before)) ↔
      ∃ cuts, Flagged target decode service work state past (cuts, (result.1, result.2.1)) before result.2.2 :=
  ⟨support_flagged target decode service work state past before result,
    fun ⟨_, path⟩ => flagged_support target decode service path⟩

/-- A flag already raised on this exact path remains raised at its complete final outcome. -/
theorem sticky (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)}
    {result : Result n X} {before after : Bool}
    (path : Flagged target decode service work state past result before after) (hit : before = true) :
    after = true := by
  induction path with
  | done value state past flag => exact hit
  | @step query next state past reply result before after supported tail ih =>
    exact ih (by simp only [hit, Bool.true_or])

/-- A selected match at a literal callback forces the flag in every continuation of that same flagged step. -/
theorem hit_suffix (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (state : CtxPrivate n)
    {work : OracleComp (ServiceSpec n) X} {afterState : CtxPrivate n} {past : List (Label n)}
    {result : Result n X} {before after : Bool}
    (tail : Flagged target decode service work afterState past result
      (before || serviceBad target decode query state) after)
    (hit : serviceBad target decode query state = true) : after = true :=
  sticky target decode service tail (by simp only [hit, Bool.or_true])

/-- Decorate this exact literal prefix once, retaining its full earlier cut list and every possible compatible flagged continuation. -/
theorem prefix_lift (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X)}
    (prefixPath : Prefix service initial start past0 work state past cuts) (before : Bool) :
    ∃ middle, ∀ (result : Result n X) (after : Bool),
      Flagged target decode service work state past result middle after →
      Flagged target decode service initial start past0 (cuts ++ result.1, result.2) before after := by
  induction prefixPath with
  | initial =>
    exact ⟨before, fun _ _ tail => tail⟩
  | @step query next state past cuts reply prefixPath supported ih =>
    obtain ⟨middle, prior⟩ := ih
    refine ⟨middle || serviceBad target decode query state, ?_⟩
    exact fun result after tail => by simpa only [List.append_assoc] using prior _ after (Flagged.step supported tail)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.erase
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.lift
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.flagged_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.flagged_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.support_flagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.support_flagged
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.support_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.support_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.sticky
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.hit_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.hit_suffix
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.prefix_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath.prefix_lift
