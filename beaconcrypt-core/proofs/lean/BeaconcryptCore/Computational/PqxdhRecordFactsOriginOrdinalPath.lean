-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries

/-! A literal supported execution path for the same complete source sealing trace. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec Sealing)
open PqxdhRecordFactsOriginOrdinalTrace (track Result)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordLiftWorldProvenance (sealingCoordinates)
variable {n : Nat} {X : Type}

/-- The exact analysis cut emitted at this callback before its reply; nonsealing callbacks emit none. -/
def cutAt (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) : List (Cut n X) :=
  match query with
  | .sealing pending => [⟨pending, next, state, past⟩]
  | _ => []

/-- Every actual callback reply and complete pre/post state along this one supported traced execution, including literal opening optional plaintext replies. -/
inductive Path (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)) :
    OracleComp (ServiceSpec n) X → CtxPrivate n → List (Label n) → Result n X → Prop
  | done (value : X) (state : CtxPrivate n) (past : List (Label n)) :
      Path service (pure value) state past ([], (value, state))
  | step {query : Service n} {next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X}
      {state : CtxPrivate n} {past : List (Label n)}
      {reply : (ServiceSpec n).Range query × CtxPrivate n} {result : Result n X}
      (supported : reply ∈ support ((service query).run state))
      (tail : Path service (next reply.1) reply.2 (past ++ sealingCoordinates query) result) :
      Path service ((ServiceSpec n).query query >>= next) state past
        (cutAt query next state past ++ result.1, result.2)

private theorem nonseal_cut (query : Service n) (nonSeal : ∀ pending, query ≠ .sealing pending)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) :
    cutAt query next state past = [] ∧ sealingCoordinates query = [] := by
  cases query
  case sealing pending => exact False.elim (nonSeal pending rfl)
  all_goals exact ⟨rfl, rfl⟩

/-- Every literal path is a supported output of the same complete tracked execution. -/
theorem path_support (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)} {result : Result n X}
    (path : Path service work state past result) : result ∈ support (track service work state past) := by
  induction path with
  | done value state past =>
    change ([], (value, state)) ∈ support (pure ([], (value, state)) : ProbComp (Result n X))
    simp only [support_pure, Set.mem_singleton_iff]
  | @step query next state past reply result supported tail ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      rw [PqxdhRecordFactsOriginOrdinalTrace.track_sealing]
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨reply, supported, result, ih, rfl⟩
    · have empty := nonseal_cut query (fun pending same => sealed ⟨pending, same⟩) next state past
      rw [PqxdhRecordFactsOriginOrdinalTrace.track_other _ query (fun pending same => sealed ⟨pending, same⟩)]
      simp only [mem_support_bind_iff]
      exact ⟨reply, supported, by simpa only [empty.1, empty.2, List.nil_append, List.append_nil] using ih⟩

/-- A supported tracked output supplies its actual callback path, retaining this same complete cut list and final state. -/
theorem support_path (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n)) (result : Result n X)
    (supported : result ∈ support (track service work state past)) : Path service work state past result := by
  induction work using OracleComp.inductionOn generalizing state past result with
  | pure value =>
    change result ∈ support (pure ([], (value, state)) : ProbComp (Result n X)) at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Path.done value state past
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      rw [PqxdhRecordFactsOriginOrdinalTrace.track_sealing] at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, answered, inner, finished, rfl⟩ := supported
      exact Path.step answered (ih reply.1 reply.2 (past ++ [pending.material]) inner finished)
    · rw [PqxdhRecordFactsOriginOrdinalTrace.track_other _ query (fun pending same => sealed ⟨pending, same⟩)] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨reply, answered, finished⟩ := supported
      have empty := nonseal_cut query (fun pending same => sealed ⟨pending, same⟩) next state past
      have tail : Path service (next reply.1) reply.2 (past ++ sealingCoordinates query) result := by
        simpa only [empty.2, List.append_nil] using ih reply.1 reply.2 past result finished
      simpa only [empty.1, List.nil_append] using Path.step answered tail

/-- A supported prefix carries its exact already executed cut list in addition to complete operational state and history. -/
inductive Prefix (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n)) :
    OracleComp (ServiceSpec n) X → CtxPrivate n → List (Label n) → List (Cut n X) → Prop
  | initial : Prefix service initial start past0 initial start past0 []
  | step {query : Service n} {next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X}
      {state : CtxPrivate n} {past : List (Label n)} {cuts : List (Cut n X)}
      {reply : (ServiceSpec n).Range query × CtxPrivate n}
      (before : Prefix service initial start past0 ((ServiceSpec n).query query >>= next) state past cuts)
      (supported : reply ∈ support ((service query).run state)) :
      Prefix service initial start past0 (next reply.1) reply.2 (past ++ sealingCoordinates query)
        (cuts ++ cutAt query next state past)

/-- Forgetting only the prefix's auxiliary cut list yields the exact original source Reach relation. -/
theorem prefix_reach (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (before : Prefix service initial start past0 work state past cuts) :
    PqxdhRecordFactsPrivateCacheSource.Reach service initial start past0 work state past := by
  induction before with
  | initial => exact .initial
  | step before supported ih => exact .step ih supported

/-- Prefix concatenation retains the exact chronological cut list and complete operational state at the join. -/
theorem prefix_trans (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial middle work : OracleComp (ServiceSpec n) X} {start between state : CtxPrivate n}
    {past0 history past : List (Label n)} {earlier later : List (Cut n X)}
    (first : Prefix service initial start past0 middle between history earlier)
    (second : Prefix service middle between history work state past later) :
    Prefix service initial start past0 work state past (earlier ++ later) := by
  induction second with
  | initial => simpa only [List.append_nil] using first
  | @step query next state past cuts reply before supported ih =>
    simpa only [List.append_assoc] using Prefix.step ih supported

/-- A literal prefix and its complete suffix reconstruct one path with the exact earlier/later cut split. -/
theorem prefix_path (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (before : Prefix service initial start past0 work state past cuts)
    {result : Result n X} (tail : Path service work state past result) :
    Path service initial start past0 (cuts ++ result.1, result.2) := by
  induction before generalizing result with
  | initial => simpa only [List.nil_append] using tail
  | @step query next state past cuts reply before supported ih =>
    simpa only [List.append_assoc] using ih (Path.step supported tail)

/-- Literal all-service expansion of the same source trace, including complete optional opening replies. -/
theorem track_query (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) :
    track service ((ServiceSpec n).query query >>= next) state past =
      (do let reply ← (service query).run state
          let result ← track service (next reply.1) reply.2 (past ++ sealingCoordinates query)
          pure (cutAt query next state past ++ result.1, result.2)) := by
  by_cases sealed : ∃ pending, query = .sealing pending
  · obtain ⟨pending, rfl⟩ := sealed
    rfl
  · rw [PqxdhRecordFactsOriginOrdinalTrace.track_other _ query (fun pending same => sealed ⟨pending, same⟩)]
    have empty := nonseal_cut query (fun pending same => sealed ⟨pending, same⟩) next state past
    simp only [empty.1, empty.2, List.nil_append, List.append_nil, Prod.mk.eta, bind_pure]

/-- Inverting this exact execution path retains the actual current callback reply and its complete same-result suffix. -/
theorem path_query (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) (result : Result n X)
    (path : Path service ((ServiceSpec n).query query >>= next) state past result) :
    ∃ reply, reply ∈ support ((service query).run state) ∧ ∃ tail : Result n X,
      Path service (next reply.1) reply.2 (past ++ sealingCoordinates query) tail ∧
      result = (cutAt query next state past ++ tail.1, tail.2) := by
  have supported := path_support service path
  rw [track_query] at supported
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨reply, answered, tail, finished, same⟩ := supported
  exact ⟨reply, answered, tail, support_path service _ _ _ tail finished, same⟩

/-- An actual opening keeps its literal optional plaintext reply and full poststate, and its suffix has the identical remaining sealing-cut list and final result. -/
theorem path_opening (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (pending : PqxdhRecordLiftProtocol.Opening n)
    (next : (ServiceSpec n).Range (.opening pending) → OracleComp (ServiceSpec n) X)
    (state : CtxPrivate n) (past : List (Label n)) (result : Result n X)
    (path : Path service ((ServiceSpec n).query (.opening pending) >>= next) state past result) :
    ∃ reply, reply ∈ support ((service (.opening pending)).run state) ∧
      Path service (next reply.1) reply.2 past result := by
  obtain ⟨reply, answered, tail, continued, same⟩ := path_query service (.opening pending) next state past result path
  simp only [cutAt, List.nil_append, Prod.mk.eta] at same
  subst result
  exact ⟨reply, answered, by simpa only [sealingCoordinates, List.append_nil] using continued⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.support_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.support_path

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_reach

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.prefix_path

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.track_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.track_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath.path_opening
