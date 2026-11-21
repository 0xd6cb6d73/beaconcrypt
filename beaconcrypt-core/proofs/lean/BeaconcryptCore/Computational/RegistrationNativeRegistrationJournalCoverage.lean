-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog
import BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalProjection
/-! Every actual typed journal occurrence has its exact same-run source prefix and suffix. Counts include all failed attempts; successful registration markers retain their literal RustM replies. Strict earlier publication is derived inside the same source path, without a prefix-owner or uniqueness condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeRawRegistrationJournal (Mark typedMark)
variable {Query S A : Type} {spec : OracleSpec Query}

def count (predicate : spec.Domain → Prop) [DecidablePred predicate] (calls : List (Call spec S)) : Nat :=
  calls.countP fun call => decide (predicate call.query)

/-- A genuine registration occurrence in a filtered journal has its exact earlier and later original callback prefixes. -/
theorem split_filterMap {X Y : Type} (f : X → Option Y) (values : List X) (leading trailing : List Y) (value : Y)
    (same : values.filterMap f = leading ++ value :: trailing) :
    ∃ earlier selected later, values = earlier ++ selected :: later ∧ earlier.filterMap f = leading ∧
      f selected = some value ∧ later.filterMap f = trailing := by
  induction values generalizing leading with
  | nil => simp at same
  | cons head tail ih =>
    cases chosen : f head with
    | none =>
      simp only [List.filterMap_cons, chosen] at same
      obtain ⟨earlier, selected, later, split, first, middle, last⟩ := ih leading same
      exact ⟨head :: earlier, selected, later, by simp only [split, List.cons_append], by simp only [List.filterMap_cons, chosen, first], middle, last⟩
    | some selected =>
      cases leading with
      | nil =>
        simp only [List.filterMap_cons, chosen, List.nil_append, List.cons.injEq] at same
        exact ⟨[], head, tail, rfl, rfl, same.1 ▸ chosen, same.2⟩
      | cons first rest =>
        simp only [List.filterMap_cons, chosen, List.cons_append, List.cons.injEq] at same
        obtain ⟨earlier, selected', later, split, first', middle, last⟩ := ih rest same.2
        exact ⟨head :: earlier, selected', later, by simp only [split, List.cons_append], by simp only [List.filterMap_cons, chosen, first', same.1], middle, last⟩

private theorem step_count (implementation : QueryImpl spec (StateT S ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (query : spec.Domain)
    (before : S × List (Call spec S)) (result : spec.Range query × (S × List (Call spec S)))
    (supported : result ∈ support ((RegistrationNativeStageTrace.handler implementation query).run before)) :
    count predicate result.2.2 = count predicate before.2 + if predicate query then 1 else 0 := by
  simp only [RegistrationNativeStageTrace.handler, StateT.run, support_map] at supported
  obtain ⟨returned, _called, rfl⟩ := supported
  simp only [count, List.countP_append, List.countP_singleton]
  by_cases selected : predicate query <;> simp only [selected, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true]

/-- Actual source journaling consumes one ordinal for every counted typed request, including all failed replies. -/
theorem count_bound (implementation : QueryImpl spec (StateT S ProbComp))
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (work : OracleComp spec A) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap)
    (before : S × List (Call spec S)) (result : A × (S × List (Call spec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run before)) :
    count predicate result.2.2 ≤ count predicate before.2 + cap := by
  induction work using OracleComp.inductionOn generalizing before cap result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, later⟩ := supported
    have rest := ih middle.1 _ (bounded.2 middle.1) middle.2 result later
    rw [step_count implementation predicate query before middle called] at rest
    by_cases selected : predicate query
    · have positive := bounded.1.resolve_left (fun impossible => impossible selected)
      simp only [selected, ite_true] at rest
      omega
    · simpa only [selected, ite_false, Nat.add_zero] using rest

/-- Every actual counted callback occurrence has an all-attempt ordinal strictly below the original typed allowance. -/
theorem ordinal_bound (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (calls leading trailing : List (Call spec S)) (call : Call spec S) (cap : Nat)
    (split : calls = leading ++ call :: trailing) (selected : predicate call.query) (bounded : count predicate calls ≤ cap) :
    count predicate leading < cap := by
  rw [split] at bounded
  simp only [count, List.countP_append, List.countP_cons, selected, decide_true, ite_true] at bounded ⊢
  omega
/-- An exact journal split retains the corresponding exact source prefix and suffix, even when identical callback records recur. -/
theorem path_split (implementation : QueryImpl spec (StateT S ProbComp)) (first last : S)
    (leading trailing : List (Call spec S)) (call : Call spec S)
    (actual : Path implementation first (leading ++ call :: trailing) last) :
    Path implementation first leading call.before ∧ RegistrationNativeStageTrace.Executed implementation call ∧
      Path implementation call.after trailing last := by
  induction leading generalizing first with
  | nil =>
    cases actual with
    | cons current called rest last following => exact ⟨.nil _, called, following⟩
  | cons head leading ih =>
    cases actual with
    | cons current called rest last following =>
      obtain ⟨before, middle, after⟩ := ih _ following
      exact ⟨.cons head called _ _ before, middle, after⟩

def IsAccept : TypedSpec.Domain → Prop
  | .inr (.accept _) => True
  | _ => False

def IsBundle : TypedSpec.Domain → Prop
  | .inr (.bundle _) => True
  | _ => False

instance : DecidablePred IsAccept := fun query => by unfold IsAccept; split <;> infer_instance
instance : DecidablePred IsBundle := fun query => by unfold IsBundle; split <;> infer_instance

/-- A successful decoded acceptance marker contains the literal typed parser input and actual successful source reply. -/
theorem accept_call (call : Call TypedSpec S) (packet : beaconcrypt_core.registration.InitPacket) (session : Nat)
    (marked : typedMark call.query call.reply = some (.accept packet (some session))) :
    ∃ before after, call = ⟨.inr (.accept packet), before, .ok (some session), after⟩ := by
  rcases call with ⟨query, before, reply, after⟩
  cases query with
  | inl coin => simp only [typedMark, reduceCtorEq] at marked
  | inr command =>
    cases command with
    | accept parsed =>
      simp only [typedMark, Option.some.injEq, Mark.accept.injEq] at marked
      obtain ⟨rfl, successful⟩ := marked
      cases reply with
      | fail error => simp only [RegistrationNativeRawAdapter.resultOption, reduceCtorEq] at successful
      | div => simp only [RegistrationNativeRawAdapter.resultOption, reduceCtorEq] at successful
      | ok returned =>
        simp only [RegistrationNativeRawAdapter.resultOption] at successful
        cases successful
        exact ⟨before, after, rfl⟩
    | _ => simp only [typedMark, Option.some.injEq, reduceCtorEq] at marked

/-- A successful publication marker contains its literal owner, exact bytes and actual source reply. -/
theorem bundle_call (call : Call TypedSpec S) (owner : Nat) (bytes : Pqxdh.Bytes)
    (marked : typedMark call.query call.reply = some (.bundle owner (some bytes))) :
    ∃ before after, call = ⟨.inr (.bundle owner), before, .ok (some bytes), after⟩ := by
  rcases call with ⟨query, before, reply, after⟩
  cases query with
  | inl coin => simp only [typedMark, reduceCtorEq] at marked
  | inr command =>
    cases command with
    | bundle index =>
      simp only [typedMark, Option.some.injEq, Mark.bundle.injEq] at marked
      obtain ⟨rfl, successful⟩ := marked
      cases reply with
      | fail error => simp only [RegistrationNativeRawAdapter.resultOption, reduceCtorEq] at successful
      | div => simp only [RegistrationNativeRawAdapter.resultOption, reduceCtorEq] at successful
      | ok returned =>
        simp only [RegistrationNativeRawAdapter.resultOption] at successful
        cases successful
        exact ⟨before, after, rfl⟩
    | _ => simp only [typedMark, Option.some.injEq, reduceCtorEq] at marked

/-- Every successful registration journal occurrence derives its actual callback, source prefixes and bounded all-attempt acceptance ordinal. -/
theorem acceptance (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (cap : Nat) (bounded : work.IsQueryBoundP IsAccept cap) (before : S)
    (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before, [])))
    (leading trailing : List Mark) (packet : beaconcrypt_core.registration.InitPacket) (session : Nat)
    (marked : result.2.2.filterMap (fun call => typedMark call.query call.reply) = leading ++ .accept packet (some session) :: trailing) :
    ∃ earlier call later, result.2.2 = earlier ++ call :: later ∧
      earlier.filterMap (fun call => typedMark call.query call.reply) = leading ∧
      typedMark call.query call.reply = some (.accept packet (some session)) ∧
      count IsAccept earlier < cap ∧ Path implementation before earlier call.before ∧
      RegistrationNativeStageTrace.Executed implementation call ∧ Path implementation call.after later result.2.1 := by
  obtain ⟨earlier, call, later, split, first, current, last⟩ := split_filterMap _ _ leading trailing (.accept packet (some session)) marked
  have actual := RegistrationNativeStageTrace.path implementation work before result supported
  have paths := path_split implementation before result.2.1 earlier later call (split ▸ actual)
  have total := count_bound implementation IsAccept work cap bounded (before, []) result supported
  have selected : IsAccept call.query := by
    obtain ⟨prior, after, rfl⟩ := accept_call call packet session current
    trivial
  refine ⟨earlier, call, later, split, first, current, ?_, paths.1, paths.2.1, paths.2.2⟩
  apply ordinal_bound IsAccept _ earlier later call cap split selected
  simpa only [count, List.countP_nil, Nat.zero_add] using total

def markAccept : Mark → Bool
  | .accept .. => true
  | _ => false

def markBundle : Mark → Bool
  | .bundle .. => true
  | _ => false

/-- The decoded marker projection counts every typed acceptance attempt, including all authentication and primitive failures. -/
theorem accept_count_project (calls : List (Call TypedSpec S)) :
    count IsAccept calls = (calls.filterMap (fun call => typedMark call.query call.reply)).countP markAccept := by
  induction calls with
  | nil => rfl
  | cons call calls ih =>
    rcases call with ⟨query, before, reply, after⟩
    cases query with
    | inl coin => simpa [count, IsAccept, typedMark] using ih
    | inr command => cases command <;> simpa [count, IsAccept, typedMark, markAccept] using ih

/-- The decoded projection counts every typed bundle attempt, including invalid handles and failed writers. -/
theorem bundle_count_project (calls : List (Call TypedSpec S)) :
    count IsBundle calls = (calls.filterMap (fun call => typedMark call.query call.reply)).countP markBundle := by
  induction calls with
  | nil => rfl
  | cons call calls ih =>
    rcases call with ⟨query, before, reply, after⟩
    cases query with
    | inl coin => simpa [count, IsBundle, typedMark] using ih
    | inr command => cases command <;> simpa [count, IsBundle, typedMark, markBundle] using ih

/-- A publication in the strict earlier decoded prefix has a real bounded all-attempt bundle ordinal and same-run source path strictly before the accepted call. -/
theorem earlier_bundle (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (qAccept qBundle : Nat) (acceptBound : work.IsQueryBoundP IsAccept qAccept) (bundleBound : work.IsQueryBoundP IsBundle qBundle) (before : S)
    (result : A × (S × List (Call TypedSpec S)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before, [])))
    (leading trailing : List Mark) (packet : beaconcrypt_core.registration.InitPacket) (session owner : Nat) (bytes : Pqxdh.Bytes)
    (marked : result.2.2.filterMap (fun call => typedMark call.query call.reply) = leading ++ .accept packet (some session) :: trailing)
    (published : .bundle owner (some bytes) ∈ leading) :
    ∃ firstCalls bundle middle accepted suffix,
      result.2.2 = firstCalls ++ bundle :: middle ++ accepted :: suffix ∧
      typedMark bundle.query bundle.reply = some (.bundle owner (some bytes)) ∧
      typedMark accepted.query accepted.reply = some (.accept packet (some session)) ∧
      count IsBundle firstCalls < qBundle ∧ count IsAccept (firstCalls ++ bundle :: middle) < qAccept ∧
      Path implementation before firstCalls bundle.before ∧ RegistrationNativeStageTrace.Executed implementation bundle ∧
      Path implementation bundle.after middle accepted.before ∧ RegistrationNativeStageTrace.Executed implementation accepted ∧
      Path implementation accepted.after suffix result.2.1 := by
  obtain ⟨earlier, accepted, suffix, split, first, acceptedMark, acceptOrdinal, beforeAccept, executedAccept, afterAccept⟩ :=
    acceptance implementation work qAccept acceptBound before result supported leading trailing packet session marked
  rw [← first, List.mem_filterMap] at published
  obtain ⟨bundle, member, bundleMark⟩ := published
  obtain ⟨firstCalls, middle, beforeSplit, prior, executedBundle, middlePath⟩ := beforeAccept.member bundle member
  have fullSplit : result.2.2 = firstCalls ++ bundle :: (middle ++ accepted :: suffix) := by
    rw [split, beforeSplit]
    simp only [List.append_assoc, List.cons_append]
  have total := count_bound implementation IsBundle work qBundle bundleBound (before, []) result supported
  have selected : IsBundle bundle.query := by
    obtain ⟨prior, after, rfl⟩ := bundle_call bundle owner bytes bundleMark
    trivial
  have bundleOrdinal := ordinal_bound IsBundle _ firstCalls (middle ++ accepted :: suffix) bundle qBundle fullSplit selected
    (by simpa only [count, List.countP_nil, Nat.zero_add] using total)
  refine ⟨firstCalls, bundle, middle, accepted, suffix, ?_, bundleMark, acceptedMark, bundleOrdinal, ?_, prior, executedBundle, middlePath, executedAccept, afterAccept⟩
  · simpa only [List.append_assoc, List.cons_append] using fullSplit
  · simpa only [beforeSplit] using acceptOrdinal

end BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage



/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.split_filterMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.split_filterMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.count_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.count_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.ordinal_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.ordinal_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.path_split' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.path_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.accept_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.accept_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.bundle_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.bundle_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.acceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.acceptance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.accept_count_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.accept_count_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.bundle_count_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.bundle_count_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.earlier_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage.earlier_bundle
