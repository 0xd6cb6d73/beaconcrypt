import BeaconcryptCore.Computational.PqxdhInitialNativeChildDraw
import BeaconcryptCore.Computational.RawCtxPublishedLineage

/-!
The finite native checker is appended after the original source client, before completed private bookkeeping is projected. On an already cached published path it reads only existing responses and preserves every original ambient field and private table. Its returned lineage is thus available to the ordinary final observation and to the full-interface deferred-draw comparison. Checker requests have a separate syntactic bill.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf
open RawCtxSelectiveChainGame RawCtxSelectedParentTable RawCtxKdfRequestTable RawCtxFiniteLineageCheck
variable {ι T Result : Type} {spec : OracleSpec ι}

def request (input : RatchetChain) : JointKdfAddress := address (RawCtxChainSend.nativeRequest input)

noncomputable def forward : QueryImpl (RawCtxFiniteLineageCheck.Spec RatchetChain) (OracleComp (spec + JointKdfRO)) :=
  fun input => (RawCtxInterpretedReceive.decodeResponse ∘ fullResponse) <$>
    ((spec + JointKdfRO).query (.inr (request input)) : OracleComp (spec + JointKdfRO) FullOutput)

noncomputable def checker (n : Nat) (input : RatchetChain) : OracleComp (spec + JointKdfRO) (List RatchetChain) :=
  simulateQ forward (RawCtxFiniteLineageCheck.program nativeKey n input)

/-- A concrete 32-byte root uses exactly the source ratchet address. -/
theorem request_concrete (root : RootOutput) :
    request (RawCtxFreshChainCut.concreteChain root) = RawCtxFirstParentRisk.inputAddress root := by
  have info : PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  simp only [request, address, RawCtxChainSend.nativeRequest, info]
  change (⟨Pqxdh.INFO_R, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain root)).toList⟩ : JointKdfAddress) = _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  rfl

/-- A fixed retained private view returns the complete native lineage without any ambient effects. -/
theorem retained (prior : Prior) (other : QueryImpl spec (StateT T ProbComp)) (n : Nat) (input : RatchetChain) :
    simulateQ (RawCtxRetainedTable.viewImpl prior other) (checker (spec := spec) n input) =
      pure (trace nativeKey (RawCtxPublishedLineage.step prior) n input) := by
  rw [checker, ← QueryImpl.simulateQ_compose]
  exact RawCtxFiniteLineageCheck.evaluate nativeKey (RawCtxPublishedLineage.step prior) n input

noncomputable def Cached (table : Table) (prior : Prior) : Nat → RatchetChain → Prop
  | 0, input => table (request input) = some (prior (request input))
  | n + 1, input => table (request input) = some (prior (request input)) ∧
      Cached table prior n (RawCtxPublishedLineage.step prior input).1

/-- Every checker lookup on an existing lineage preserves the original table and all ambient state; only the private cursor may advance. -/
theorem cached (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT T ProbComp)) (table : Table) (prior : Prior)
    (n : Nat) (input : RatchetChain) (known : Cached table prior n input)
    (state : T) (cursor : Cursor) :
    (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
      (simulateQ (handler source stage other) (checker (spec := spec) n input)).run (state, (table, cursor)) =
      pure (trace nativeKey (RawCtxPublishedLineage.step prior) n input, (state, table)) := by
  induction n generalizing input cursor with
  | zero =>
    simp only [Cached] at known
    simp only [checker, RawCtxFiniteLineageCheck.program, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, forward, simulateQ_map, StateT.run_bind, StateT.run_map, StateT.run_pure,
      handler]
    simp only [StateT.run, private_hit source stage (request input) (table, cursor) _ known,
      cache_hit table (request input) _ known, pure_bind, map_pure]
    rfl
  | succ n ih =>
    simp only [Cached] at known
    simp only [checker, RawCtxFiniteLineageCheck.program, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, forward, simulateQ_map, StateT.run_bind, StateT.run_map, StateT.run_pure,
      handler]
    simp only [StateT.run, private_hit source stage (request input) (table, cursor) _ known.1,
      cache_hit table (request input) _ known.1, pure_bind, map_pure, bind_pure_comp, Functor.map_map]
    simpa only [Functor.map_map, map_pure, trace, checker, RawCtxPublishedLineage.step,
      RawCtxFunctionalFamily.execute, request, Function.comp_def, StateT.run] using congrArg
      (fun work : ProbComp (List RatchetChain × (T × Table)) =>
        (fun result => (input :: result.1, result.2)) <$> work)
      (ih _ known.2 (advance cursor (request input) (prior (request input))))

private theorem walk_front (table : Table) (n : Nat) (root : RootOutput) :
    RawCtxCursorLineage.walk table (n + 1) root = (do
      let output ← table (RawCtxFirstParentRisk.inputAddress root)
      let rest ← RawCtxCursorLineage.walk table n (PqxdhOrderedChainHybrids.nextChain output)
      pure (root :: rest.1, rest.2)) := by
  induction n with
  | zero => simp [RawCtxCursorLineage.walk]
  | succ n ih =>
    rw [RawCtxCursorLineage.walk, ih]
    simp only [RawCtxCursorLineage.walk, bind_assoc, pure_bind]
    rfl

/-- The checker cache condition follows from the protocol's existing finite cached path, without imposing any restriction on unqueried fallback addresses. -/
theorem walk_cached (table : Table) (fallback : Prior) (n : Nat) (root : RootOutput)
    (result : List RootOutput × RootOutput)
    (walked : RawCtxCursorLineage.walk table (n + 1) root = some result) :
    Cached table (view fallback table) n (RawCtxFreshChainCut.concreteChain root) := by
  induction n generalizing root result with
  | zero =>
    rw [walk_front] at walked
    cases found : table (RawCtxFirstParentRisk.inputAddress root) with
    | none => simp [found] at walked
    | some output =>
      have present : table (request (RawCtxFreshChainCut.concreteChain root)) = some output :=
        by
          rw [request_concrete root]
          exact found
      simp only [Cached, view, present, Option.getD_some]
  | succ n ih =>
    rw [walk_front] at walked
    cases found : table (RawCtxFirstParentRisk.inputAddress root) with
    | none => simp [found] at walked
    | some output =>
      cases rest : RawCtxCursorLineage.walk table (n + 1) (PqxdhOrderedChainHybrids.nextChain output) with
      | none => simp [found, rest] at walked
      | some reached =>
        have present : table (request (RawCtxFreshChainCut.concreteChain root)) = some output :=
          by
          rw [request_concrete root]
          exact found
        constructor
        · simp only [view, present, Option.getD_some]
        · rw [RawCtxPublishedLineage.step_next]
          simp only [view, found, Option.getD_some]
          exact ih _ reached rest

/-- The actual cached source walk discharges the entire checker condition, preserving every ambient field and the source table. -/
theorem cached_walk (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT T ProbComp)) (table : Table) (n : Nat) (root : RootOutput)
    (result : List RootOutput × RootOutput)
    (walked : RawCtxCursorLineage.walk table (n + 1) root = some result) (state : T) (cursor : Cursor) :
    (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
      (simulateQ (handler source stage other) (checker (spec := spec) n (RawCtxFreshChainCut.concreteChain root))).run
        (state, (table, cursor)) =
      pure (trace nativeKey (RawCtxPublishedLineage.step (view (productionStream source.crypto) table)) n
        (RawCtxFreshChainCut.concreteChain root), (state, table)) :=
  cached source stage other table _ n _ (walk_cached table _ n root result walked) state cursor

/-- The appended native checker has exactly the finite all-reply reservation; it invokes no external callback. -/
theorem queries (n : Nat) (input : RatchetChain) :
    (checker (spec := spec) n input).IsTotalQueryBound (n + 1) := by
  induction n generalizing input with
  | zero =>
    simp only [checker, program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, forward, bind_map_left,
      isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => by trivial⟩
  | succ n ih =>
    simp only [checker, program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, forward, bind_map_left,
      isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun reply => ?_⟩
    simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, Nat.add_sub_cancel, checker] using
      ih ((RawCtxInterpretedReceive.decodeResponse ∘ fullResponse) reply).1

noncomputable def appended (client : OracleComp (spec + JointKdfRO) Result) (gate : Result → Bool)
    (n : Nat) (root : RootOutput) : OracleComp (spec + JointKdfRO) (Result × Option (List RatchetChain)) := do
  let result ← client
  if gate result then
    let lineage ← checker n (RawCtxFreshChainCut.concreteChain root)
    pure (result, some lineage)
  else pure (result, none)

/-- Appending the cached checker computes the final source table's original finite lineage before erasing bookkeeping, retaining the entire original result and ambient state. -/
theorem appended_cached (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT T ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (gate : Result → Bool) (n : Nat) (root : RootOutput) (state : T × Store)
    (published : ∀ result ∈ support ((simulateQ (handler source stage other) client).run state),
      gate result.1 = true → ∃ path, RawCtxCursorLineage.walk result.2.2.1 (n + 1) root = some path) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler source stage other) (appended client gate n root)).run state =
      (fun result => ((result.1, if gate result.1 then some
        (trace nativeKey (RawCtxPublishedLineage.step (view (productionStream source.crypto) result.2.2.1)) n
          (RawCtxFreshChainCut.concreteChain root)) else none), result.2.1)) <$>
        (simulateQ (handler source stage other) client).run state := by
  simp only [appended, simulateQ_bind, StateT.run_bind, ← bind_pure_comp, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro result reached
  cases good : gate result.1 with
  | false => simp only [Bool.false_eq_true, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
  | true =>
    obtain ⟨path, walked⟩ := published result reached good
    simp only [if_true, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    have read := cached_walk source stage other result.2.2.1 n root path walked result.2.1 result.2.2.2
    simpa only [Functor.map_map, map_pure, Prod.eta] using congrArg
      (fun work : ProbComp (List RatchetChain × (T × Table)) =>
        (fun reply => ((result.1, some reply.1), reply.2.1)) <$> work) read

/-- The same appended client under an early retained view exposes the complete lineage through its result, while keeping every original ambient effect. -/
theorem appended_retained (prior : Prior) (other : QueryImpl spec (StateT T ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (gate : Result → Bool)
    (n : Nat) (root : RootOutput) (state : T) :
    (simulateQ (RawCtxRetainedTable.viewImpl prior other) (appended client gate n root)).run state =
      (fun result => ((result.1, if gate result.1 then some
        (trace nativeKey (RawCtxPublishedLineage.step prior) n (RawCtxFreshChainCut.concreteChain root))
        else none), result.2)) <$>
        (simulateQ (RawCtxRetainedTable.viewImpl prior other) client).run state := by
  simp only [appended, simulateQ_bind, StateT.run_bind, ← bind_pure_comp]
  apply bind_congr
  intro result
  cases gate result.1 with
  | false => simp only [Bool.false_eq_true, if_false, simulateQ_pure, StateT.run_pure]
  | true => simp only [if_true, simulateQ_bind, simulateQ_pure, retained, pure_bind, StateT.run_pure]

/-- The complete source lineage observation commutes with the one remaining deferred full76 draw, using the actual source's publication cache witness and preserving every result and ambient field. -/
theorem appended_uniform (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl spec (StateT T ProbComp)) (client : OracleComp (spec + JointKdfRO) Result)
    (gate : Result → Bool) (n : Nat) (root : RootOutput) (state : T) (table : Table) (cursor : Cursor)
    (missing : table (cursorAddress cursor) = none)
    (published : ∀ result ∈ support ((simulateQ (handler source (cursor.depth + 1) other) client).run (state, (table, cursor))),
      gate result.1 = true → ∃ path, RawCtxCursorLineage.walk result.2.2.1 (n + 1) root = some path) :
    𝒮[(fun result => ((result.1, if gate result.1 then some
      (trace nativeKey (RawCtxPublishedLineage.step (view (productionStream source.crypto) result.2.2.1)) n
        (RawCtxFreshChainCut.concreteChain root)) else none), result.2.1)) <$>
      (simulateQ (handler source (cursor.depth + 1) other) client).run (state, (table, cursor))] =
    𝒮[($ᵗ FullOutput) >>= fun output =>
      let prior := view (productionStream source.crypto) (table.cacheQuery (cursorAddress cursor) output)
      (fun result => ((result.1, if gate result.1 then some
        (trace nativeKey (RawCtxPublishedLineage.step prior) n (RawCtxFreshChainCut.concreteChain root))
        else none), result.2)) <$>
        (simulateQ (RawCtxRetainedTable.viewImpl prior other) client).run state] := by
  rw [← appended_cached source (cursor.depth + 1) other client gate n root (state, (table, cursor)) published]
  rw [RawCtxSelectiveSingleDraw.single_uniform source other (appended client gate n root) state table cursor missing]
  exact evalSPMF_bind_congr' ($ᵗ FullOutput) (fun output => congrArg evalSPMF
    (appended_retained (view (productionStream source.crypto) (table.cacheQuery (cursorAddress cursor) output))
      other client gate n root state))

/-- The analysis continuation explicitly reserves its full finite checker after the original client, under every possible callback reply. -/
theorem appended_queries (client : OracleComp (spec + JointKdfRO) Result) (gate : Result → Bool)
    (n : Nat) (root : RootOutput) (q : Nat) (bounded : client.IsTotalQueryBound q) :
    (appended client gate n root).IsTotalQueryBound (q + (n + 1)) := by
  apply isTotalQueryBound_bind bounded
  intro result
  cases gate result with
  | false => simp only [Bool.false_eq_true, if_false]; trivial
  | true =>
    simpa only [if_true, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      queries (spec := spec) n (RawCtxFreshChainCut.concreteChain root)

variable {I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem logged_flat (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) :
    (simulateQ (handler source stage (PqxdhInitialNativeChildDraw.other source writer external))
      (simulateQ PqxdhInitialNativeChildDraw.compiler client)).run
        (PqxdhInitialNativeChildDraw.pack (PqxdhInitialNativeLog.erase state)) =
      (fun result => (result.1, PqxdhInitialNativeChildDraw.pack (PqxdhInitialNativeLog.erase result.2))) <$>
        (simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state := by
  rw [PqxdhInitialNativeChildDraw.bare_program, ← PqxdhInitialNativeLog.program_projection]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- The full original logged source retains its gated lineage observation through the exact deferred child draw; source support and every external state field are transported by the literal compiler. -/
theorem logged_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B) Result)
    (gate : Result → Bool) (n : Nat) (root : RootOutput) (state : PqxdhInitialNativeLog.State A N C)
    (missing : state.1.1.2.1 (cursorAddress state.1.1.2.2) = none)
    (published : ∀ result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer
        (state.1.1.2.2.depth + 1) external) client).run state),
      gate result.1 = true → ∃ path, RawCtxCursorLineage.walk result.2.1.1.2.1 (n + 1) root = some path) :
    𝒮[(fun result => ((result.1, if gate result.1 then some
      (trace nativeKey (RawCtxPublishedLineage.step (view (productionStream source.crypto) result.2.1.1.2.1)) n
        (RawCtxFreshChainCut.concreteChain root)) else none), PqxdhInitialNativeRetained.project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer (state.1.1.2.2.depth + 1) external) client).run state] =
    𝒮[($ᵗ FullOutput) >>= fun output =>
      let prior := view (productionStream source.crypto) (state.1.1.2.1.cacheQuery (cursorAddress state.1.1.2.2) output)
      (fun result => ((result.1, if gate result.1 then some
        (trace nativeKey (RawCtxPublishedLineage.step prior) n (RawCtxFreshChainCut.concreteChain root))
        else none), result.2)) <$>
        (simulateQ (PqxdhInitialNativeRetained.retained source writer prior external) client).run
          (PqxdhInitialNativeRetained.project state)] := by
  have same := logged_flat source writer (state.1.1.2.2.depth + 1) external client state
  have cachedSource : ∀ result ∈ support ((simulateQ
      (handler source (state.1.1.2.2.depth + 1) (PqxdhInitialNativeChildDraw.other source writer external))
      (simulateQ PqxdhInitialNativeChildDraw.compiler client)).run
        (PqxdhInitialNativeChildDraw.pack (PqxdhInitialNativeLog.erase state))),
      gate result.1 = true → ∃ path, RawCtxCursorLineage.walk result.2.2.1 (n + 1) root = some path := by
    intro result reached good
    rw [same, support_map] at reached
    obtain ⟨original, supported, rfl⟩ := reached
    exact published original supported good
  have equality := appended_uniform source (PqxdhInitialNativeChildDraw.other source writer external)
    (simulateQ PqxdhInitialNativeChildDraw.compiler client) gate n root
    (PqxdhInitialNativeRetained.project state) state.1.1.2.1 state.1.1.2.2 missing cachedSource
  dsimp only [PqxdhInitialNativeChildDraw.pack, PqxdhInitialNativeLog.erase, PqxdhInitialNativeRetained.project] at same equality ⊢
  rw [same] at equality
  simpa only [Functor.map_map, ← QueryImpl.simulateQ_compose, PqxdhInitialNativeChildDraw.retained_compiler] using equality

end BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.request_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.request_concrete

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.retained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.cached

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.walk_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.walk_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.cached_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.cached_walk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.appended_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.logged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck.logged_uniform
