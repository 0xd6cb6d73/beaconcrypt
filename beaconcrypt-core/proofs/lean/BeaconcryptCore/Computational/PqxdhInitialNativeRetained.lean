import BeaconcryptCore.Computational.PqxdhInitialNativePath
import BeaconcryptCore.Computational.RawCtxPendingRetainedExecution
import BeaconcryptCore.Computational.RawCtxSelectiveReplay

/-!
The full original pending source retains external preparation, initializer, application and publication effects when its private cache is interpreted through a retained lookup. Saturation preserves the complete logged execution; evaluated retained-view equalities project private table/cursor/log only after completion. Support replay uses the actual final cache and is not a probability or query-cost equality.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeRetained
open PqxdhJointKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhInitialNativeLog PqxdhInitialBeaconAmbient
open RawCtxSelectiveChainGame RawCtxSelectedParentTable RawCtxCursorLineage
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every actual full-interface callback preserves or advances the private cursor, while all external effects retain it exactly. -/
theorem step_depth (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).Range query × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((PqxdhInitialNativeLog.handler source writer stage external query).run state)) :
    state.1.1.2.2.depth ≤ result.2.1.1.2.2.depth := by
  cases query with
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact Nat.le_refl _
  | inl query =>
      rw [live_handler] at supported
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp,
        support_map, Set.mem_image] at supported
      obtain ⟨reply, ⟨actual, reached, rfl⟩, rfl⟩ := supported
      change state.1.1.2.2.depth ≤ actual.2.2.2.depth
      cases addressEq : RawCtxSelectedFamilyContext.queryAddress query with
      | none =>
          rw [RawCtxPendingNonKdfStore.callback_store source writer stage query addressEq state.1.1 actual reached]
      | some address =>
          obtain ⟨output, same⟩ := RawCtxPendingParentCallbacks.kdf_state source writer stage query address addressEq state.1.1 actual reached
          rw [same, advance_depth]
          exact Nat.le_add_right _ _

/-- A full callback past the selected stage uses the same real memoized backend, including all external effects. -/
theorem step_saturated (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C) (past : stage ≤ state.1.1.2.2.depth) :
    (PqxdhInitialNativeLog.handler source writer stage external query).run state =
      (PqxdhInitialNativeLog.handler source writer 0 external query).run state := by
  cases query with
  | inr query => rfl
  | inl query =>
      have same := RawCtxPendingRetainedExecution.saturated source writer stage
        (((RawCtxPendingSelectiveFamily.Spec S B).query query) : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _) state.1.1 past
      simp only [simulateQ_spec_query] at same
      rw [live_handler, live_handler]
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run]
      dsimp only [StateT.run] at same
      rw [same]


/-- Pointwise equality on an invariant is preserved by the complete adaptive computation. -/
theorem program_same {δ T V : Type} {oracle : OracleSpec δ}
    (left right : QueryImpl oracle (StateT T ProbComp)) (valid : T → Prop)
    (same : ∀ q s, valid s → (left q).run s = (right q).run s)
    (preserved : ∀ q s, valid s → ∀ r ∈ support ((right q).run s), valid r.2)
    (client : OracleComp oracle V) (state : T) (initial : valid state) :
    (simulateQ left client).run state = (simulateQ right client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [same query state initial]
      apply bind_congr_of_forall_mem_support
      intro reply reached
      exact ih reply.1 reply.2 (preserved query state initial reply reached)

/-- The full original source after the selected stage keeps all ambient, root-cache, private-cache and chronological-log effects. -/
theorem saturated (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) (past : stage ≤ state.1.1.2.2.depth) :
    (simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state =
      (simulateQ (PqxdhInitialNativeLog.handler source writer 0 external) client).run state := by
  exact program_same _ _ (fun state : PqxdhInitialNativeLog.State A N C => stage ≤ state.1.1.2.2.depth)
    (fun query state valid => step_saturated source writer stage external query state valid)
    (fun query state valid result reached => valid.trans (step_depth source writer 0 external query state result reached))
    client state past

/-- The stage-zero backend only records the value already selected by its retained lookup. -/
theorem zero_view {δ T V : Type} {oracle : OracleSpec δ}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl oracle (StateT T ProbComp))
    (client : OracleComp (oracle + JointKdfRO) V) (state : T × Store)
    (result : V × (T × Store))
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveChainGame.handler source 0 other) client).run state)) :
    view (productionStream source.crypto) result.2.2.1 = view (productionStream source.crypto) state.2.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      cases query with
      | inl query =>
          simp only [simulateQ_bind, simulateQ_spec_query] at supported
          rw [StateT.run_bind] at supported
          simp only [RawCtxSelectiveChainGame.handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
          obtain ⟨reply, _, tail⟩ := supported
          exact ih reply.1 (reply.2, state.2) result tail
      | inr request =>
          simp only [simulateQ_bind, simulateQ_spec_query] at supported
          rw [StateT.run_bind] at supported
          simp only [RawCtxSelectiveChainGame.handler, StateT.run, private_zero] at supported
          have memo := RawCtxRetainedTable.memo_view source state.2.1 request
          dsimp only [StateT.run] at memo
          rw [memo] at supported
          simp only [map_pure, pure_bind] at supported
          exact (ih _ _ result supported).trans (RawCtxRetainedTable.view_stable _ _ _)


/-- The actual enriched pending callback preserves the complete retained view at stage zero. -/
theorem pending_view (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxPendingSelectiveFamily.State A) (result : Result × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (RawCtxPendingSelectiveFamily.handler source writer 0) client).run state)) :
    view (productionStream source.crypto) result.2.2.1 = view (productionStream source.crypto) state.2.1 := by
  simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.backend,
    RawCtxPendingBackendInterpretation.program_compose] at supported
  exact zero_view source (RawCtxProtocolBackend.backend source writer)
    (simulateQ RawCtxPendingRetainedExecution.compiler client) state result supported

/-- Every supported complete-interface stage-zero callback retains the same lookup, including all external effects. -/
theorem step_view (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((PqxdhInitialNativeLog.handler source writer 0 external query).run state)) :
    view (productionStream source.crypto) result.2.1.1.2.1 = view (productionStream source.crypto) state.1.1.2.1 := by
  cases query with
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      rfl
  | inl query =>
      rw [live_handler] at supported
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp,
        support_map, Set.mem_image] at supported
      obtain ⟨reply, ⟨actual, reached, rfl⟩, rfl⟩ := supported
      exact pending_view source writer
        (((RawCtxPendingSelectiveFamily.Spec S B).query query) : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _)
        state.1.1 actual (by simpa only [simulateQ_spec_query, StateT.run] using reached)

abbrev RetainedState (A N C : Type) := RawCtxSharedPrimitive.SharedState A × (N × C)

def project (state : PqxdhInitialNativeLog.State A N C) : RetainedState A N C := (state.1.1.1, state.2)

/-- Only private table, cursor and chronological log are erased. Every external callback keeps its original ambient and root-cache effects. -/
noncomputable def retained (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C)) :
    QueryImpl (Spec extra RatchetChain I D K X Response Shared S B) (StateT (RetainedState A N C) ProbComp)
  | .inl query => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxPendingRetainedExecution.retained source writer prior query).run state.1
  | .inr query => fun state =>
      (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
        ((external query (state.1, state.2.1)).run state.2.2)

/-- Erasing only completed private bookkeeping from one stage-zero callback gives the exact retained callback. -/
theorem step_retained (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C) :
    (fun result => (result.1, project result.2)) <$>
      (PqxdhInitialNativeLog.handler source writer 0 external query).run state =
      (retained source writer (view (productionStream source.crypto) state.1.1.2.1) external query).run (project state) := by
  cases query with
  | inr query =>
      rw [external_handler]
      simp only [retained, StateT.run, project, Functor.map_map]
  | inl query =>
      have same := RawCtxPendingRetainedExecution.logged_retained source writer 0
        (((RawCtxPendingSelectiveFamily.Spec S B).query query) : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _)
        state.1 (Nat.zero_le _)
      simp only [simulateQ_spec_query] at same
      rw [live_handler]
      simpa only [Functor.map_map, retained, StateT.run, project] using
        congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work) same

/-- Exact callback projection with a stable retained parameter extends to the complete adaptive program. -/
theorem program_project {δ T U V Key : Type} {oracle : OracleSpec δ}
    (impl : QueryImpl oracle (StateT T ProbComp)) (other : Key → QueryImpl oracle (StateT U ProbComp))
    (key : T → Key) (erase : T → U)
    (step : ∀ q s, (fun r => (r.1, erase r.2)) <$> (impl q).run s = (other (key s) q).run (erase s))
    (stable : ∀ q s, ∀ r ∈ support ((impl q).run s), key r.2 = key s)
    (client : OracleComp oracle V) (state : T) :
    (fun r => (r.1, erase r.2)) <$> (simulateQ impl client).run state =
      (simulateQ (other (key state)) client).run (erase state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← step query state]
      simp only [bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro reply reached
      rw [ih, stable query state reply reached]

/-- Past the selected stage, the entire actual source equals its retained lookup execution after erasing only final private bookkeeping. -/
theorem retained_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) (past : stage ≤ state.1.1.2.2.depth) :
    (fun result => (result.1, project result.2)) <$>
      (simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state =
      (simulateQ (retained source writer (view (productionStream source.crypto) state.1.1.2.1) external) client).run (project state) := by
  rw [saturated source writer stage external client state past]
  exact program_project _ (fun prior => retained (S := S) (B := B) source writer prior external) (fun state : PqxdhInitialNativeLog.State A N C => view (productionStream source.crypto) state.1.1.2.1)
    project (step_retained (S := S) (B := B) source writer external) (step_view (S := S) (B := B) source writer external) client state

/-- The same full result and ambient state replay under any table extending this execution's final bindings; all initial full responses remain present. -/
theorem replay_larger {δ State Result : Type} {spec : OracleSpec δ} (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State × Store)
    (result : Result × (State × Store))
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveChainGame.handler source stage other) client).run state))
    (finalTable : RawCtxKdfRequestTable.Table) (larger : Extends result.2.2.1 finalTable) :
    Extends state.2.1 result.2.2.1 ∧
      (result.1, result.2.1) ∈ support ((simulateQ
        (RawCtxRetainedTable.viewImpl (view (productionStream source.crypto) finalTable) other) client).run state.1) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨fun _ _ known => known, by simp⟩
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      rw [StateT.run_bind] at supported
      simp only [RawCtxSelectiveChainGame.handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, actual, tail⟩ := supported
      have later := ih reply.1 (reply.2, state.2) result tail larger
      refine ⟨later.1, ?_⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RawCtxRetainedTable.viewImpl, mem_support_bind_iff]
      exact ⟨reply, actual, later.2⟩
    | inr request =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      rw [StateT.run_bind] at supported
      simp only [RawCtxSelectiveChainGame.handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, actual, tail⟩ := supported
      have later := ih reply.1 (state.1, reply.2) result tail larger
      have extension := private_extends source stage request state.2 reply actual
      have recorded : reply.2.1 request = some reply.1 := by
        rw [private_state source stage request state.2 reply actual]
        simp
      have retained := larger request reply.1 (later.1 request reply.1 recorded)
      refine ⟨fun address output known => later.1 address output (extension address output known), ?_⟩
      simpa only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        RawCtxRetainedTable.viewImpl, StateT.run_pure, pure_bind, view, retained, Option.getD_some] using later.2


/-- The same actual enriched primitive schedule replays under any retained table extending its own final bindings. -/
theorem pending_larger (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxPendingSelectiveFamily.State A) (result : Result × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state))
    (finalTable : RawCtxKdfRequestTable.Table) (larger : Extends result.2.2.1 finalTable) :
    (result.1, result.2.1) ∈ support ((simulateQ
      (RawCtxPendingRetainedExecution.retained source writer (view (productionStream source.crypto) finalTable)) client).run state.1) := by
  simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.backend,
    RawCtxPendingBackendInterpretation.program_compose] at supported
  have replay := (replay_larger source stage (RawCtxProtocolBackend.backend source writer)
    (simulateQ RawCtxPendingRetainedExecution.compiler client) state result supported finalTable larger).2
  simpa only [RawCtxPendingRetainedExecution.retained, RawCtxPendingBackendInterpretation.program_compose,
    RawCtxPendingRetainedExecution.compiler] using replay

/-- Every supported complete-interface callback replays under a retained extension of its actual post-cache, preserving all original ambient effects. -/
theorem step_replay (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((PqxdhInitialNativeLog.handler source writer stage external query).run state))
    (finalTable : RawCtxKdfRequestTable.Table) (larger : Extends result.2.1.1.2.1 finalTable) :
    (result.1, project result.2) ∈ support
      ((retained source writer (view (productionStream source.crypto) finalTable) external query).run (project state)) := by
  cases query with
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      simp only [retained, StateT.run, support_map, Set.mem_image]
      exact ⟨reply, actual, rfl⟩
  | inl query =>
      rw [live_handler] at supported
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp,
        support_map, Set.mem_image] at supported
      obtain ⟨reply, ⟨actual, reached, rfl⟩, rfl⟩ := supported
      have replay := pending_larger source writer stage
        (((RawCtxPendingSelectiveFamily.Spec S B).query query) : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _)
        state.1.1 actual (by simpa only [simulateQ_spec_query, StateT.run] using reached) finalTable larger
      simp only [retained, StateT.run, support_map, Set.mem_image]
      exact ⟨(actual.1, actual.2.1), by simpa only [simulateQ_spec_query, StateT.run, project] using replay, rfl⟩

/-- Source callback replay and immutable earlier bindings extend through the complete supported adaptive program. -/
theorem program_replay {δ T U V : Type} {oracle : OracleSpec δ}
    (impl : QueryImpl oracle (StateT T ProbComp))
    (other : RawCtxKdfRequestTable.Table → QueryImpl oracle (StateT U ProbComp))
    (cache : T → RawCtxKdfRequestTable.Table) (erase : T → U)
    (extension : ∀ q s, ∀ r ∈ support ((impl q).run s), Extends (cache s) (cache r.2))
    (replay : ∀ q s, ∀ r ∈ support ((impl q).run s), ∀ finalTable, Extends (cache r.2) finalTable →
      (r.1, erase r.2) ∈ support ((other finalTable q).run (erase s)))
    (client : OracleComp oracle V) (state : T) (result : V × T)
    (supported : result ∈ support ((simulateQ impl client).run state))
    (finalTable : RawCtxKdfRequestTable.Table) (larger : Extends (cache result.2) finalTable) :
    Extends (cache state) (cache result.2) ∧
      (result.1, erase result.2) ∈ support ((simulateQ (other finalTable) client).run (erase state)) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨fun _ _ known => known, by simp⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      have later := ih reply.1 reply.2 result tail larger
      have first := extension query state reply head
      refine ⟨fun address output known => later.1 address output (first address output known), ?_⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(reply.1, erase reply.2), replay query state reply head finalTable
        (fun address output known => larger address output (later.1 address output known)), later.2⟩

/-- The actual full source result and every ambient effect replay under this execution's own final cache; every earlier binding remains present. This is support-only replay. -/
theorem complete_replay (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) (result : Result × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state)) :
    Extends state.1.1.2.1 result.2.1.1.2.1 ∧
      (result.1, project result.2) ∈ support ((simulateQ
        (retained source writer (view (productionStream source.crypto) result.2.1.1.2.1) external) client).run (project state)) := by
  exact program_replay _ (fun finalTable => retained (S := S) (B := B) source writer (view (productionStream source.crypto) finalTable) external)
    (fun state : PqxdhInitialNativeLog.State A N C => state.1.1.2.1) project
    (PqxdhInitialNativePath.step_extends (S := S) (B := B) source writer stage external)
    (step_replay (S := S) (B := B) source writer stage external) client state result supported _ (fun _ _ known => known)

/-- A lookup preserved by every supported callback remains unchanged after the complete adaptive client. -/
theorem program_stable {δ T V Key : Type} {oracle : OracleSpec δ}
    (impl : QueryImpl oracle (StateT T ProbComp)) (key : T → Key)
    (stable : ∀ q s, ∀ r ∈ support ((impl q).run s), key r.2 = key s)
    (client : OracleComp oracle V) (state : T) (result : V × T)
    (supported : result ∈ support ((simulateQ impl client).run state)) : key result.2 = key state := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact (ih reply.1 reply.2 result tail).trans (stable query state reply head)

/-- The final actual cache of a saturated complete source has exactly the initial retained lookup, although its domain may grow. -/
theorem final_view (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) (past : stage ≤ state.1.1.2.2.depth)
    (result : Result × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state)) :
    view (productionStream source.crypto) result.2.1.1.2.1 = view (productionStream source.crypto) state.1.1.2.1 := by
  rw [saturated source writer stage external client state past] at supported
  exact program_stable _ (fun state : PqxdhInitialNativeLog.State A N C => view (productionStream source.crypto) state.1.1.2.1)
    (step_view (S := S) (B := B) source writer external) client state result supported

/-- Every actually cached final response in a saturated source equals the original retained lookup at that queried address; no unqueried-address premise is needed. -/
theorem final_binding (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : PqxdhInitialNativeLog.State A N C) (past : stage ≤ state.1.1.2.2.depth)
    (result : Result × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage external) client).run state))
    (address : JointKdfAddress) (output : FullOutput) (found : result.2.1.1.2.1 address = some output) :
    view (productionStream source.crypto) state.1.1.2.1 address = output := by
  rw [← final_view source writer stage external client state past result supported]
  simp only [view, found, Option.getD_some]

end BeaconcryptCore.Computational.PqxdhInitialNativeRetained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_saturated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_saturated

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_same

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.saturated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.saturated

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.zero_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.zero_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.pending_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.pending_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_retained

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.retained_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.retained_run

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.replay_larger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.replay_larger

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.pending_larger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.pending_larger

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.step_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.complete_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.complete_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.program_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.final_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.final_view

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRetained.final_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRetained.final_binding
