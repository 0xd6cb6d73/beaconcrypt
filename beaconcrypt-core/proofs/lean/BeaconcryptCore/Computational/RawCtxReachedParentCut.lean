import BeaconcryptCore.Computational.RawCtxPendingReceivePrefix
import BeaconcryptCore.Computational.RawCtxSelectedPendingCut
import BeaconcryptCore.Computational.RawCtxRetainedTable

/-!
The original pending receive queries use one concrete full76 table and the original opening effects. Source memoization erases only the private table; chronological scanning retains the complete reached table and auxiliary state. Hits and misses remain separate actual callback branches. A uniform miss is an explicit comparison draw, not an assumption that source HKDF is uniform. The private stop and table are not public or live-reveal capabilities.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxReachedParentCut
open RawCtxChainReceive RawCtxInterpretedOpening RawCtxPendingReceivePrefix
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Spec (Context Plaintext : Type) :=
  RawCtxPendingReceiveQueries.Spec RatchetChain RatchetChain RatchetMaterial Context Plaintext
abbrev OpenSpec (Context Plaintext : Type) :=
  Opening RatchetChain RatchetChain RatchetMaterial Context →ₒ core.option.Option Plaintext
abbrev TableSpec (Context Plaintext : Type) := OpenSpec Context Plaintext + JointKdfRO

noncomputable def compiler {Context Plaintext : Type} :
    QueryImpl (Spec Context Plaintext) (OracleComp (TableSpec Context Plaintext))
  | .inl pending => (RawCtxInterpretedReceive.decodeResponse ∘ RawCtxKdfRequestTable.fullResponse) <$>
      (TableSpec Context Plaintext).query (.inr (RawCtxSelectedPendingCut.requestAddress pending.request))
  | .inr opening => (TableSpec Context Plaintext).query (.inl opening)

noncomputable def tableHandler {Context Plaintext Auxiliary : Type}
    (kdf : QueryImpl JointKdfRO (StateT RawCtxKdfRequestTable.Table ProbComp))
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp)) :
    QueryImpl (TableSpec Context Plaintext) (StateT (Auxiliary × RawCtxKdfRequestTable.Table) ProbComp)
  | .inl query => fun state => do
      let result ← (other query).run state.1
      pure (result.1, (result.2, state.2))
  | .inr address => fun state => do
      let result ← (kdf address).run state.2
      pure (result.1, (state.1, result.2))

noncomputable def handler {Context Plaintext Auxiliary : Type}
    (kdf : QueryImpl JointKdfRO (StateT RawCtxKdfRequestTable.Table ProbComp))
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec Context Plaintext) (StateT (Auxiliary × RawCtxKdfRequestTable.Table) ProbComp) :=
  tableHandler kdf other ∘ₛ compiler

noncomputable def sourceHandler {Context Plaintext Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec Context Plaintext) (StateT Auxiliary ProbComp) :=
  RawCtxKdfRequestTable.directImpl source other ∘ₛ compiler

noncomputable def viewHandler {Context Plaintext Auxiliary : Type}
    (prior : Prior) (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec Context Plaintext) (StateT Auxiliary ProbComp) :=
  RawCtxRetainedTable.viewImpl prior other ∘ₛ compiler

/-- The source table is the original fixed-function memoization, including all earlier bindings and opening effects. -/
theorem source_table {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (client : OracleComp (Spec Context Plaintext) Result) (state : Auxiliary)
    (table : RawCtxKdfRequestTable.Table) (consistent : RawCtxKdfRequestTable.Consistent source table) :
    (simulateQ (sourceHandler source other) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other) client).run (state, table) := by
  have same : tableHandler (RawCtxKdfRequestTable.memoImpl source) other = RawCtxKdfRequestTable.tableImpl source other := by
    funext query state
    cases query <;> rfl
  simpa only [sourceHandler, handler, QueryImpl.simulateQ_compose, same] using
    RawCtxKdfRequestTable.table_complete source other (simulateQ compiler client) state table consistent

/-- The selected KDF callback evaluates the address carried by that original pending request, then decodes the same complete response and retains both state components. -/
theorem kdf_run {Context Plaintext Auxiliary : Type}
    (kdf : QueryImpl JointKdfRO (StateT RawCtxKdfRequestTable.Table ProbComp))
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (state : Auxiliary × RawCtxKdfRequestTable.Table) :
    ((handler kdf other (.inl pending)).run state) =
      (do let result ← (kdf (RawCtxSelectedPendingCut.requestAddress pending.request)).run state.2
          pure (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1), (state.1, result.2))) := by
  simp only [handler, QueryImpl.compose, compiler, simulateQ_map]
  rw [StateT.run_map]
  simp [tableHandler, StateT.run]

/-- Scanning and then finishing the same source memo execution retains all original callback effects, including completion before selection. -/
theorem source_scan {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (client : OracleComp (Spec Context Plaintext) Result) (state : Auxiliary)
    (table : RawCtxKdfRequestTable.Table) (consistent : RawCtxKdfRequestTable.Consistent source table)
    (index : Nat) :
    (simulateQ (sourceHandler source other) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (scan (handler (RawCtxKdfRequestTable.memoImpl source) other) client index (state, table) >>=
          finish (handler (RawCtxKdfRequestTable.memoImpl source) other)) := by
  rw [scan_finish, source_table source other client state table consistent]

/-- At the selected original call, cache hits retain their old response; only an actual miss invokes the supplied comparison sampler. The rest of the original continuation keeps the same cache and fixed-source fallback. -/
noncomputable def atStop {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (sample : JointKdfAddress → ProbComp FullOutput)
    (stopped : Prefix RatchetChain RatchetChain RatchetMaterial Context Plaintext Result
      (Auxiliary × RawCtxKdfRequestTable.Table)) : ProbComp (Result × (Auxiliary × RawCtxKdfRequestTable.Table)) :=
  match stopped.1 with
  | .complete result => pure (result, stopped.2)
  | .pending pending next => do
    let result ← (handler (QueryImpl.withCaching (spec := JointKdfRO) sample) other (.inl pending)).run stopped.2
    (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other) (next result.1)).run result.2

/-- Selecting the original source response gives exactly the original full continuation, without altering the executed prefix or cache. -/
theorem atStop_source {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (stopped : Prefix RatchetChain RatchetChain RatchetMaterial Context Plaintext Result
      (Auxiliary × RawCtxKdfRequestTable.Table)) :
    atStop source other (fun address => pure (productionStream source.crypto address)) stopped =
      finish (handler (RawCtxKdfRequestTable.memoImpl source) other) stopped := by
  rcases stopped with ⟨stopped, state⟩
  cases stopped <;> rfl

/-- The reached miss invokes the supplied sampler once at the original pending address, inserts that same response and runs the original continuation with the complete next state. -/
theorem atStop_miss {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (sample : JointKdfAddress → ProbComp FullOutput)
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (next : RatchetChain × RatchetMaterial → OracleComp (Spec Context Plaintext) Result)
    (state : Auxiliary × RawCtxKdfRequestTable.Table)
    (miss : state.2 (RawCtxSelectedPendingCut.requestAddress pending.request) = none) :
    atStop source other sample (.pending pending next, state) =
      (do let output ← sample (RawCtxSelectedPendingCut.requestAddress pending.request)
          (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other)
            (next (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)))).run
              (state.1, state.2.cacheQuery (RawCtxSelectedPendingCut.requestAddress pending.request) output)) := by
  simp only [atStop]
  rw [kdf_run]
  simp [miss]

/-- A reached hit never invokes the selected sampler and retains the entire cache for the original continuation. -/
theorem atStop_hit {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (sample : JointKdfAddress → ProbComp FullOutput)
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (next : RatchetChain × RatchetMaterial → OracleComp (Spec Context Plaintext) Result)
    (state : Auxiliary × RawCtxKdfRequestTable.Table) (output : FullOutput)
    (hit : state.2 (RawCtxSelectedPendingCut.requestAddress pending.request) = some output) :
    atStop source other sample (.pending pending next, state) =
      (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other)
        (next (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)))).run state := by
  simp only [atStop]
  rw [kdf_run]
  simp [hit]

/-- A stop supported by the actual receive program resumes its original pending control and complete cache; no separately supplied successful cut or continuation is assumed. -/
theorem reached_miss {Context Plaintext Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (before : QueryImpl (Spec Context Plaintext) (StateT (Auxiliary × RawCtxKdfRequestTable.Table) ProbComp))
    (effect : Effect RatchetChain RatchetChain RatchetMaterial Context) (index : Nat)
    (initial state : Auxiliary × RawCtxKdfRequestTable.Table)
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial Context)
    (next : RatchetChain × RatchetMaterial → OracleComp (Spec Context Plaintext)
      (RefinedRatchet RatchetChain RatchetChain RatchetMaterial × core.option.Option Plaintext))
    (supported : (.pending pending next, state) ∈
      support (scan before (RawCtxPendingReceiveQueries.program effect) index initial))
    (sample : JointKdfAddress → ProbComp FullOutput)
    (miss : state.2 (RawCtxSelectedPendingCut.requestAddress pending.request) = none) :
    atStop source other sample (.pending pending next, state) =
      (do let output ← sample (RawCtxSelectedPendingCut.requestAddress pending.request)
          (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other)
            (RawCtxPendingReceiveQueries.program (normalResume pending
              (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))))).run
                (state.1, state.2.cacheQuery (RawCtxSelectedPendingCut.requestAddress pending.request) output)) := by
  rw [program_pending before effect index initial pending next state supported]
  exact atStop_miss source other sample pending _ state miss

/-- The full original continued program after the selected insertion realizes the retained predecessor entry over its actual prior cache; the final cache is erased only after this entire continuation. -/
theorem retained_entry {Context Plaintext Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (client : OracleComp (Spec Context Plaintext) Result) (state : Auxiliary)
    (cache : RawCtxKdfRequestTable.Table) (address : JointKdfAddress) (output : FullOutput) :
    (simulateQ (viewHandler (lookup (view (productionStream source.crypto) cache)
      (fromOutput address output) (PqxdhOrderedChainHybrids.nextChain output)) other) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) other) client).run
          (state, cache.cacheQuery address output) := by
  have same : tableHandler (RawCtxKdfRequestTable.memoImpl source) other = RawCtxKdfRequestTable.tableImpl source other := by
    funext query state
    cases query <;> rfl
  simpa only [viewHandler, handler, QueryImpl.simulateQ_compose, same] using
    RawCtxRetainedTable.recorded_complete source other (simulateQ compiler client) state cache address output

end BeaconcryptCore.Computational.RawCtxReachedParentCut

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.source_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.source_table

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.kdf_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.kdf_run

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.source_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.source_scan

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_source

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_miss

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.atStop_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.reached_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.reached_miss

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentCut.retained_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentCut.retained_entry
