import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-!
The selected cursor is linked to an executable walk from its original initial input through the same retained private cache. Actual private hits preserve their previous full response; misses only add a previously absent binding. Every matched callback extends the stored path by its original response, and every other callback keeps the same path. The walk records all earlier chain inputs, including repetitions, without assuming injectivity or enumerating an arbitrary cache domain.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxCursorLineage
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxSelectiveChainGame RawCtxKdfRequestTable RawCtxFirstParentRisk
variable {A Result : Type} {S B : Nat}

def Extends (before after : Table) : Prop := ∀ address output, before address = some output → after address = some output

def walk (table : Table) : Nat → RootOutput → Option (List RootOutput × RootOutput)
  | 0, root => some ([], root)
  | n + 1, root => do
      let (earlier, input) ← walk table n root
      let output ← table (inputAddress input)
      pure (earlier ++ [input], nextChain output)

def Lineage (root : RootOutput) (store : Store) : Prop :=
  ∃ earlier, walk store.1 store.2.depth root = some (earlier, store.2.input)

/-- The concrete finite walk is unchanged by any extension of its already present cache bindings. -/
theorem walk_extends (before after : Table) (extension : Extends before after) (n : Nat)
    (root : RootOutput) (result : List RootOutput × RootOutput)
    (known : walk before n root = some result) : walk after n root = some result := by
  induction n generalizing result with
  | zero => exact known
  | succ n ih =>
    cases earlier : walk before n root with
    | none => simp [walk, earlier] at known
    | some reached =>
      have keep := ih reached earlier
      cases found : before (inputAddress reached.2) with
      | none => simp [walk, earlier, found] at known
      | some output =>
        have reduced : some (reached.1 ++ [reached.2], nextChain output) = some result := by
          simpa [walk, earlier, found] using known
        simpa [walk, keep, extension _ output found] using reduced

/-- A successful cache walk retains exactly one earlier input per step, and every recorded input has an actual retained full response. -/
theorem walk_shape (table : Table) (n : Nat) (root : RootOutput)
    (result : List RootOutput × RootOutput) (known : walk table n root = some result) :
    result.1.length = n ∧ ∀ input ∈ result.1, ∃ output, table (inputAddress input) = some output := by
  induction n generalizing result with
  | zero =>
    simp only [walk, Option.some.injEq] at known
    subst result
    simp
  | succ n ih =>
    cases earlier : walk table n root with
    | none => simp [walk, earlier] at known
    | some reached =>
      cases found : table (inputAddress reached.2) with
      | none => simp [walk, earlier, found] at known
      | some output =>
        have same : (reached.1 ++ [reached.2], nextChain output) = result := by
          simpa [walk, earlier, found] using known
        subst result
        have previous := ih reached earlier
        constructor
        · simp [previous.1]
        · intro input present
          simp only [List.mem_append, List.mem_singleton] at present
          rcases present with old | rfl
          · exact previous.2 input old
          · exact ⟨output, found⟩

/-- Every actual private callback preserves all earlier full cache bindings, including a hit on the current request. -/
theorem private_extends (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (result : FullOutput × Store)
    (supported : result ∈ support (privateStep source stage request store)) : Extends store.1 result.2.1 := by
  intro address output cached
  by_cases same : address = request
  · subst address
    rw [private_hit source stage request store output cached, mem_support_pure_iff] at supported
    subst result
    simp
  · have state := private_state source stage request store result supported
    rw [state]
    exact (QueryCache.cacheQuery_of_ne (spec := JointKdfRO) store.1 result.1 same).trans cached

/-- Each actual matching response advances the cursor along the same retained cache path; all other inputs retain its original depth and path. -/
theorem private_lineage (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (root : RootOutput) (valid : Lineage root store)
    (result : FullOutput × Store) (supported : result ∈ support (privateStep source stage request store)) :
    Lineage root result.2 := by
  obtain ⟨earlier, known⟩ := valid
  have retained := walk_extends store.1 result.2.1 (private_extends source stage request store result supported)
    store.2.depth root (earlier, store.2.input) known
  have state := private_state source stage request store result supported
  rw [state] at retained ⊢
  cases matching : matched store.2 request with
  | false =>
    exact ⟨earlier, by simpa only [advance, matching, Bool.false_eq_true, if_false] using retained⟩
  | true =>
    have same : request = inputAddress store.2.input := by
      simpa only [matched, cursorAddress, inputAddress, decide_eq_true_eq] using matching
    refine ⟨earlier ++ [store.2.input], ?_⟩
    simp only [advance, matching, if_true]
    simp [walk, retained, nextChain]
    rw [← same]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Every original pending callback preserves previous cache bindings and the selected initial-input path, including non-KDF shared effects and optional reads. -/
theorem callback_state (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain)
    (state : RawCtxPendingSelectiveFamily.State A) (root : RootOutput) (valid : Lineage root state.2)
    (result : (RawCtxPendingSelectiveFamily.Spec S B).Range query × RawCtxPendingSelectiveFamily.State A)
    (supported : result ∈ support ((RawCtxPendingSelectiveFamily.handler source writer stage query).run state)) :
    Extends state.2.1 result.2.2.1 ∧ Lineage root result.2.2 := by
  cases found : RawCtxSelectedFamilyContext.queryAddress query with
  | none =>
    rw [RawCtxPendingNonKdfStore.callback_store source writer stage query found state result supported]
    exact ⟨fun _ _ present => present, valid⟩
  | some address =>
    rcases query with ((request | opening) | ((request | sealing) | request)) | request
    all_goals simp only [RawCtxSelectedFamilyContext.queryAddress, RawCtxSelectedFamilyContext.primitiveAddress] at found
    all_goals try cases found
    all_goals first | rw [RawCtxPendingParentCallbacks.receive_step] at supported | rw [RawCtxPendingParentCallbacks.send_step] at supported
    all_goals simp only [support_map, Set.mem_image] at supported
    all_goals obtain ⟨reply, actual, rfl⟩ := supported
    all_goals exact ⟨private_extends source stage _ state.2 reply actual,
      private_lineage source stage _ state.2 root valid reply actual⟩

/-- Actual chronological logging preserves the same selected cache path and every earlier full response. -/
theorem logged_state (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain)
    (state : RawCtxSelectiveFamilyLog.LoggedState A) (root : RootOutput) (valid : Lineage root state.1.2)
    (result : (RawCtxPendingSelectiveFamily.Spec S B).Range query × RawCtxSelectiveFamilyLog.LoggedState A)
    (supported : result ∈ support ((RawCtxSelectiveFamilyLog.handler source writer stage query).run state)) :
    Extends state.1.2.1 result.2.1.2.1 ∧ Lineage root result.2.1.2 := by
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  exact callback_state source writer stage query state.1 root valid reply actual

/-- The full original adaptive pending program retains its exact initial-input lineage and all initial private bindings. -/
theorem program_state (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxSelectiveFamilyLog.LoggedState A) (root : RootOutput) (valid : Lineage root state.1.2)
    (result : Result × RawCtxSelectiveFamilyLog.LoggedState A)
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state)) :
    Extends state.1.2.1 result.2.1.2.1 ∧ Lineage root result.2.1.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨fun _ _ present => present, valid⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    have step := logged_state source writer stage query state root valid reply head
    have rest := ih reply.1 reply.2 step.2 result tail
    exact ⟨fun address output present => rest.1 address output (step.1 address output present), rest.2⟩

/-- Every actually saved prefix retains that same initial-input path and all earlier cache bindings; selection changes neither the statement nor its proof. -/
theorem scan_state (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (selected : (RawCtxPendingSelectiveFamily.Spec S B).Domain → RawCtxSelectiveFamilyLog.LoggedState A → Bool)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (state : RawCtxSelectiveFamilyLog.LoggedState A) (root : RootOutput) (valid : Lineage root state.1.2)
    (result : RawCtxPendingMixedPrefix.Prefix (RawCtxPendingSelectiveFamily.Spec S B) Result (RawCtxSelectiveFamilyLog.LoggedState A))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (RawCtxSelectiveFamilyLog.handler source writer stage) client state)) :
    Extends state.1.2.1 result.2.1.2.1 ∧ Lineage root result.2.1.2 := by
  apply RawCtxStatefulPrefixInvariant.scan_valid selected (RawCtxSelectiveFamilyLog.handler source writer stage)
    (fun reached => Extends state.1.2.1 reached.1.2.1 ∧ Lineage root reached.1.2) ?_
    client state ⟨fun _ _ present => present, valid⟩ result supported
  intro query before invariant _ reply actual
  have step := logged_state source writer stage query before root invariant.2 reply actual
  exact ⟨fun address output present => step.1 address output (invariant.1 address output present), step.2⟩

/-- Starting the selected direction at its actual initial coordinate establishes the cache path without an assumption on any cached output. -/
theorem initial (table : Table) (root : RootOutput) : Lineage root (table, ⟨root, 0⟩) := ⟨[], rfl⟩

end BeaconcryptCore.Computational.RawCtxCursorLineage

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.walk_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.walk_extends

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.walk_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.walk_shape

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.private_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.private_extends

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.private_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.private_lineage

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.callback_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.callback_state

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.logged_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.logged_state

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.program_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.program_state

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.scan_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.scan_state

/-- info: 'BeaconcryptCore.Computational.RawCtxCursorLineage.initial' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCursorLineage.initial
