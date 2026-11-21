import BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins

/-!
The concrete adaptive record/reveal client keeps a chronological audit of the actual original indexed record requests, full private entry roles, unchanged optional results and before/after authentication observations. The executable needs no selected-key argument. Erasure retains the original selected compiler and complete receipt history, including a nonempty prefix.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedProductionAudit
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedAuthenticationObserver RawCtxSelectedAcceptedRecord RawCtxSelectedProductionOrigins
open RawCtxSelectedFamilyLiveCompiler (Front)
open CtxRomAuth
variable {M P I D K Result : Type} {S B : Nat}

structure Record (M P I D K : Type) (S B : Nat) where
  query : (RawCtxProtocolRoles.SourceSpec S B).Domain
  roles : Roles M P I D K S B
  reply : Option ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles M P I D K S B)
  before : State
  after : State

structure Audit (M P I D K : Type) (S B : Nat) where
  front : Front M P I D K S B
  observer : State
  records : List (Record M P I D K S B)

noncomputable def step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Audit M P I D K S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Audit M P I D K S B) :=
  match query with
  | .inl request => do
      let result ← monitor
        (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request state.front.1) state.observer
      let published := RawCtxSelectedFamilyLiveCompiler.publish state.front result.1
      pure (published.1, ⟨published.2, result.2,
        state.records ++ [⟨request, state.front.1, result.1, state.observer, result.2⟩]⟩)
  | .inr request =>
      let observed := RawCtxSelectedMessageReveals.step request state.front
      pure (RawCtxSelectedMessageReveals.emit request observed.1, ⟨observed.2, state.observer, state.records⟩)

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (OptionT (StateT (Audit M P I D K S B) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))) :=
  fun query => OptionT.mk (step source writer prior parent target nonce next sender route read query)

noncomputable def client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B) :=
  ((simulateQ (impl source writer prior parent target nonce next sender route read) original).run).run state

def erase {X : Type} (result : X × Audit M P I D K S B) : (X × Front M P I D K S B) × State :=
  ((result.1, result.2.front), result.2.observer)

/-- Erasing only the source audit recovers the actual source step with its exact full role/history state and ordinary authentication receipts. Every optional stop and plaintext remains unchanged. -/
theorem step_erase (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Audit M P I D K S B) :
    erase <$> step source writer prior parent target nonce next sender route read query state =
      monitor (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read query).run).run state.front) state.observer := by
  cases query with
  | inl request =>
    simp only [step, bind_pure_comp, Functor.map_map, RawCtxSelectedFamilyLiveCompiler.impl,
      OptionT.run_mk, StateT.run, monitor_map]
    rfl
  | inr request => rfl

private theorem monitor_bind {X Y : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X)
    (continuation : X → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Y) (state : State) :
    monitor (work >>= continuation) state =
      (do let result ← monitor work state; monitor (continuation result.1) result.2) := by
  simp only [monitor, simulateQ_bind, StateT.run_bind]

/-- The complete adaptive original client has the same final optional decision, private family/history and authentication receipt list after erasing only the source query audit. -/
theorem client_erase (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B) :
    erase <$> client source writer prior parent target nonce next sender route read original state =
      monitor (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read original state.front) state.observer := by
  induction original using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [client, RawCtxSelectedFamilyLiveCompiler.client, simulateQ_bind, simulateQ_spec_query,
      OptionT.run_bind, Option.elimM, StateT.run_bind]
    rw [map_bind, monitor_bind, ← step_erase, bind_map_left]
    apply bind_congr
    rintro ⟨none | value, nextState⟩
    · rfl
    · exact ih value nextState

/-- The complete source query audit preserves every component query predicate and budget exactly, including repeated/rejected raw attempts and nonce-stopping seals. -/
theorem client_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (client source writer prior parent target nonce next sender route read original state).IsQueryBoundP predicate bound ↔
      (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read original state.front).IsQueryBoundP predicate bound := by
  have same := congrArg (fun work => work.IsQueryBoundP predicate bound)
    (client_erase source writer prior parent target nonce next sender route read original state)
  simpa only [isQueryBoundP_map_iff, monitor_queries] using same.to_iff

noncomputable def Recorded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (entry : Record M P I D K S B) : Prop :=
  (entry.reply, entry.after) ∈ support (monitor
    (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read entry.query entry.roles) entry.before)

/-- Each new audit entry contains the actual reached original query, private entry roles, unchanged optional result and both observer histories. Prior entries are retained verbatim. -/
theorem step_records (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Audit M P I D K S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Audit M P I D K S B)
    (supported : result ∈ support (step source writer prior parent target nonce next sender route read query state))
    (entry : Record M P I D K S B) (found : entry ∈ result.2.records) :
    entry ∈ state.records ∨ Recorded source writer prior parent target nonce next sender route read entry := by
  cases query with
  | inl request =>
    simp only [step, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    simp only [List.mem_append, List.mem_singleton] at found
    rcases found with earlier | same
    · exact Or.inl earlier
    · subst entry
      exact Or.inr reached
  | inr request =>
    simp only [step, mem_support_pure_iff] at supported
    subst result
    exact Or.inl found

/-- Exact observer continuity between chronologically ordered actual source record requests; reveal steps leave this observer unchanged. -/
inductive Edges : State → List (Record M P I D K S B) → State → Prop where
  | nil (state : State) : Edges state [] state
  | cons (entry : Record M P I D K S B) {tail : List (Record M P I D K S B)} {after : State}
      (rest : Edges entry.after tail after) : Edges entry.before (entry :: tail) after

/-- Adjacent pieces of the same actual observer history compose without dropping prefix seals or attempts. -/
theorem edges_append {before middle after : State} {first second : List (Record M P I D K S B)}
    (left : Edges before first middle) (right : Edges middle second after) :
    Edges before (first ++ second) after := by
  induction left with
  | nil => exact right
  | cons entry rest ih => exact .cons entry (ih right)

/-- A concrete step appends exactly its actual record request, or no record on reveal; every appended entry is justified by the literal source call and preserves the complete chronological observer chain. -/
theorem step_trace (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Audit M P I D K S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Audit M P I D K S B)
    (supported : result ∈ support (step source writer prior parent target nonce next sender route read query state)) :
    ∃ suffix, result.2.records = state.records ++ suffix ∧ Edges state.observer suffix result.2.observer ∧
      ∀ entry ∈ suffix, Recorded source writer prior parent target nonce next sender route read entry := by
  cases query with
  | inl request =>
    simp only [step, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    refine ⟨[⟨request, state.front.1, actual.1, state.observer, actual.2⟩], rfl, .cons ⟨request, state.front.1, actual.1, state.observer, actual.2⟩ (.nil actual.2), ?_⟩
    intro entry found
    have same := List.mem_singleton.mp found
    subst entry
    exact reached
  | inr request =>
    simp only [step, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], (List.append_nil _).symm, .nil _, by simp⟩

/-- The complete adaptive run produces a chronological suffix of actual source calls while preserving every entry observer seal/attempt and every prior audit entry. No assumed origin or callback simulation premise is used. -/
theorem client_trace (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state)) :
    ∃ suffix, result.2.records = state.records ++ suffix ∧ Edges state.observer suffix result.2.observer ∧
      ∀ entry ∈ suffix, Recorded source writer prior parent target nonce next sender route read entry := by
  induction original using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [client, simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨[], (List.append_nil _).symm, .nil _, by simp⟩
  | query_bind query continuation ih =>
    simp only [client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    obtain ⟨first, firstRecords, firstEdges, firstActual⟩ :=
      step_trace source writer prior parent target nonce next sender route read query state reply head
    rcases reply with ⟨none | value, nextState⟩
    · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
      subst result
      exact ⟨first, firstRecords, firstEdges, firstActual⟩
    · simp only [Option.elim_some] at tail
      obtain ⟨second, secondRecords, secondEdges, secondActual⟩ := ih value nextState tail
      refine ⟨first ++ second, ?_, edges_append firstEdges secondEdges, ?_⟩
      · change nextState.records = state.records ++ first at firstRecords
        rw [secondRecords, firstRecords, List.append_assoc]
      · intro entry found
        rcases List.mem_append.mp found with earlier | later
        · exact firstActual entry earlier
        · exact secondActual entry later

/-- Every seal in an actual chronological source trace belongs to its retained prefix or to a concrete indexed send in that trace. Source origin consumes actual callback support, not tuple injectivity. -/
theorem trace_production (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    {before after : State} {records : List (Record M P I D K S B)}
    (edges : Edges before records after)
    (actual : ∀ record ∈ records, Recorded source writer prior parent target nonce next sender route read record)
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ ∃ record ∈ records,
      FamilyProduced writer prior parent target nonce next sender record.query record.roles record.reply entry := by
  induction edges with
  | nil state => exact Or.inl found
  | cons record rest ih =>
    have tailActual : ∀ later ∈ _, Recorded source writer prior parent target nonce next sender route read later :=
      fun later member => actual later (List.mem_cons_of_mem record member)
    rcases ih tailActual found with middle | later
    · rcases family_produced source writer prior parent target nonce next sender route read record.query record.roles
        record.before record.after record.reply (actual record (List.mem_cons_self)) entry middle with earlier | produced
      · exact Or.inl earlier
      · exact Or.inr ⟨record, List.mem_cons_self, produced.1⟩
    · obtain ⟨later, member, produced⟩ := later
      exact Or.inr ⟨later, List.mem_cons_of_mem record member, produced⟩

/-- Whole adaptive source provenance comes from the audited execution itself. Every final selected seal is an entry-prefix seal or has a newly reached original indexed send, private source capability and actual optional publication in the produced chronological suffix. -/
theorem client_production (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state))
    (entry : CtxSuccessfulSeal) (found : entry ∈ result.2.observer.seals) :
    entry ∈ state.observer.seals ∨ ∃ suffix, result.2.records = state.records ++ suffix ∧
      ∃ record ∈ suffix, Recorded source writer prior parent target nonce next sender route read record ∧
        FamilyProduced writer prior parent target nonce next sender record.query record.roles record.reply entry := by
  obtain ⟨suffix, appended, edges, actual⟩ :=
    client_trace source writer prior parent target nonce next sender route read original state result supported
  rcases trace_production source writer prior parent target nonce next sender route read edges actual entry found with earlier | produced
  · exact Or.inl earlier
  · obtain ⟨record, member, production⟩ := produced
    exact Or.inr ⟨suffix, appended, record, member, actual record member, production⟩

/-- Cutting a chronological observer trace uses the actual list position, so duplicate record values never identify or reorder source occurrences. -/
theorem edges_cut {before after : State} (preceding suffix : List (Record M P I D K S B))
    (record : Record M P I D K S B) (edges : Edges before (preceding ++ record :: suffix) after) :
    Edges before preceding record.before ∧ Edges record.after suffix after := by
  induction preceding generalizing before with
  | nil =>
    cases edges with
    | cons entry rest => exact ⟨.nil _, rest⟩
  | cons entry preceding ih =>
    cases edges with
    | cons first rest =>
      obtain ⟨earlier, later⟩ := ih rest
      exact ⟨.cons entry earlier, later⟩

/-- At any actual recorded query position, every preceding selected seal is a retained entry-prefix receipt or belongs to a strictly earlier original indexed send. Future seals cannot supply the accepted query's origin. -/
theorem client_before_production (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state))
    (preceding suffix : List (Record M P I D K S B)) (current : Record M P I D K S B)
    (position : result.2.records = state.records ++ (preceding ++ current :: suffix))
    (entry : CtxSuccessfulSeal) (found : entry ∈ current.before.seals) :
    entry ∈ state.observer.seals ∨ ∃ earlier ∈ preceding,
      Recorded source writer prior parent target nonce next sender route read earlier ∧
      FamilyProduced writer prior parent target nonce next sender earlier.query earlier.roles earlier.reply entry := by
  obtain ⟨actual, appended, edges, calls⟩ :=
    client_trace source writer prior parent target nonce next sender route read original state result supported
  have same : actual = preceding ++ current :: suffix := List.append_cancel_left (appended.symm.trans position)
  rw [same] at edges calls
  have before := (edges_cut preceding suffix current edges).1
  have priorCalls : ∀ earlier ∈ preceding, Recorded source writer prior parent target nonce next sender route read earlier :=
    fun earlier member => calls earlier (List.mem_append_left _ member)
  rcases trace_production source writer prior parent target nonce next sender route read before priorCalls entry found with old | produced
  · exact Or.inl old
  · obtain ⟨earlier, member, production⟩ := produced
    exact Or.inr ⟨earlier, member, priorCalls earlier member, production⟩

/-- Every record/public query adds exactly one chronological audit position; every reveal adds zero, including stopping paths. -/
theorem step_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Audit M P I D K S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × Audit M P I D K S B)
    (supported : result ∈ support (step source writer prior parent target nonce next sender route read query state)) :
    result.2.records.length = state.records.length + (if query.isLeft then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [step, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨actual, _, rfl⟩ := supported
    simp only [List.length_append, List.length_singleton, Sum.isLeft_inl, ite_true]
  | inr request =>
    simp only [step, mem_support_pure_iff] at supported
    subst result
    rfl

/-- Every actual adaptive source record/public attempt has one bounded audit position. Repeated attempts and stopping calls are counted, while reveals preserve the observer history without manufacturing record positions. -/
theorem client_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (qRecord : Nat)
    (bounded : original.IsQueryBoundP (fun query => query.isLeft = true) qRecord)
    (state : Audit M P I D K S B) (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state)) :
    result.2.records.length ≤ state.records.length + qRecord := by
  induction original using OracleComp.inductionOn generalizing state qRecord with
  | pure value =>
    simp only [client, simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    have counted := step_length source writer prior parent target nonce next sender route read query state reply head
    rcases reply with ⟨none | value, nextState⟩
    · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
      subst result
      cases query <;> simp_all only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true,
        not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega
    · simp only [Option.elim_some] at tail
      have rest := ih value _ (bounded.2 value) nextState tail
      cases query <;> simp_all only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true,
        not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega

/-- The five original record/public budgets supply the actual finite source-position cap; the separate reveal budget is retained without inflating this count. -/
theorem source_record_bound (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded original budget) :
    original.IsQueryBoundP (fun query => query.isLeft = true) (RawCtxRevealBudgets.bill (fun _ => 1) 0 budget) := by
  refine IsQueryBound.proj (RawCtxRevealBudgets.bill (fun _ => 1) 0) ?_ ?_ bounded
  all_goals intro query current permitted
  all_goals have bill := RawCtxRevealBudgets.bill_step (fun _ => 1) 0 query current permitted
  all_goals cases query <;> simp_all only [RawCtxRevealBudgets.weight, Sum.isLeft_inl, Sum.isLeft_inr,
    Bool.false_eq_true, not_false_eq_true, true_or, ↓reduceIte]
  all_goals omega

/-- The original full source budgets bound the final actual query ledger, in addition to the exact unchanged component query caps. This is a position count, not a cryptographic selection loss. -/
theorem source_length (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded original budget)
    (state : Audit M P I D K S B) (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state)) :
    result.2.records.length ≤ state.records.length + RawCtxRevealBudgets.bill (fun _ => 1) 0 budget :=
  client_length source writer prior parent target nonce next sender route read original _
    (source_record_bound original budget bounded) state result supported

end BeaconcryptCore.Computational.RawCtxSelectedProductionAudit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_records
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.edges_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.edges_append
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_trace
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_trace
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.trace_production' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.trace_production
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_production' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_production
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.edges_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.edges_cut
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_before_production' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_before_production
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.step_length
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.client_length
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.source_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.source_record_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.source_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionAudit.source_length
