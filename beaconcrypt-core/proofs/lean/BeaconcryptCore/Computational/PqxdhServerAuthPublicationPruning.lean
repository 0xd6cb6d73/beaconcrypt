import BeaconcryptCore.Computational.PqxdhServerAuthPublicationFilter
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationCaptureSource

/-! Explicit oracle-tree stopping preserves every query before the stop. Capture observes no event when a branch ends before its raw request. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning
variable {ι Left Right : Type} {spec : OracleSpec ι}

/-- A pruned program may terminate at any point, but every query before termination and every possible reply continuation remains the original one. Returned values are deliberately unrelated. -/
inductive Prunes : OracleComp spec Left → OracleComp spec Right → Prop
  | stop (value : Left) (work : OracleComp spec Right) : Prunes (pure value) work
  | query (q : spec.Domain) (left : spec.Range q → OracleComp spec Left)
      (right : spec.Range q → OracleComp spec Right)
      (next : ∀ reply, Prunes (left reply) (right reply)) :
      Prunes (do let reply ← spec.query q; left reply) (do let reply ← spec.query q; right reply)

/-- Keeping a complete program is a permitted pruning; the relation makes no distributional assumption. -/
theorem refl (work : OracleComp spec Left) : Prunes work work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact .stop value _
  | query_bind query next ih => exact .query query next next ih

/-- Pruning preserves every all-replies query certificate, including weighted byte and mixed resource ledgers. -/
theorem query_bound {Budget : Type} (left : OracleComp spec Left) (right : OracleComp spec Right)
    (pruned : Prunes left right) (budget : Budget)
    (canQuery : spec.Domain → Budget → Prop) (cost : spec.Domain → Budget → Budget)
    (bounded : right.IsQueryBound budget canQuery cost) :
    left.IsQueryBound budget canQuery cost := by
  induction pruned generalizing budget with
  | stop value work => trivial
  | query query left right next ih =>
      rw [isQueryBound_query_bind_iff] at bounded ⊢
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- An entire common callback precedes either continuation, so pruning never drops its internal component work. The continuation relation is needed only on actual syntactic support. -/
theorem bind_same {Value : Type} (work : OracleComp spec Value)
    (left : Value → OracleComp spec Left) (right : Value → OracleComp spec Right)
    (next : ∀ value ∈ support work, Prunes (left value) (right value)) :
    Prunes (work >>= left) (work >>= right) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using next value (by simp)
  | query_bind query continuation ih =>
      rw [bind_assoc, bind_assoc]
      refine Prunes.query query _ _ fun reply => ih reply fun value supported => next value ?_
      simp only [mem_support_bind_iff]
      exact ⟨reply, by simp, supported⟩

/-- Only a selected seal replaces the private saved record; all other forwarded replies retain it. -/
def remembered (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (reply : AdaptiveCtxDynamicKnownKeys.Spec.Range query) (saved : Option CtxRomAuth.CtxRomRecord) :
    Option CtxRomAuth.CtxRomRecord :=
  match query with
  | .inl (.inl (.inr (.inr _))) => reply
  | _ => saved

/-- Every nonraw dynamic request is executed before its actual reply selects the continuation and retained record. -/
theorem dynamic_query (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (notRaw : ∀ raw, query ≠ .inl (.inr raw))
    (next : AdaptiveCtxDynamicKnownKeys.Spec.Range query → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Left)
    (saved : Option CtxRomAuth.CtxRomRecord) :
    PqxdhServerAuthPublicationCaptureSource.dynamic (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query query; next reply) saved =
      (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query query
          PqxdhServerAuthPublicationCaptureSource.dynamic (next reply) (remembered query reply saved)) := by
  rcases query with (((coin | (input | request)) | raw) | known)
  all_goals try rfl
  exact (notRaw raw rfl).elim

set_option linter.deprecated false in
/-- Stopping branches cannot increase a before-raw capture event that is false when no candidate was captured. The full stateful component interpreter, its replies and its poststate are shared. -/
theorem capture_mono {State : Type}
    (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT State ProbComp))
    (left : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Left)
    (right : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Right) (pruned : Prunes left right)
    (saved : Option CtxRomAuth.CtxRomRecord) (state : State)
    (event : PqxdhServerAuthPublicationGuess.Candidate → Prop) (empty : ¬ event none) :
    Pr[fun result => event result.1 | (simulateQ impl
      (PqxdhServerAuthPublicationCaptureSource.dynamic left saved)).run state] ≤
      Pr[fun result => event result.1 | (simulateQ impl
        (PqxdhServerAuthPublicationCaptureSource.dynamic right saved)).run state] := by
  classical
  induction pruned generalizing saved state with
  | stop value work =>
      change Pr[fun result => event result.1 | (pure (none, state) : ProbComp (PqxdhServerAuthPublicationGuess.Candidate × State))] ≤ _
      simp [probEvent_pure, empty]
  | query query left right next ih =>
      by_cases raw : ∃ bytes, query = .inl (.inr bytes)
      · obtain ⟨bytes, rfl⟩ := raw
        exact le_rfl
      · rw [dynamic_query query (fun bytes equal => raw ⟨bytes, equal⟩),
          dynamic_query query (fun bytes equal => raw ⟨bytes, equal⟩)]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun reply => mul_le_mul_right (ih reply.1 _ reply.2) _

set_option linter.deprecated false in
/-- The literal dynamic source experiment preserves capture domination, including its selected-key draw and full shared source state. -/
theorem source_mono (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (crypto : Pqxdh.Crypto)
    (left : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Left)
    (right : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Right) (pruned : Prunes left right)
    (saved : Option CtxRomAuth.CtxRomRecord)
    (event : PqxdhServerAuthPublicationGuess.Candidate → Prop) (empty : ¬ event none) :
    Pr[fun result => event result.1 | AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto
      (PqxdhServerAuthPublicationCaptureSource.dynamic left saved)] ≤
      Pr[fun result => event result.1 | AdaptiveCtxDynamicKnownKeys.sourceGame real decode crypto
        (PqxdhServerAuthPublicationCaptureSource.dynamic right saved)] := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun key => mul_le_mul_right
    (capture_mono (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode crypto key) left right pruned
      saved AdaptiveCtxDynamicKnownKeys.initialSource event empty) _

/-- The ordered before-raw observer ignores only the program's terminal value; all queried replies and private saved records remain unchanged. -/
theorem dynamic_map {Mapped : Type} (f : Left → Mapped)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Left) (saved : Option CtxRomAuth.CtxRomRecord) :
    PqxdhServerAuthPublicationCaptureSource.dynamic (f <$> work) saved =
      PqxdhServerAuthPublicationCaptureSource.dynamic work saved := by
  classical
  induction work using OracleComp.inductionOn generalizing saved with
  | pure value => rfl
  | query_bind query next ih =>
      rw [map_bind]
      by_cases raw : ∃ bytes, query = .inl (.inr bytes)
      · obtain ⟨bytes, rfl⟩ := raw
        rfl
      · rw [dynamic_query query (fun bytes equal => raw ⟨bytes, equal⟩),
          dynamic_query query (fun bytes equal => raw ⟨bytes, equal⟩)]
        exact bind_congr fun reply => ih reply _

/-- Pure terminal observations cannot change which oracle prefixes were truncated. -/
theorem map_both {LeftOut RightOut : Type} (left : OracleComp spec Left)
    (right : OracleComp spec Right) (pruned : Prunes left right)
    (f : Left → LeftOut) (g : Right → RightOut) :
    Prunes (f <$> left) (g <$> right) := by
  induction pruned with
  | stop value work => simpa only [map_pure] using (Prunes.stop (f value) (g <$> work))
  | query query left right next ih =>
      simpa only [map_bind] using Prunes.query query _ _ ih

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.refl
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.query_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.query_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.bind_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.bind_same
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.dynamic_query' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.dynamic_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.capture_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.capture_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.source_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.source_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.dynamic_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.dynamic_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.map_both' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPruning.map_both
