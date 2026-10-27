import BeaconcryptCore.Computational.RawCtxSelectedMessageStopping
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The actual stopped source retains every attempted read in private history, including the read that stops execution. Candidate accounting counts all known returned chain/key values and all prior disclosed values, even repeated values or byte aliases. No key-guessing bound is inferred from their count.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds
open PqxdhSecretInputKdf PqxdhJointKdfGame RawCtxFreshChainCut
open RawCtxSelectedMessageKey RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals RawCtxSelectedMessageFamily RawCtxSelectedMessageStopping
variable {M P I D K σ Result : Type} {S B : Nat}

/-- Every source read costs at most one known candidate, including its retained stopping observation; record/public callbacks preserve the private history. -/
theorem step_candidates (record : Record M P I D K σ S B) (prior : List RatchetChain)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : FullState M P I D K σ S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × FullState M P I D K σ S B)
    (supported : result ∈ support (((stopping record query).run).run state)) :
    (keys prior result.2.1.2).length ≤ (keys prior state.1.2).length + (if query.isRight then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [stopping, OptionT.run_mk, StateT.run] at supported
    rcases mem_support_map_peel _ _ supported with ⟨child, _, rfl⟩
    exact Nat.le_refl _
  | inr request =>
    simp only [stopping_read] at supported
    subst result
    exact step_probe_bound prior request state.1

/-- Every stopped execution has at most its original reveal budget many new known candidates, with all rejected and repeated attempts charged. -/
theorem schedule_candidates (record : Record M P I D K σ S B) (prior : List RatchetChain)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (qReveal : Nat)
    (bounded : client.IsQueryBoundP (fun query => query.isRight = true) qReveal)
    (state : FullState M P I D K σ S B) (result : Option Result × FullState M P I D K σ S B)
    (supported : result ∈ support (((simulateQ (stopping record) client).run).run state)) :
    (keys prior result.2.1.2).length ≤ (keys prior state.1.2).length + qReveal := by
  induction client using OracleComp.inductionOn generalizing qReveal state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    have step := step_candidates record prior query state reply head
    rcases reply with ⟨none | value, nextState⟩
    · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
      subst result
      dsimp only at step ⊢
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega
    · simp only [Option.elim_some] at tail
      have rest := ih value _ (bounded.2 value) nextState tail
      dsimp only at step
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega

/-- The complete six-coordinate source budget supplies the candidate bill consumed by terminal selected-key probes. -/
theorem source_candidates (record : Record M P I D K σ S B) (prior : List RatchetChain)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (budget : RawCtxRevealBudgets.Budget)
    (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : FullState M P I D K σ S B) (result : Option Result × FullState M P I D K σ S B)
    (supported : result ∈ support (((simulateQ (stopping record) client).run).run state)) :
    (keys prior result.2.1.2).length ≤ (keys prior state.1.2).length + budget.2 :=
  schedule_candidates record prior client budget.2 (RawCtxRevealBudgets.reveal_bound client budget bounded)
    state result supported

/-- Stopping adds no uniform queries to record/public callbacks and no uniform draw to any actual read, including the stopping one. -/
theorem step_uniform (record : Record M P I D K σ S B) (cost : RawCtxServerServiceBounds.Kind → Nat)
    (recordBound : ∀ query state, ((record query).run state).IsTotalQueryBound (cost (RawCtxProtocolBudgets.sourceKind query)))
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : FullState M P I D K σ S B) :
    (((stopping record query).run).run state).IsTotalQueryBound (RawCtxRevealBudgets.weight cost 0 query) := by
  cases query with
  | inl request =>
    simpa only [stopping, OptionT.run_mk, StateT.run, IsTotalQueryBound, isQueryBound_map_iff, RawCtxRevealBudgets.weight] using recordBound request (state.1.1, state.2)
  | inr request => trivial

/-- The stopped adaptive source schedule consumes its full weighted callback bill; every callback cost remains an explicit operational obligation. -/
theorem schedule_uniform (record : Record M P I D K σ S B) (cost : RawCtxServerServiceBounds.Kind → Nat)
    (recordBound : ∀ query state, ((record query).run state).IsTotalQueryBound (cost (RawCtxProtocolBudgets.sourceKind query)))
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (budget : RawCtxRevealBudgets.Budget)
    (bounded : RawCtxRevealBudgets.Bounded client budget) (state : FullState M P I D K σ S B) :
    (((simulateQ (stopping record) client).run).run state).IsTotalQueryBound (RawCtxRevealBudgets.bill cost 0 budget) := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value => trivial
  | query_bind query next ih =>
    change RawCtxRevealBudgets.permitted query budget ∧
      ∀ value, RawCtxRevealBudgets.Bounded (next value) (RawCtxRevealBudgets.remaining query budget) at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    have step := step_uniform record cost recordBound query state
    have rest : ∀ reply : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × FullState M P I D K σ S B,
        ((reply.1.elim (pure none) (fun value => (simulateQ (stopping record) (next value)).run)).run reply.2).IsTotalQueryBound
          (RawCtxRevealBudgets.bill cost 0 (RawCtxRevealBudgets.remaining query budget)) := by
      rintro ⟨none | value, nextState⟩
      · trivial
      · exact ih value _ (bounded.2 value) nextState
    have bound := isTotalQueryBound_bind step rest
    simpa only [RawCtxRevealBudgets.bill_step cost 0 query budget bounded.1] using bound

end BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.step_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.step_candidates
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.schedule_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.schedule_candidates
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.source_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.source_candidates
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.step_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds.schedule_uniform
