import BeaconcryptCore.Computational.RawCtxStoppedParentSource

/-!
Proof certificates are attached to the result of the same finite oracle program by structural recursion. Every query, reply and branch is retained. Erasing the proof field recovers the literal original program, so its source cost is unchanged. This is forward proof annotation, not conditioning, rejection sampling, a runtime support test or an inverse selection of an earlier Context.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSupportedSample
variable {ι α β : Type} {spec : OracleSpec ι}

def certify (program : OracleComp spec α) (property : α → Prop)
    (valid : ∀ value ∈ support program, property value) : OracleComp spec {value // property value} :=
  OracleComp.construct (C := fun original =>
    (∀ value ∈ support original, property value) → OracleComp spec {value // property value})
    (fun value known => pure ⟨value, known value (by simp)⟩)
    (fun query next recurse known => (liftM (spec.query query) : OracleComp spec _) >>= fun reply =>
      recurse reply (fun value reached => known value
        ((mem_support_bind_iff _ _ _).mpr ⟨reply, mem_support_query query reply, reached⟩))) program valid

/-- Forgetting only the certificate recovers the same original syntax, including every query and reply branch. -/
theorem erase (program : OracleComp spec α) (property : α → Prop)
    (valid : ∀ value ∈ support program, property value) :
    Subtype.val <$> certify program property valid = program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [certify, OracleComp.construct_pure, map_pure]
  | query_bind query next ih =>
    simp only [certify, OracleComp.construct_query_bind, map_bind]
    congr 1
    funext reply
    exact ih reply _

/-- Any original continuation receives the exact original result after proof annotation. -/
theorem run (program : OracleComp spec α) (property : α → Prop)
    (valid : ∀ value ∈ support program, property value) (next : α → OracleComp spec β) :
    (certify program property valid >>= fun result => next result.val) = program >>= next := by
  rw [← bind_map_left, erase]

/-- Every selective query budget is exactly unchanged, by literal syntax rather than evaluated probability equality. -/
theorem query_bound (program : OracleComp spec α) (property : α → Prop)
    (valid : ∀ value ∈ support program, property value) (counted : spec.Domain → Prop) [DecidablePred counted] (bound : Nat) :
    (certify program property valid).IsQueryBoundP counted bound ↔ program.IsQueryBoundP counted bound := by
  calc
    _ ↔ (Subtype.val <$> certify program property valid).IsQueryBoundP counted bound := (isQueryBoundP_map_iff _ _ _).symm
    _ ↔ _ := by rw [erase]

abbrev Pending (sample : OracleComp spec (Bool ⊕ α)) := {value : α // Sum.inr value ∈ support sample}

def sum (sample : OracleComp spec (Bool ⊕ α)) : OracleComp spec (Bool ⊕ Pending sample) :=
  (fun result => match result with
    | ⟨.inl decision, _⟩ => Sum.inl decision
    | ⟨.inr context, reached⟩ => Sum.inr ⟨context, reached⟩) <$>
      certify sample (fun value => value ∈ support sample) (fun _ reached => reached)

/-- The common decision and pending runtime Context are identical after erasing the support certificate. -/
theorem sum_erase (sample : OracleComp spec (Bool ⊕ α)) :
    Sum.map id Subtype.val <$> sum sample = sample := by
  rw [sum, Functor.map_map]
  change (fun result => _) <$> certify sample (fun value => value ∈ support sample) _ = _
  have same : (fun result : {value // value ∈ support sample} =>
      Sum.map id Subtype.val (match result with
        | ⟨.inl decision, _⟩ => Sum.inl decision
        | ⟨.inr context, reached⟩ => Sum.inr ⟨context, reached⟩)) = Subtype.val := by
    funext result
    rcases result with ⟨decision | context, reached⟩ <;> rfl
  rw [same, erase]

/-- Original common/pending continuations receive the same runtime value after support annotation. -/
theorem sum_run (sample : OracleComp spec (Bool ⊕ α)) (next : Bool ⊕ α → OracleComp spec β) :
    (sum sample >>= fun value => next (Sum.map id Subtype.val value)) = sample >>= next := by
  rw [← bind_map_left, sum_erase]

/-- The supported common/pending sampler retains every selective source query bound exactly. -/
theorem sum_bound (sample : OracleComp spec (Bool ⊕ α)) (counted : spec.Domain → Prop)
    [DecidablePred counted] (bound : Nat) :
    (sum sample).IsQueryBoundP counted bound ↔ sample.IsQueryBoundP counted bound := by
  calc
    _ ↔ (Sum.map id Subtype.val <$> sum sample).IsQueryBoundP counted bound := (isQueryBoundP_map_iff _ _ _).symm
    _ ↔ _ := by rw [sum_erase]

end BeaconcryptCore.Computational.RawCtxSupportedSample

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.run

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.query_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.sum_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.sum_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.sum_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.sum_run

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedSample.sum_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedSample.sum_bound
