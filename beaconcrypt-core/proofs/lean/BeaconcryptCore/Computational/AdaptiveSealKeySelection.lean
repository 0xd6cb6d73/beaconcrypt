import BeaconcryptCore.Computational.AdaptiveSealKeyFamily

/-!
The actual finite key sampler is partitioned at each original index under its complete evaluated continuation. Every selected and unselected history is reconstructed, preserving possible equal sampled key values and challenger-first generation order.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveSealKeySelection
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open RawKeyPartition AdaptiveSealKeyFamily

noncomputable def select {count : Nat} (target : Fin (count + 1)) :
    QueryImpl (Spec (count + 1)) (OracleComp (SplitSpec count)) :=
  fun query => match finSuccEquiv' target query.1 with
  | none => (SplitSpec count).query (.inl query.2)
  | some other => (SplitSpec count).query (.inr ⟨other, query.2⟩)

noncomputable def combine {count : Nat} (target : Fin (count + 1))
    (state : SplitState count) : State (count + 1) := join target state.2 state.1

set_option backward.isDefEq.respectTransparency false in
theorem selected_step {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (real : Fin count → Bool) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (Spec (count + 1)).Domain) (state : SplitState count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (splitImpl targetReal real c targetKey keys) (select target query)).run state =
      (familyImpl c (join target targetKey keys) (join target targetReal real) query).run (combine target state) := by
  obtain ⟨index, query⟩ := query
  obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
  cases position with
  | none =>
      simp only [finSuccEquiv'_symm_none, select, finSuccEquiv'_at,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        familyImpl, splitImpl, StateT.run, combine,
        join_target, bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      rw [join_selected_update target state.2 result.2 state.1]
  | some other =>
      simp only [finSuccEquiv'_symm_some, select, finSuccEquiv'_succAbove,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        familyImpl, splitImpl, StateT.run, combine,
        join_other, bind_pure_comp, Functor.map_map, join_other_update]

set_option backward.isDefEq.respectTransparency false in
theorem selected_schedule {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (real : Fin count → Bool) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (Spec (count + 1)) Result) (state : SplitState count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (splitImpl targetReal real c targetKey keys) (simulateQ (select target) client)).run state =
      (simulateQ (familyImpl c (join target targetKey keys) (join target targetReal real)) client).run (combine target state) := by
  simpa only [QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
    map_run_simulateQ_eq_of_query_map_eq
      ((splitImpl targetReal real c targetKey keys) ∘ₛ select target)
      (familyImpl c (join target targetKey keys) (join target targetReal real))
      (combine target) (selected_step target targetReal real c targetKey keys) client state

noncomputable def sourceGame {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp (Spec count) Result) :
    ProbComp (Result × State count) := do
  let keys ← $ᵗ (Fin count → CtxKey)
  (simulateQ (familyImpl c keys real) client).run (initialState count)

set_option backward.isDefEq.respectTransparency false in
theorem fixed_source_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (real : Fin count → Bool) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (Spec (count + 1)) Result) :
    (simulateQ (familyImpl c (join target targetKey keys) (join target targetReal real)) client).run (initialState (count + 1)) =
      (fun result => (result.1, combine target result.2)) <$>
        (simulateQ (splitImpl targetReal real c targetKey keys) (simulateQ (select target) client)).run
          (initialState count, emptyModifiedNonceAeadHandlerState) := by
  have complete := (selected_schedule target targetReal real c targetKey keys client
      (initialState count, emptyModifiedNonceAeadHandlerState)).symm
  have initial : combine target (initialState count, emptyModifiedNonceAeadHandlerState) = initialState (count + 1) :=
    join_constant target emptyModifiedNonceAeadHandlerState
  rw [initial] at complete
  exact complete

noncomputable def prepared {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp (Spec (count + 1)) Result) :
    OracleComp ModifiedNonceAeadAdversarySpec (Result × State count) := do
  let keys ← OracleComp.liftComp ($ᵗ (Fin count → CtxKey)) ModifiedNonceAeadAdversarySpec
  wrapped real c keys (simulateQ (select target) client) (initialState count)

noncomputable def reconstruct {count : Nat} {Result : Type} (target : Fin (count + 1))
    (result : (Result × State count) × ModifiedNonceAeadHandlerState) : Result × State (count + 1) :=
  (result.1.1, join target result.2 result.1.2)

set_option backward.isDefEq.respectTransparency false in
theorem prepared_run {count : Nat} (target : Fin (count + 1)) (targetReal : Bool)
    (real : Fin count → Bool) (c : Pqxdh.Crypto) (targetKey : CtxKey)
    {Result : Type} (client : OracleComp (Spec (count + 1)) Result)
    (state : ModifiedNonceAeadHandlerState) :
    (simulateQ (localImpl targetReal c targetKey) (prepared target real c client)).run state =
      (do
        let keys ← $ᵗ (Fin count → CtxKey)
        (simulateQ (localImpl targetReal c targetKey)
           (wrapped real c keys (simulateQ (select target) client) (initialState count))).run state) := by
  simp only [prepared, simulateQ_bind]
  rw [StateT.run_bind, targetUniform]
  simp only [bind_map_left]

/-- The finite key partition retains the full evaluated continuation and actual challenger-first generator order. -/
theorem source_prepared_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (real : Fin count → Bool) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp (Spec (count + 1)) Result) :
    𝒮[sourceGame (join target targetReal real) c client] =
      𝒮[do
        let key ← $ᵗ CtxKey
        reconstruct target <$> (simulateQ (localImpl targetReal c key)
          (prepared target real c client)).run emptyModifiedNonceAeadHandlerState] := by
  unfold sourceGame
  rw [partition_continuation_vcvioLegacy count target]
  simp only [prepared_run, fixed_source_selection, schedule_interpretation, map_bind, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.AdaptiveSealKeySelection

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeySelection.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeySelection.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeySelection.selected_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeySelection.selected_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeySelection.fixed_source_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeySelection.fixed_source_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeySelection.prepared_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeySelection.prepared_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeySelection.source_prepared_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeySelection.source_prepared_selection
