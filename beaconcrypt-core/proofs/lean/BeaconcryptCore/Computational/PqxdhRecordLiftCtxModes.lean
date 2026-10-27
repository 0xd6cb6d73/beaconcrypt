-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds

/-! Dynamic known-key calls may already be in the replay hybrid. Their actual local programs keep one shared cache with the selected challenger; the reduction receives no selected key. This component does not supply a source key distribution or a global record compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxSharedModes
open AdaptiveCtxSharedTarget hiding replacePublic replaceShared forward_complete forward_schedule forward_step
open AdaptiveCtxDynamicKnownKeys (SourceState ReductionState project erase initialReduction initialSource)

/-- The known key, decoder, history slot and real/replay mode are chosen by the actual adaptive simulator. This is a private compiler interface. -/
structure KnownCall extends AdaptiveCtxDynamicKnownKeys.KnownCall where
  real : Bool

abbrev KnownSpec : OracleSpec KnownCall := fun call => ReceiveSpec.Range call.request
abbrev Spec := ReceiveSpec + KnownSpec

/-- Every target or known-key operation retains its local history and the same shared public cache. -/
noncomputable def sourceImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl selected => do
      let result ← (simulateQ hashImpl ((localImpl real decode c key selected).run state.selected)).run state.cache
      pure (result.1.1, { state with selected := result.1.2, cache := result.2 })
  | .inr known => do
      let result ← (simulateQ hashImpl
        ((localImpl known.real known.decode c known.key known.request).run (state.others known.slot))).run state.cache
      pure (result.1.1, { state with others := Function.update state.others known.slot result.1.2, cache := result.2 })

/-- Actual known-key work and its private sampling are forwarded through the selected challenger's hash/coin interface. No selected key is an argument. -/
noncomputable def reductionImpl (c : Pqxdh.Crypto) :
    QueryImpl Spec (StateT ReductionState (OracleComp ReceiveSpec)) := fun query state =>
  match query with
  | .inl selected => do
      let answer ← ReceiveSpec.query selected
      pure (answer, { state with selectedPublic := nextPublic selected state.selectedPublic })
  | .inr known => do
      let result ← simulateQ forward
        ((localImpl known.real known.decode c known.key known.request).run (state.others known.slot))
      pure (result.1, { state with others := Function.update state.others known.slot result.2 })

noncomputable def linkedImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT (ReductionState × AdaptiveCtxSharedModes.State) ProbComp) :=
  ((targetImpl real decode c key).mapStateTBase (reductionImpl c)).flattenStateT

/-- The selected callback is unchanged, retaining its actual optional result and full state. -/
theorem selected_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl real decode c key (.inl query)).run (state, selected) =
      (sourceImpl real decode c key (.inl query)).run (project (state, selected)) := by
  exact AdaptiveCtxDynamicKnownKeys.selected_step real decode c key query state selected

set_option backward.isDefEq.respectTransparency false in
/-- A dynamic known-key call can be real or replay-mode; both retain their complete private dictionary and share the selected challenger's exact public cache. -/
theorem known_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (known : KnownCall) (state : ReductionState) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl real decode c key (.inr known)).run (state, selected) =
      (sourceImpl real decode c key (.inr known)).run (project (state, selected)) := by
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (targetImpl real decode c key)
      (do let result ← simulateQ forward
            ((localImpl known.real known.decode c known.key known.request).run (state.others known.slot))
          pure (result.1, { state with others := Function.update state.others known.slot result.2 }))).run selected) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  rw [AdaptiveCtxSharedModes.forward_complete]
  change _ = (do
    let result ← (simulateQ hashImpl
      ((localImpl known.real known.decode c known.key known.request).run (state.others known.slot))).run selected.2
    pure (result.1.1, { project (state, selected) with
      others := Function.update state.others known.slot result.1.2, cache := result.2 }))
  rw [← cache_schedule _ (selected.2, selected.1.1.publicInputs)]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- Every selected or dynamically keyed callback preserves the original complete source state. -/
theorem linked_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : Spec.Domain) (state : ReductionState × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl real decode c key query).run state =
      (sourceImpl real decode c key query).run (project state) := by
  cases query with
  | inl query => exact selected_step real decode c key query state.1 state.2
  | inr known => exact known_step real decode c key known state.1 state.2

/-- Arbitrary adaptive known-key generation and selected optional replies preserve every local history and the shared cache. -/
theorem linked_schedule (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp Spec Result)
    (state : ReductionState × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (simulateQ (linkedImpl real decode c key) client).run state =
      (simulateQ (sourceImpl real decode c key) client).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (linked_step real decode c key) client state

noncomputable def wrapped (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp Spec Result)
    (state : ReductionState) : OracleComp ReceiveSpec (Result × ReductionState) :=
  (simulateQ (reductionImpl c) client).run state

def erase {Result : Type} (result : (Result × ReductionState) × AdaptiveCtxSharedModes.State) :
    Result × SourceState := (result.1.1, project (result.1.2, result.2))

/-- The actual one-key reduction contains no selected key argument; interpreting it by the challenger gives the same entire source execution. -/
theorem schedule_interpretation (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp Spec Result) (state : ReductionState)
    (selected : AdaptiveCtxSharedModes.State) :
    erase <$> (simulateQ (targetImpl real decode c key) (wrapped c client state)).run selected =
      (simulateQ (sourceImpl real decode c key) client).run (project (state, selected)) := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map]
  exact linked_schedule real decode c key client (state, selected)

/-- Only the selected key is sampled in this endpoint; every known key is generated by its actual adaptive caller. -/
noncomputable def sourceGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp Spec Result) : ProbComp (Result × SourceState) := do
  let key ← $ᵗ CtxKey
  (simulateQ (sourceImpl real decode c key) client).run initialSource

noncomputable def decisionClient (c : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    OracleComp ReceiveSpec Bool := Prod.fst <$> wrapped c client initialReduction

/-- The same complete adaptive source decision is exactly the constructed ordinary one-key CTX client, with known-key work sharing its cache. -/
theorem source_view (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp Spec Bool) :
    Prod.fst <$> sourceGame real decode c client =
      targetView real decode c (decisionClient c client) := by
  simp only [sourceGame, targetView, targetGame, decisionClient, map_bind,
    simulateQ_map, StateT.run_map, Functor.map_map]
  apply bind_congr
  intro key
  have exactRun := congrArg (fun work => Prod.fst <$> work)
    (schedule_interpretation real decode c key client initialReduction AdaptiveCtxSharedModes.initialState)
  simpa only [Functor.map_map, erase, initialSource] using exactRun.symm

/-- Existing real-only dynamic clients enter the enlarged private interface unchanged. -/
def realLift : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (OracleComp Spec)
  | .inl query => Spec.query (.inl query)
  | .inr known => Spec.query (.inr ⟨known, true⟩)

/-- The new simulation exactly contains the prior real-only interpreter, without changing any local state or reply. -/
theorem real_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain) :
    (sourceImpl real decode c key ∘ₛ realLift) query =
      AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key query := by
  cases query <;> simp only [QueryImpl.compose, realLift, simulateQ_spec_query] <;> rfl

/-- Every existing adaptive real-known-key client is the same complete experiment after the embedding. -/
theorem real_schedule (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    simulateQ (sourceImpl real decode c key) (simulateQ realLift client) =
      simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) client := by
  rw [← QueryImpl.simulateQ_compose]
  have same : sourceImpl real decode c key ∘ₛ realLift =
      AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key := funext (real_step real decode c key)
  rw [same]

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.selected_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.known_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.known_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.linked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.linked_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.source_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.real_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.real_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.real_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxModes.real_schedule
