import BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds

/-!
One selected key is held by the ordinary CTX challenger. Every other operation carries an actual known key, decoder and history slot chosen at that point in the adaptive continuation. Known keys need not be fixed before the run or independent of previous replies. They may even have equal bytes. The reduction performs their real local work and forwards its hash requests to the same challenger cache.

This is an operational factorization of the complete shared state. It does not supply the selected uniform key distribution, target decoder consistency, permitted reveal policy, key-alias bound or a source compiler. The known-call interface is private simulator data, not a network disclosure. Known local AEAD work remains computation and each forwarded oracle query remains charged.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxSharedModes
open AdaptiveCtxSharedTarget hiding replacePublic replaceShared forward_complete forward_schedule forward_step

structure KnownCall where
  slot : Nat
  key : CtxKey
  decode : RawDecoder
  request : ReceiveSpec.Domain

abbrev KnownSpec : OracleSpec KnownCall := fun call => ReceiveSpec.Range call.request
abbrev Spec := ReceiveSpec + KnownSpec

structure SourceState where
  selected : Entry
  others : Nat → Entry
  cache : CtxRO.QueryCache

structure ReductionState where
  others : Nat → Entry
  selectedPublic : List Pqxdh.Bytes

noncomputable def sourceImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl selected => do
      let result ← (simulateQ hashImpl ((localImpl real decode c key selected).run state.selected)).run state.cache
      pure (result.1.1, { state with selected := result.1.2, cache := result.2 })
  | .inr known => do
      let result ← (simulateQ hashImpl
        ((localImpl true known.decode c known.key known.request).run (state.others known.slot))).run state.cache
      pure (result.1.1, { state with others := Function.update state.others known.slot result.1.2, cache := result.2 })

noncomputable def reductionImpl (c : Pqxdh.Crypto) :
    QueryImpl Spec (StateT ReductionState (OracleComp ReceiveSpec)) := fun query state =>
  match query with
  | .inl selected => do
      let answer ← ReceiveSpec.query selected
      pure (answer, { state with selectedPublic := nextPublic selected state.selectedPublic })
  | .inr known => do
      let result ← simulateQ forward
        ((localImpl true known.decode c known.key known.request).run (state.others known.slot))
      pure (result.1, { state with others := Function.update state.others known.slot result.2 })

def project (state : ReductionState × AdaptiveCtxSharedModes.State) : SourceState :=
  ⟨(replacePublic state.2 state.1.selectedPublic).1, state.1.others, state.2.2⟩

noncomputable def linkedImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl Spec (StateT (ReductionState × AdaptiveCtxSharedModes.State) ProbComp) :=
  ((targetImpl real decode c key).mapStateTBase (reductionImpl c)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
/-- Selected requests use only the challenger and retain its actual optional result and all state. -/
theorem selected_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl real decode c key (.inl query)).run (state, selected) =
      (sourceImpl real decode c key (.inl query)).run (project (state, selected)) := by
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (targetImpl real decode c key)
      (do let answer ← ReceiveSpec.query query
          pure (answer, { state with selectedPublic := nextPublic query state.selectedPublic }))).run selected) = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  change _ = (do
    let result ← (simulateQ hashImpl ((localImpl real decode c key query).run
      (project (state, selected)).selected)).run (project (state, selected)).cache
    pure (result.1.1, { project (state, selected) with selected := result.1.2, cache := result.2 }))
  rw [local_from_target]
  have entry : ((project (state, selected)).selected, (project (state, selected)).cache) =
      replacePublic selected state.selectedPublic := rfl
  rw [entry, ← public_history_step real decode c key query selected state.selectedPublic]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A dynamically supplied known key is evaluated locally and shares exactly the selected challenger's complete hash cache. -/
theorem known_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (known : KnownCall) (state : ReductionState) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl real decode c key (.inr known)).run (state, selected) =
      (sourceImpl real decode c key (.inr known)).run (project (state, selected)) := by
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (targetImpl real decode c key)
      (do let result ← simulateQ forward
            ((localImpl true known.decode c known.key known.request).run (state.others known.slot))
          pure (result.1, { state with others := Function.update state.others known.slot result.2 }))).run selected) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  rw [AdaptiveCtxSharedModes.forward_complete]
  change _ = (do
    let result ← (simulateQ hashImpl
      ((localImpl true known.decode c known.key known.request).run (state.others known.slot))).run selected.2
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

def initialReduction : ReductionState := ⟨fun _ => initialEntry, []⟩
def initialSource : SourceState := project (initialReduction, AdaptiveCtxSharedModes.initialState)

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

end BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.known_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.known_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.linked_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.source_view
