import BeaconcryptCore.Computational.AdaptiveCtxSharedModes
import BeaconcryptCore.Computational.RawCtxRoleFamily

/-!
The mixed-mode family runs actual known-key work and forwards the selected key through its ordinary challenger. All local histories, per-key private dictionaries, original public histories and the one common cache remain in the complete state equality. Distinct keys need not have distinct bytes.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxSharedModes
open AdaptiveCtxSharedTarget hiding replacePublic replaceShared forward_complete forward_schedule forward_step

abbrev OtherSpec (count : Nat) := RawCtxRoleFamily.FamilySpec ReceiveSpec count
abbrev FamilySpec (count : Nat) := ReceiveSpec + OtherSpec count
abbrev Others (count : Nat) := Fin count → Entry

structure SourceState (count : Nat) where
  selected : Entry
  others : Others count
  cache : CtxRO.QueryCache

structure ReductionState (count : Nat) where
  others : Others count
  selectedPublic : List Pqxdh.Bytes

noncomputable def sourceImpl {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (SourceState count) ProbComp) := fun query state =>
  match query with
  | .inl selected => do
      let result ← (simulateQ hashImpl
        ((localImpl selectedReal selectedDecode c selectedKey selected).run state.selected)).run state.cache
      pure (result.1.1, { state with selected := result.1.2, cache := result.2 })
  | .inr other => do
      let result ← (simulateQ hashImpl
        ((localImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.others other.1))).run state.cache
      pure (result.1.1, { state with others := Function.update state.others other.1 result.1.2, cache := result.2 })

noncomputable def reductionImpl {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (ReductionState count) (OracleComp ReceiveSpec)) := fun query state =>
  match query with
  | .inl selected => do
      let answer ← ReceiveSpec.query selected
      pure (answer, { state with selectedPublic := nextPublic selected state.selectedPublic })
  | .inr other => do
      let result ← simulateQ forward
        ((localImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.others other.1))
      pure (result.1, { state with others := Function.update state.others other.1 result.2 })

def project {count : Nat} (state : ReductionState count × AdaptiveCtxSharedModes.State) : SourceState count :=
  ⟨(replacePublic state.2 state.1.selectedPublic).1, state.1.others, state.2.2⟩

noncomputable def linkedImpl {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (ReductionState count × AdaptiveCtxSharedModes.State) ProbComp) :=
  ((targetImpl selectedReal selectedDecode c selectedKey).mapStateTBase (reductionImpl real decode c keys)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
theorem linked_selected_run {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState count) (selected : AdaptiveCtxSharedModes.State) :
    (linkedImpl selectedReal selectedDecode real decode c selectedKey keys (.inl query)).run (state, selected) =
      (fun result => (result.1, ({ state with selectedPublic := nextPublic query state.selectedPublic }, result.2))) <$>
        (targetImpl selectedReal selectedDecode c selectedKey query).run selected := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (targetImpl selectedReal selectedDecode c selectedKey)
      (do let answer ← ReceiveSpec.query query
          pure (answer, { state with selectedPublic := nextPublic query state.selectedPublic }))).run selected = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
theorem selected_step {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState count) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl selectedReal selectedDecode real decode c selectedKey keys (.inl query)).run (state, selected) =
      (sourceImpl selectedReal selectedDecode real decode c selectedKey keys (.inl query)).run (project (state, selected)) := by
  rw [linked_selected_run]
  change _ = (do
    let result ← (simulateQ hashImpl ((localImpl selectedReal selectedDecode c selectedKey query).run
      (project (state, selected)).selected)).run (project (state, selected)).cache
    pure (result.1.1, { project (state, selected) with selected := result.1.2, cache := result.2 }))
  rw [local_from_target]
  have entry : ((project (state, selected)).selected, (project (state, selected)).cache) =
      replacePublic selected state.selectedPublic := rfl
  rw [entry, ← public_history_step selectedReal selectedDecode c selectedKey query selected state.selectedPublic]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem linked_other_run {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (other : (OtherSpec count).Domain) (state : ReductionState count) (selected : AdaptiveCtxSharedModes.State) :
    (linkedImpl selectedReal selectedDecode real decode c selectedKey keys (.inr other)).run (state, selected) =
      (fun result => (result.1.1, ({ state with others := Function.update state.others other.1 result.1.2 }, result.2))) <$>
        (simulateQ (targetImpl selectedReal selectedDecode c selectedKey) (simulateQ forward
          ((localImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.others other.1)))).run selected := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (targetImpl selectedReal selectedDecode c selectedKey)
      (do let result ← simulateQ forward ((localImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.others other.1))
          pure (result.1, { state with others := Function.update state.others other.1 result.2 }))).run selected = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
theorem other_step {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (other : (OtherSpec count).Domain) (state : ReductionState count) (selected : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl selectedReal selectedDecode real decode c selectedKey keys (.inr other)).run (state, selected) =
      (sourceImpl selectedReal selectedDecode real decode c selectedKey keys (.inr other)).run (project (state, selected)) := by
  rw [linked_other_run, AdaptiveCtxSharedModes.forward_complete]
  change _ = (do
    let result ← (simulateQ hashImpl
      ((localImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.others other.1))).run selected.2
    pure (result.1.1, { project (state, selected) with
      others := Function.update state.others other.1 result.1.2, cache := result.2 }))
  rw [← cache_schedule _ (selected.2, selected.1.1.publicInputs)]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

theorem linked_step {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : ReductionState count × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl selectedReal selectedDecode real decode c selectedKey keys query).run state =
      (sourceImpl selectedReal selectedDecode real decode c selectedKey keys query).run (project state) := by
  cases query with
  | inl selected => exact selected_step selectedReal selectedDecode real decode c selectedKey keys selected state.1 state.2
  | inr other => exact other_step selectedReal selectedDecode real decode c selectedKey keys other state.1 state.2

theorem linked_schedule {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (state : ReductionState count × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (simulateQ (linkedImpl selectedReal selectedDecode real decode c selectedKey keys) client).run state =
      (simulateQ (sourceImpl selectedReal selectedDecode real decode c selectedKey keys) client).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq (linkedImpl selectedReal selectedDecode real decode c selectedKey keys)
    (sourceImpl selectedReal selectedDecode real decode c selectedKey keys) project
      (linked_step selectedReal selectedDecode real decode c selectedKey keys) client state

noncomputable def wrapped {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (state : ReductionState count) : OracleComp ReceiveSpec (Result × ReductionState count) :=
  (simulateQ (reductionImpl real decode c keys) client).run state

def erase {count : Nat} {Result : Type} (result : (Result × ReductionState count) × AdaptiveCtxSharedModes.State) :
    Result × SourceState count := (result.1.1, project (result.1.2, result.2))

theorem schedule_interpretation {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (state : ReductionState count) (selected : AdaptiveCtxSharedModes.State) :
    erase <$> (simulateQ (targetImpl selectedReal selectedDecode c selectedKey) (wrapped real decode c keys client state)).run selected =
      (simulateQ (sourceImpl selectedReal selectedDecode real decode c selectedKey keys) client).run (project (state, selected)) := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map]
  exact linked_schedule selectedReal selectedDecode real decode c selectedKey keys client (state, selected)


def initialReduction (count : Nat) : ReductionState count := ⟨fun _ => initialEntry, []⟩
def initialSource (count : Nat) : SourceState count := ⟨initialEntry, fun _ => initialEntry, ∅⟩

theorem initial_projection (count : Nat) :
    project (initialReduction count, AdaptiveCtxSharedModes.initialState) = initialSource count := rfl

noncomputable def sourceGame {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) : ProbComp (Result × SourceState count) := do
  let selectedKey ← $ᵗ CtxKey
  (simulateQ (sourceImpl selectedReal selectedDecode real decode c selectedKey keys) client).run (initialSource count)

theorem uniform_interpretation {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) :
    sourceGame selectedReal selectedDecode real decode c keys client =
      erase <$> targetGame selectedReal selectedDecode c (wrapped real decode c keys client (initialReduction count)) := by
  simp only [sourceGame, targetGame, map_bind, schedule_interpretation, initial_projection]

noncomputable def decisionClient {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool) :
    OracleComp ReceiveSpec Bool := Prod.fst <$> wrapped real decode c keys client (initialReduction count)

theorem source_view_eq {count : Nat} (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) :
    Prod.fst <$> sourceGame selectedReal selectedDecode real decode c keys client =
      targetView selectedReal selectedDecode c (decisionClient real decode c keys client) := by
  rw [uniform_interpretation]
  simp only [targetView, targetGame, decisionClient, map_bind, simulateQ_map, StateT.run_map,
    Functor.map_map, erase]

end BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_selected_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_selected_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_other_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_other_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.other_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.other_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.linked_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.initial_projection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.initial_projection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.uniform_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.uniform_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.source_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily.source_view_eq
