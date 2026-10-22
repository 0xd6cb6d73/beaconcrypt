-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSeedRelay
import BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy
import BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy

/-! Identify the independent seed endpoint `PqxdhRecordLiftGlobalSeedCut.seedUniform` with the adjacent concrete mixed policy in which the selected initial coordinate `(slot, direction, start direction)` is ideal. Only native and uniform analysis counters are projected away on the proof side; every source byte, the shared ROM cache, the seeds, the complete chain table and both frame logs remain. The supported-prefix lemmas of the second part (a supported query is reached, its continuation reaches a supported final state, and a lookup whose coordinate is absent from every final table never occurs) are generic over the private Protocol interpreter and are reused by the chain hybrid. Adapted from Codex's seed-policy plan (`codex/deployment-record-wip@023b9a81:doc/impl/handover/record-lift-wip/codex-plan-seed-policy.md`, SHA-256 `02cb4c6516c6bc060b1c0eaa715274c54e04a804d206557b6a91fd1109d6f11d`); the proofs follow the published `PqxdhRecordLiftChildPolicy`. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
variable {n : Nat}

/-! ### The selected initial coordinate -/

/-- The single coordinate whose source input is the selected seed half. -/
def initial (state : PqxdhRecordLiftGlobalSeedCut.Mask n) : Coordinate (Slot n) :=
  ⟨state.slot, state.direction, start state.direction⟩

/-- The structural seed reader is exactly the selected initial coordinate. -/
theorem reads_iff (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (coordinate : Coordinate (Slot n)) :
    PqxdhRecordLiftGlobalSeedCut.Reads state coordinate ↔ coordinate = initial state := by
  constructor
  · rintro ⟨slot, direction, position⟩
    cases coordinate
    simp_all only [initial]
  · intro same
    subst coordinate
    exact ⟨rfl, rfl, rfl⟩

/-- Only the selected initial lookup can need the relay's child. -/
theorem needs_lookup (ideal : Coordinate (Slot n) → Bool) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (query : Service n) (needs : PqxdhRecordLiftSeedRelay.Needs ideal state query) :
    query = .lookup (initial state) := by
  cases query with
  | lookup coordinate => rw [(reads_iff state coordinate).mp needs.2]
  | _ => exact needs.elim

/-- Every seed-mask service keeps the selected slot, direction and retained opposite half. -/
theorem interpreter_fixed {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (ideal : Coordinate (Slot n) → Bool)
    (filling : PqxdhSecretInputKdf.RootOutput) (child : FullOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (result : (ServiceSpec n).Range query × PqxdhRecordLiftGlobalSeedCut.Mask n)
    (supported : result ∈ support ((PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child
      setup codec query).run state)) :
    result.2.slot = state.slot ∧ result.2.direction = state.direction ∧ result.2.other = state.other := by
  cases query with
  | allocate slot =>
      simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, StateT.run,
        PqxdhRecordLiftGlobalSeedCut.allocate] at supported
      split_ifs at supported with same
      · rw [mem_support_pure_iff] at supported
        subst result
        exact ⟨rfl, rfl, rfl⟩
      · simp only [PqxdhRecordLiftGlobalSeedCut.withPrivate, StateT.run, bind_pure_comp,
          support_map, Set.mem_image] at supported
        obtain ⟨inner, _, rfl⟩ := supported
        exact ⟨rfl, rfl, rfl⟩
  | lookup coordinate =>
      simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, PqxdhRecordLiftGlobalSeedCut.lookup,
        StateT.run] at supported
      split_ifs at supported
      · split at supported
        · rw [mem_support_pure_iff] at supported
          subst result
          exact ⟨rfl, rfl, rfl⟩
        · simp only [bind_pure_comp, support_map, Set.mem_image] at supported
          obtain ⟨inner, _, rfl⟩ := supported
          exact ⟨rfl, rfl, rfl⟩
      all_goals
        rw [mem_support_pure_iff] at supported
        subst result
        exact ⟨rfl, rfl, rfl⟩
  | _ =>
      simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, PqxdhRecordLiftGlobalSeedCut.withPrivate,
        StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact ⟨rfl, rfl, rfl⟩

/-- The state view erases only native and uniform analysis counts; the selected seed half is restored solely for this proof-side comparison. -/
noncomputable def view (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) : PqxdhRecordLiftCtxProtocol.Bare n :=
  PqxdhRecordLiftCtxProtocol.erasePrivate (PqxdhRecordLiftGlobalSeedCut.realize hidden state)

/-- Every service other than the selected initial lookup has the unchanged concrete source law under the adjacent policy, including optional failure replies and complete public-effect, seed, table and log state. -/
theorem different_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (filling : PqxdhSecretInputKdf.RootOutput) (child : FullOutput) (hidden : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (different : query ≠ .lookup (initial state)) :
    Prod.map id (view hidden) <$>
      (PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child setup codec query).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (initial state) true) query).run (view hidden state) := by
  have unused : ¬ PqxdhRecordLiftSeedRelay.Needs ideal state query :=
    fun needs => different (needs_lookup ideal state query needs)
  rw [PqxdhRecordLiftSeedRelay.unused_source setup.source ideal filling setup codec query state child
    (PqxdhJointKdf.productionStream setup.source.crypto
      (PqxdhJointKdfGame.FixedHkdfDomain.ratchet.address hidden.toList)) unused]
  have sourceLaw := congrArg (fun work => Prod.map id PqxdhRecordLiftCtxProtocol.erasePrivate <$> work)
    (PqxdhRecordLiftGlobalSeedCut.interpreter_realization setup.source ideal filling hidden setup codec query state)
  rw [PqxdhRecordLiftCtxProtocol.bare_query] at sourceLaw
  simp only [Functor.map_map] at sourceLaw
  apply sourceLaw.trans
  cases query with
  | lookup coordinate =>
      have unequal : coordinate ≠ initial state := fun same => different (congrArg Service.lookup same)
      simp only [PqxdhRecordLiftCtxProtocol.bareInterpreter, PqxdhRecordLiftCtxOracle.bareLookup,
        StateT.run, Function.update_of_ne unequal]
      rfl
  | _ => rfl

/-- The persistent child cell tracks the literal table entry of the selected initial coordinate. -/
def CellMatches (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput) : Prop :=
  state.before.chain (initial state) = cell

/-- The selected initial coordinate is real in the current policy. -/
def Ready (ideal : Coordinate (Slot n) → Bool) (state : PqxdhRecordLiftGlobalSeedCut.Mask n) : Prop :=
  ideal (initial state) = false

def putChild (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (child : FullOutput) :
    PqxdhRecordLiftGlobalSeedCut.Mask n :=
  PqxdhRecordLiftGlobalSeedCut.putLookup state (state.before.chain.cacheQuery (initial state) child)
    (PqxdhRecordLiftChainOracle.charge state.before.primitive)

/-- The actual real initial lookup overwrites its own cached response with the supplied full76, charges its native KDF call and keeps every other private field. -/
theorem lookup_child {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (filling : PqxdhSecretInputKdf.RootOutput) (child : FullOutput)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (ready : Ready ideal state) :
    (PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child setup codec
      (.lookup (initial state))).run state = pure ((), putChild state child) := by
  have reads : PqxdhRecordLiftGlobalSeedCut.Reads state (initial state) := (reads_iff state _).mpr rfl
  have real : ideal (initial state) = false := ready
  simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, PqxdhRecordLiftGlobalSeedCut.lookup, StateT.run,
    real, Bool.false_eq_true, ite_false, reads, ite_true]
  rfl

noncomputable def relayQuery {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput) :=
  (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
    ((PqxdhRecordLiftSeedRelay.interpreter setup.source ideal filling setup codec query).run state)).run cell

/-- The first real initial read samples once; later reads reuse the exact full76 stored in the persistent cell. The source still executes and charges its own lookup each time. -/
theorem relay_child {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput) (ready : Ready ideal state) :
    relayQuery ideal setup codec filling (.lookup (initial state)) state cell =
      match cell with
      | some child => pure (((), putChild state child), some child)
      | none => (fun child => (((), putChild state child), some child)) <$> ($ᵗ FullOutput) := by
  have needs : PqxdhRecordLiftSeedRelay.Needs ideal state (.lookup (initial state)) :=
    ⟨ready, (reads_iff state _).mpr rfl⟩
  simp only [relayQuery, PqxdhRecordLiftSeedRelay.interpreter, StateT.run, needs, ite_true,
    simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftDeferredChild.lazyImpl]
  change ((PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput) (.inl ()) >>= fun child =>
    simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
      (simulateQ PqxdhRecordLiftChildRelay.coinLift
        ((PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child setup codec
          (.lookup (initial state))).run state)))).run cell = _
  simp_rw [lookup_child ideal setup codec filling _ state ready]
  simp only [simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do let value ← (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput) (.inl ())).run cell
             pure (((), putChild state value.1), value.2)) = _
  cases cell <;> simp only [PqxdhRecordLiftDeferredChild.lazyImpl, StateT.run, bind_pure_comp,
    Functor.map_map, map_pure]
  rfl

/-- Restoring the seed commutes with the exact initial cache write and erases only the native KDF count increment. -/
theorem view_putChild (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (child : FullOutput) :
    view hidden (putChild state child) =
      { view hidden state with chain := (view hidden state).chain.cacheQuery (initial state) child } := by
  simp only [view, PqxdhRecordLiftCtxProtocol.erasePrivate, PqxdhRecordLiftGlobalSeedCut.realize,
    putChild, PqxdhRecordLiftGlobalSeedCut.putLookup, PqxdhRecordLiftChainOracle.charge, initial]

/-- The cell relation keeps the literal initial table entry, not an independent projection sample. -/
theorem view_child (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput) (agrees : CellMatches state cell) :
    (view hidden state).chain (initial state) = cell := agrees

/-- At the selected initial coordinate, the relay and the adjacent concrete ideal lookup return the same complete counter-erased source state for both the first miss and repeated hits. -/
theorem child_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (hidden : PqxdhSecretInputKdf.RootOutput) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (cell : Option FullOutput) (ready : Ready ideal state) (agrees : CellMatches state cell) :
    (fun result => (result.1.1, view hidden result.1.2)) <$>
      relayQuery ideal setup codec filling (.lookup (initial state)) state cell =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (initial state) true)
        (.lookup (initial state))).run (view hidden state) := by
  rw [relay_child ideal setup codec filling state cell ready]
  simp only [PqxdhRecordLiftCtxProtocol.bareInterpreter, StateT.run,
    PqxdhRecordLiftCtxOracle.bareLookup, Function.update_self, ite_true,
    view_child hidden state cell agrees]
  cases cell with
  | none =>
      simp only [Functor.map_map, bind_pure_comp, view_putChild]
  | some child =>
      have cached := view_child hidden state (some child) agrees
      have unchanged : (view hidden state).chain.cacheQuery (initial state) child =
          (view hidden state).chain := by
        apply QueryCache.ext
        intro query
        by_cases same : query = initial state
        · subst query
          simp only [QueryCache.cacheQuery_self, cached]
        · exact QueryCache.cacheQuery_of_ne _ _ same
      simp only [map_pure, pure_bind, view_putChild, unchanged]

/-- The relay requests its child exactly at the selected initial lookup. -/
theorem needs_iff (ideal : Coordinate (Slot n) → Bool) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (query : Service n) (ready : Ready ideal state) :
    PqxdhRecordLiftSeedRelay.Needs ideal state query ↔ query = .lookup (initial state) := by
  constructor
  · exact needs_lookup ideal state query
  · intro same
    subst query
    exact ⟨ready, (reads_iff state _).mpr rfl⟩

/-- A service outside the selected initial lookup forwards its whole original computation and leaves the persistent cell unchanged. -/
theorem relay_different {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput)
    (different : query ≠ .lookup (initial state)) :
    relayQuery ideal setup codec filling query state cell =
      (fun result => (result, cell)) <$>
        (PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling
          PqxdhRecordLiftChildRelay.unusedChild setup codec query).run state := by
  have unused : ¬ PqxdhRecordLiftSeedRelay.Needs ideal state query :=
    fun needs => different (needs_lookup ideal state query needs)
  simp only [relayQuery, PqxdhRecordLiftSeedRelay.interpreter, StateT.run, unused, ite_false, pure_bind]
  change (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
    (simulateQ PqxdhRecordLiftChildRelay.coinLift
      ((PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling PqxdhRecordLiftChildRelay.unusedChild
        setup codec query).run state))).run cell = _
  exact PqxdhRecordLiftChildPolicy.coin_lazy _ _ _

/-- Every private service of the lazy-child relay agrees with the adjacent concrete policy on the complete counter-erased source state. -/
theorem query_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (hidden : PqxdhSecretInputKdf.RootOutput) (query : Service n)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput)
    (ready : Ready ideal state) (agrees : CellMatches state cell) :
    (fun result => (result.1.1, view hidden result.1.2)) <$> relayQuery ideal setup codec filling query state cell =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (initial state) true) query).run (view hidden state) := by
  by_cases selected : query = .lookup (initial state)
  · subst query
    exact child_source ideal setup codec filling hidden state cell ready agrees
  · rw [relay_different ideal setup codec filling query state cell selected, Functor.map_map]
    exact different_source ideal setup codec filling _ hidden query state selected

/-- Every other complete source service preserves the exact initial table entry, including failed native operations and unrelated random lookups. -/
theorem different_entry {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (child : FullOutput) (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (different : query ≠ .lookup (initial state))
    (result : (ServiceSpec n).Range query × PqxdhRecordLiftGlobalSeedCut.Mask n)
    (supported : result ∈ support ((PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child
      setup codec query).run state)) :
    result.2.before.chain (initial result.2) = state.before.chain (initial state) := by
  have fixed := interpreter_fixed setup.source ideal filling child setup codec query state result supported
  have sameInitial : initial result.2 = initial state := by
    simp only [initial, fixed.1, fixed.2.1]
  have unused : ¬ PqxdhRecordLiftSeedRelay.Needs ideal state query :=
    fun needs => different (needs_lookup ideal state query needs)
  rw [PqxdhRecordLiftSeedRelay.unused_source setup.source ideal filling setup codec query state child
    (PqxdhJointKdf.productionStream setup.source.crypto
      (PqxdhJointKdfGame.FixedHkdfDomain.ratchet.address filling.toList)) unused] at supported
  have actual : (result.1, PqxdhRecordLiftGlobalSeedCut.realize filling result.2) ∈
      support ((PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
        setup codec query).run (PqxdhRecordLiftGlobalSeedCut.realize filling state)) := by
    rw [← PqxdhRecordLiftGlobalSeedCut.interpreter_realization setup.source ideal filling filling setup codec
      query state, support_map]
    exact ⟨result, supported, rfl⟩
  have avoids : PqxdhRecordLiftFirstLookup.Avoids (initial state) query := by
    cases query <;> simp_all only [PqxdhRecordLiftFirstLookup.Avoids, ne_eq, Service.lookup.injEq,
      not_false_eq_true]
  have same := PqxdhRecordLiftFirstLookup.query_other setup.source ideal setup codec
    (initial state) query avoids _ _ actual
  rw [sameInitial]
  simpa only [PqxdhRecordLiftGlobalSeedCut.realize] using same

/-- The single-step relay keeps its selected slot and direction, readiness and the child-cell/cache invariant under every actual reply. -/
theorem query_invariant {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalSeedCut.Mask n) (cell : Option FullOutput)
    (ready : Ready ideal state) (agrees : CellMatches state cell)
    (result : ((ServiceSpec n).Range query × PqxdhRecordLiftGlobalSeedCut.Mask n) × Option FullOutput)
    (supported : result ∈ support (relayQuery ideal setup codec filling query state cell)) :
    initial result.1.2 = initial state ∧ Ready ideal result.1.2 ∧ CellMatches result.1.2 result.2 := by
  by_cases selected : query = .lookup (initial state)
  · subst query
    rw [relay_child ideal setup codec filling state cell ready] at supported
    cases cell with
    | none =>
        rw [support_map] at supported
        obtain ⟨child, _, rfl⟩ := supported
        refine ⟨rfl, ready, ?_⟩
        simp only [CellMatches, putChild, PqxdhRecordLiftGlobalSeedCut.putLookup, initial,
          QueryCache.cacheQuery_self]
    | some child =>
        rw [mem_support_pure_iff] at supported
        subst result
        refine ⟨rfl, ready, ?_⟩
        simp only [CellMatches, putChild, PqxdhRecordLiftGlobalSeedCut.putLookup, initial,
          QueryCache.cacheQuery_self]
  · rw [relay_different ideal setup codec filling query state cell selected, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have fixed := interpreter_fixed setup.source ideal filling PqxdhRecordLiftChildRelay.unusedChild setup codec
      query state inner member
    have sameInitial : initial inner.2 = initial state := by
      simp only [initial, fixed.1, fixed.2.1]
    refine ⟨sameInitial, ?_, ?_⟩
    · simpa only [Ready, sameInitial] using ready
    · exact (different_entry ideal setup codec filling _ query state selected inner member).trans agrees

abbrev State (n : Nat) := PqxdhRecordLiftGlobalSeedCut.Mask n × Option FullOutput

def Good (selected : Coordinate (Slot n)) (ideal : Coordinate (Slot n) → Bool) (state : State n) : Prop :=
  initial state.1 = selected ∧ Ready ideal state.1 ∧ CellMatches state.1 state.2

/-- Flatten only the extra child-cell transformer, retaining every original field. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput) :
    QueryImpl (ServiceSpec n) (StateT (State n) ProbComp) := fun query state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> relayQuery ideal setup codec filling query state.1 state.2

/-- The flattened relay preserves the fixed initial coordinate and the exact cell relation under every supported reply. -/
theorem step_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (selected : Coordinate (Slot n)) (query : Service n) (state : State n) (good : Good selected ideal state)
    (result : (ServiceSpec n).Range query × State n)
    (supported : result ∈ support ((interpreter ideal setup codec filling query).run state)) :
    Good selected ideal result.2 := by
  simp only [interpreter, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have actual := query_invariant ideal setup codec filling query state.1 state.2 good.2.1 good.2.2 inner member
  exact ⟨actual.1.trans good.1, actual.2⟩

/-- The entire adaptive relay equals the adjacent concrete source interpreter after only native and uniform count erasure and removal of the additional cell. -/
theorem schedule_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (hidden : PqxdhSecretInputKdf.RootOutput) (selected : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : State n) (good : Good selected ideal state) :
    Prod.map id (fun state : State n => view hidden state.1) <$>
      (simulateQ (interpreter ideal setup codec filling) client).run state =
      (simulateQ (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal selected true)) client).run (view hidden state.1) := by
  apply map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Good selected ideal)
    (fun state : State n => view hidden state.1)
    (step_good ideal setup codec filling selected) ?_ client state good
  intro query before ready
  have actual := query_source ideal setup codec filling hidden query before.1 before.2 ready.2.1 ready.2.2
  simpa only [interpreter, StateT.run, Functor.map_map, ready.1, Prod.map_def, id_eq] using actual

/-- Flattening the extra child-cell transformer preserves the literal complete execution, before any source-state projection. -/
theorem flatten_run {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (cell : Option FullOutput) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
        ((simulateQ (PqxdhRecordLiftSeedRelay.interpreter setup.source ideal filling setup codec) client).run
          state)).run cell =
      (simulateQ (interpreter ideal setup codec filling) client).run (state, cell) := by
  induction client using OracleComp.inductionOn generalizing state cell with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      simp only [interpreter, StateT.run, bind_map_left, relayQuery]

/-- A uniformly supplied persistent initial child has the adjacent concrete mixed-policy law under every observation of the complete counter-erased source state. The selected seed half is restored only on the proof side. -/
theorem independent_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (hidden : PqxdhSecretInputKdf.RootOutput) (selected : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (good : Good selected ideal (state, none)) :
    LazyOracleDiscard.LawEq
      (do let child ← $ᵗ FullOutput
          Prod.map id (view hidden) <$>
            (simulateQ (PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child setup codec)
              client).run state)
      ((simulateQ (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal selected true)) client).run (view hidden state)) := by
  have deferred := LazyOracleDiscard.LawEq.map (Prod.map id (view hidden))
    (PqxdhRecordLiftSeedRelay.deferred_source setup.source ideal filling setup codec ($ᵗ FullOutput) client state)
  have flattened := congrArg (fun work => Prod.map id (fun state : State n => view hidden state.1) <$> work)
    (flatten_run ideal setup codec filling client state none)
  rw [schedule_source ideal setup codec filling hidden selected client (state, none) good] at flattened
  simp only [Functor.map_map] at flattened deferred
  simp only [map_bind] at deferred
  exact deferred.symm.trans (LazyOracleDiscard.LawEq.of_eq flattened)

/-- The independent initial-child endpoint agrees with the actual adjacent source suffix at the established observer boundary, preserving the complete client result, shared ROM and writer logs. -/
theorem independent_observed {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (filling : PqxdhSecretInputKdf.RootOutput)
    (hidden : PqxdhSecretInputKdf.RootOutput) (selected : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalSeedCut.Mask n)
    (good : Good selected ideal (state, none)) (finish : PqxdhRecordLiftGlobalCut.Observer Result) :
    LazyOracleDiscard.LawEq
      (do let child ← $ᵗ FullOutput
          (simulateQ (PqxdhRecordLiftGlobalSeedCut.interpreter setup.source ideal filling child setup codec)
            client).run state >>= PqxdhRecordLiftGlobalSeedCut.observeMasked finish)
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter
        (PqxdhRecordLiftChainOracle.lookup setup.source · (Function.update ideal selected true))
        setup codec) client).run (PqxdhRecordLiftGlobalSeedCut.realize hidden state) >>=
          PqxdhRecordLiftGlobalCut.observe finish) := by
  have independent := (independent_source ideal setup codec filling hidden selected client state good).bind
    (fun result => LazyOracleDiscard.LawEq.refl (PqxdhRecordLiftChildPolicy.observeBare finish result))
  have concrete := congrArg (fun work => work >>= PqxdhRecordLiftChildPolicy.observeBare finish)
    (PqxdhRecordLiftCtxProtocol.bare_schedule setup codec (Function.update ideal selected true)
      client (PqxdhRecordLiftGlobalSeedCut.realize hidden state))
  simp only [bind_assoc, bind_map_left] at independent concrete
  exact independent.trans (LazyOracleDiscard.LawEq.of_eq concrete.symm)

/-! ### Supported prefixes and absent lookups -/

open PqxdhRecordLiftAvailability

/-- Law equality is a congruence for `bind` on the support of the first program. -/
theorem lawEq_bind_support {α β : Type} (mx : ProbComp α) {f g : α → ProbComp β}
    (hk : ∀ a ∈ support mx, LazyOracleDiscard.LawEq (f a) (g a)) :
    LazyOracleDiscard.LawEq (mx >>= f) (mx >>= g) := by
  intro γ _ k
  simp only [bind_assoc]
  exact OracleComp.evalDist_bind_congr_of_support mx _ _ (fun a member => hk a member γ k)

/-- Supported prefixes compose. -/
theorem reaches_trans {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)}
    {first middle last : OracleComp spec Result} {before between after : State}
    (head : Reaches impl first before middle between) (tail : Reaches impl middle between last after) :
    Reaches impl first before last after := by
  induction head with
  | here client before => exact tail
  | later query next before step rest after actual inner ih =>
      exact Reaches.later query next before step _ _ actual (ih tail)

/-- One more supported reply extends an actual prefix. -/
theorem reaches_step {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)}
    {client : OracleComp spec Result} {before after : State} {query : spec.Domain}
    {next : spec.Range query → OracleComp spec Result}
    (reached : Reaches impl client before (spec.query query >>= next) after)
    (step : spec.Range query × State) (actual : step ∈ support ((impl query).run after)) :
    Reaches impl client before (next step.1) step.2 :=
  reaches_trans reached (Reaches.later query next after step _ _ actual (Reaches.here _ _))

/-- A supported final result of a reached remainder is a supported final result of the whole run. -/
theorem reaches_final {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)}
    {client rest : OracleComp spec Result} {before after : State}
    (reached : Reaches impl client before rest after) (final : Result × State)
    (member : final ∈ support ((simulateQ impl rest).run after)) :
    final ∈ support ((simulateQ impl client).run before) := by
  induction reached with
  | here client before => exact member
  | later query next before step rest after actual inner ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨step, actual, ih member⟩

/-- A property of every reached query prestate is a query-safety certificate. -/
theorem safe_of_reaches {ι State Result : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT State ProbComp)) (predicate : spec.Domain → State → Prop)
    (client : OracleComp spec Result) (before : State)
    (every : ∀ query (next : spec.Range query → OracleComp spec Result) after,
      Reaches impl client before (spec.query query >>= next) after → predicate query after) :
    Safe impl predicate client before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      refine ⟨every query next before (Reaches.here _ _), fun result member => ?_⟩
      exact ih result.1 result.2 (fun query' next' after reached =>
        every query' next' after (Reaches.later query next before result _ after member reached))

/-- Query-safety certificates are monotone in their predicate. -/
theorem safe_mono {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)} {predicate weaker : spec.Domain → State → Prop}
    (client : OracleComp spec Result) (before : State) (safe : Safe impl predicate client before)
    (implies : ∀ query state, predicate query state → weaker query state) :
    Safe impl weaker client before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      exact ⟨implies query before safe.1, fun result member => ih result.1 result.2 (safe.2 result member)⟩

/-- Every concrete real call, ideal hit and ideal miss leaves its own coordinate populated. -/
theorem chain_lookup_present (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Slot n)) (ideal : Coordinate (Slot n) → Bool) (coordinate : Coordinate (Slot n))
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (result : FullOutput × PqxdhRecordLiftChainCompiler.Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state)) :
    result.2.1 coordinate ≠ none := by
  cases selected : ideal coordinate with
  | false =>
    rw [PqxdhRecordLiftChainOracle.lookup_real source seeds ideal coordinate state selected,
      support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, PqxdhRecordLiftRealTable.record, QueryCache.cacheQuery_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
  | true =>
    cases found : state.1 coordinate with
    | none =>
      rw [PqxdhRecordLiftChainOracle.lookup_miss source seeds ideal coordinate state selected found,
        support_map] at supported
      obtain ⟨value, _, rfl⟩ := supported
      simp only [QueryCache.cacheQuery_self, ne_eq, reduceCtorEq, not_false_eq_true]
    | some value =>
      rw [PqxdhRecordLiftChainOracle.lookup_hit source seeds ideal coordinate state selected value found,
        support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, found, ne_eq, reduceCtorEq, not_false_eq_true]

/-- The private lookup service populates its own coordinate under every concrete mixed policy. -/
theorem lookup_present {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Coordinate (Slot n)) (secret : Private n) (result : Unit × Private n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec
      (.lookup target)).run secret)) :
    result.2.chain target ≠ none := by
  simp only [PqxdhRecordLiftProtocol.interpreter, withRecord, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, member, rfl⟩ := supported
  change reply ∈ support (((fun _ => ()) <$>
    PqxdhRecordLiftLoggedAdapters.liftLookup
      (PqxdhRecordLiftChainOracle.lookup source (cachedSeeds secret) ideal) target :
      StateT (RecordState n) ProbComp Unit).run (recordState secret)) at member
  rw [StateT.run_map] at member
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, Functor.map_map, support_map] at member
  obtain ⟨actual, member, rfl⟩ := member
  exact chain_lookup_present source (cachedSeeds secret) ideal target (secret.chain, secret.primitive) actual member

/-- A populated coordinate stays populated through every private service. -/
theorem present_preserved {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (target : Coordinate (Slot n)) :
    QueryImpl.PreservesInv (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
      (fun secret => secret.chain target ≠ none) := by
  intro query secret present result supported
  by_cases same : query = .lookup target
  · subst query
    exact lookup_present source ideal setup codec target secret result supported
  · have avoids : PqxdhRecordLiftFirstLookup.Avoids target query := by
      cases query <;> simp_all only [PqxdhRecordLiftFirstLookup.Avoids, ne_eq, Service.lookup.injEq,
        not_false_eq_true]
    rw [PqxdhRecordLiftFirstLookup.query_other source ideal setup codec target query avoids secret result supported]
    exact present

/-- If the target coordinate is absent from every supported final table, no supported prefix reaches its lookup. -/
theorem lookup_absent {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (target : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (secret : Private n)
    (absent : ∀ final ∈ support ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
      setup codec) client).run secret), final.2.chain target = none) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
      (fun query _ => query ≠ .lookup target) client secret := by
  apply safe_of_reaches
  intro query next after reached same
  subst same
  obtain ⟨step, member⟩ := OracleComp.support_nonempty
    ((PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec (.lookup target)).run after)
  obtain ⟨final, finalMember⟩ := OracleComp.support_nonempty
    ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (next step.1)).run
      step.2)
  have present := simulateQ_run_preservesInv _ _ (present_preserved source ideal setup codec target)
    (next step.1) step.2 (lookup_present source ideal setup codec target after step member) final finalMember
  exact present (absent final (reaches_final (reaches_step reached step member) final finalMember))

/-- Mixed policies agreeing at every reached lookup give the same complete private execution. -/
theorem run_agrees {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (client : OracleComp (ServiceSpec n) Result) (secret : Private n)
    (safe : Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec)
      (fun query _ => PqxdhRecordLiftPrefixPolicy.AgreesAt left right query) client secret) :
    (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec) client).run secret =
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source right) setup codec) client).run
        secret := by
  induction client using OracleComp.inductionOn generalizing secret with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [← PqxdhRecordLiftPrefixPolicy.query_agrees setup codec left right query safe.1 secret]
      exact bind_congr_of_forall_mem_support _ (fun result member => ih result.1 result.2 (safe.2 result member))

/-- Policies differing only at one coordinate agree at every lookup other than that coordinate. -/
theorem agrees_update (ideal : Coordinate (Slot n) → Bool) (selected : Coordinate (Slot n)) (value : Bool)
    (query : Service n) (different : query ≠ .lookup selected) :
    PqxdhRecordLiftPrefixPolicy.AgreesAt ideal (Function.update ideal selected value) query := by
  cases query with
  | lookup coordinate =>
      have unequal : coordinate ≠ selected := fun same => different (congrArg Service.lookup same)
      exact (Function.update_of_ne unequal value ideal).symm
  | _ => trivial

/-! ### The seed prefix and the adjacent seed policy -/

/-- A completed first-allocation scan is a completed run of the whole client. -/
theorem complete_whole {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (target : Slot n)
    (client : OracleComp (ServiceSpec n) Result) (result : Result) (after : Private n)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.complete result, after) ∈ support
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
        (PqxdhRecordLiftGlobalSeedCut.scan target client)).run initialPrivate)) :
    (result, after) ∈ support ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
      setup codec) client).run initialPrivate) := by
  rw [← PqxdhRecordLiftGlobalSeedCut.scan_finish target client, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff]
  exact ⟨_, supported, by simp only [PqxdhRecordLiftGlobalSeedCut.finish, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff]⟩

/-- Every supported final state of the first-allocation scan of the frozen program has an empty table at every coordinate of the selected slot: a pending cut by source table provenance, a completed run because its never-allocated slot cannot hold a table entry. -/
theorem scan_absent {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (target : Slot n) (coordinate : Coordinate (Slot n)) (same : coordinate.slot = target)
    (final : PqxdhRecordLiftGlobalSeedCut.Cut n (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n) × Private n)
    (supported : final ∈ support ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
      setup codec) (PqxdhRecordLiftGlobalSeedCut.scan target
        (program env setup.source.crypto codec route serverKid bounds mode adversary))).run initialPrivate)) :
    final.2.chain coordinate = none := by
  rcases final with ⟨cut | next, after⟩
  · have missing := PqxdhRecordLiftGlobalSeedCut.scan_initial_missing setup.source ideal setup codec target
      (program env setup.source.crypto codec route serverKid bounds mode adversary) _ supported
    have whole := complete_whole setup.source ideal setup codec target _ cut after supported
    have good := PqxdhRecordLiftMixedWorld.protocol_run_good setup codec ideal route env serverKid bounds mode
      adversary (cut, after) whole
    cases found : after.chain coordinate with
    | none => rfl
    | some value =>
        obtain ⟨seed, present⟩ := good.2.2.1 coordinate value found
        change after.seeds.1 coordinate.slot = some seed at present
        rw [same, missing] at present
        contradiction
  · exact (PqxdhRecordLiftSeedScope.pending_schedule setup codec ideal route
      (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
      target next after supported).2.2 coordinate same

/-- The proof-attached first-allocation prefix of the frozen program is the same under the adjacent policy that idealizes one initial coordinate of the selected slot: that coordinate is never looked up before the slot's first allocation. -/
theorem seed_prefix {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (target : Slot n) (direction : Bool) :
    PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
        (program env setup.source.crypto codec route serverKid bounds mode adversary) =
      PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source
        (Function.update ideal ⟨target, direction, start direction⟩ true) setup codec target
        (program env setup.source.crypto codec route serverKid bounds mode adversary) := by
  apply (map_inj_right (f := Subtype.val) (fun h => Subtype.ext h)).mp
  rw [PqxdhRecordLiftGlobalSeedCut.prefix_forget, PqxdhRecordLiftGlobalSeedCut.prefix_forget]
  have absent := lookup_absent setup.source ideal setup codec ⟨target, direction, start direction⟩ _ initialPrivate
    (fun final member => scan_absent setup codec ideal route env serverKid bounds mode adversary target
      ⟨target, direction, start direction⟩ rfl final member)
  exact run_agrees setup codec ideal _ _ initialPrivate
    (safe_mono _ _ absent (fun query _ different => agrees_update ideal _ true query different))

/-- The independent seed endpoint of `PqxdhRecordLiftGlobalSeedCut.observed_bound` is the adjacent concrete mixed policy with the selected initial coordinate ideal, under the complete client result, shared ROM cache and writer logs. Early completion (the slot is never allocated) gives equal games. -/
theorem uniform_policy {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (filling : PqxdhSecretInputKdf.RootOutput) (target : Slot n) (direction : Bool)
    (real : ideal ⟨target, direction, start direction⟩ = false)
    (finish : PqxdhRecordLiftGlobalCut.Observer (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n)) :
    LazyOracleDiscard.LawEq
      (PqxdhRecordLiftGlobalSeedCut.seedUniform setup.source ideal filling setup codec target direction
        (program env setup.source.crypto codec route serverKid bounds mode adversary) finish)
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
        (Function.update ideal ⟨target, direction, start direction⟩ true)) setup codec)
        (program env setup.source.crypto codec route serverKid bounds mode adversary)).run initialPrivate >>=
          PqxdhRecordLiftGlobalCut.observe finish) := by
  rw [← PqxdhRecordLiftGlobalSeedCut.resume_prefix setup.source _ setup codec target,
    ← seed_prefix setup codec ideal route env serverKid bounds mode adversary target direction]
  simp only [PqxdhRecordLiftGlobalSeedCut.seedUniform, PqxdhRecordLiftGlobalSeedCut.retainedContext, bind_assoc,
    pure_bind]
  apply lawEq_bind_support
  intro reached supported
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [PqxdhRecordLiftGlobalSeedCut.seedObserver, stopped, PqxdhRecordLiftGlobalSeedCut.finish,
        simulateQ_pure, StateT.run_pure, pure_bind]
      exact (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
        (fun _ => LazyOracleDiscard.lawEq_drop _ _)).trans (LazyOracleDiscard.lawEq_drop _ _)
  | pending next =>
      have facts := PqxdhRecordLiftSeedScope.sampled_program setup codec ideal route env serverKid bounds mode
        adversary target reached supported next stopped
      simp only [PqxdhRecordLiftGlobalSeedCut.seedObserver, stopped, PqxdhRecordLiftGlobalSeedCut.finish,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine LazyOracleDiscard.LawEq.trans ?_ (PqxdhRecordLiftGlobalSeedCut.miss_continuation
        (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (Function.update ideal ⟨target, direction, start direction⟩ true)) setup codec target direction
        reached.val.2 reached.property _).symm
      apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
      intro other
      have good : Good ⟨target, direction, start direction⟩ ideal
          (PqxdhRecordLiftGlobalSeedCut.prepare reached.val.2 target direction other, none) :=
        ⟨rfl, real, facts.2.2 _ rfl⟩
      exact (LazyOracleDiscard.lawEq_drop ($ᵗ PqxdhSecretInputKdf.RootOutput) _).symm.trans
        (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) (fun hidden =>
          independent_observed ideal setup codec filling hidden _ (next ())
            (PqxdhRecordLiftGlobalSeedCut.prepare reached.val.2 target direction other) good finish))

end BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reads_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reads_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.needs_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.needs_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.interpreter_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.interpreter_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.different_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.different_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.relay_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.relay_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.view_putChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.view_putChild

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.view_child' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.view_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.child_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.child_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.needs_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.needs_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.relay_different' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.relay_different

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.different_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.different_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.query_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.query_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.step_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.flatten_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.flatten_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.independent_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.independent_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.independent_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.independent_observed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lawEq_bind_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lawEq_bind_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_step' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.reaches_final

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.safe_of_reaches' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.safe_of_reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.safe_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.safe_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.chain_lookup_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.chain_lookup_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.present_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.present_preserved

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.lookup_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.run_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.run_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.agrees_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.agrees_update

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.complete_whole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.complete_whole

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.scan_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.scan_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.seed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.seed_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.uniform_policy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy.uniform_policy
