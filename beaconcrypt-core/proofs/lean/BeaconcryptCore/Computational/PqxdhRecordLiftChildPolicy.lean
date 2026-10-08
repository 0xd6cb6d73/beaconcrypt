-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChildRelay
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol

/-! Identify the persistent evolving-child response with the adjacent concrete mixed policy. Only native/uniform analysis counters are projected; all source bytes and observable state remain. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
variable {n : Nat}

/-- Away from the selected parent, its only possible structural reader is its successor. The parent lower bound is the actual source availability condition; the total natural-number zero fallback is handled explicitly. -/
theorem reads_iff (coordinate parent : Coordinate (Slot n))
    (lower : start parent.direction ≤ parent.position) (different : coordinate ≠ parent) :
    PqxdhRecordLiftMaskedReads.Reads coordinate parent ↔ coordinate = advance parent 1 := by
  constructor
  · rintro ⟨_, prior⟩
    have positive : 0 < coordinate.position := by
      by_contra zero
      have poszero : coordinate.position = 0 := Nat.eq_zero_of_not_pos zero
      have same : previous coordinate = coordinate := by
        cases coordinate
        simp_all only [previous, Nat.zero_sub]
      exact different (same.symm.trans prior)
    have arithmetic : coordinate.position - 1 + 1 = coordinate.position := by omega
    rw [← prior]
    cases coordinate
    simp only [previous, advance, arithmetic]
  · intro same
    subst coordinate
    refine ⟨?_, previous_advance parent⟩
    simp only [advance]
    omega

/-- Forwarding an actual uniform computation never queries or changes the persistent child cell. -/
theorem coin_lazy {Result : Type} (draw : ProbComp FullOutput) (work : ProbComp Result)
    (cell : Option FullOutput) :
    (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl draw)
      (simulateQ PqxdhRecordLiftChildRelay.coinLift work)).run cell =
      (fun result => (result, cell)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftChildRelay.coinLift,
        PqxdhRecordLiftDeferredChild.lazyImpl, StateT.run, map_bind]
      change ((unifSpec.query query : ProbComp _) >>= fun reply =>
        (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl draw)
          (simulateQ PqxdhRecordLiftChildRelay.coinLift (next reply))).run cell) = _
      exact bind_congr ih

/-- The state view erases only native/uniform analysis counts; the selected parent is restored solely for this proof-side comparison. -/
noncomputable def view (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalMask.State n) : PqxdhRecordLiftCtxProtocol.Bare n :=
  PqxdhRecordLiftCtxProtocol.erasePrivate (PqxdhRecordLiftGlobalMask.realize hidden state)

def NonLookup : Service n → Prop
  | .lookup _ => False
  | _ => True

/-- All non-lookup source services retain their literal native behavior under the adjacent lookup policy, including optional failure replies and complete public-effect, seed, table and log state. -/
theorem other_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (child : FullOutput) (hidden : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n)
    (other : NonLookup query) (parentIdeal : ideal state.masked.coordinate = true) :
    Prod.map id (view hidden) <$>
      (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec query).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance state.masked.coordinate 1) true) query).run (view hidden state) := by
  have unused : ¬ PqxdhRecordLiftChildRelay.Needs ideal state query := by
    cases query <;> simp_all only [NonLookup, PqxdhRecordLiftChildRelay.Needs, not_false_eq_true]
  rw [PqxdhRecordLiftChildRelay.unused_source setup.source ideal setup codec query state child
    (PqxdhJointKdf.productionStream setup.source.crypto
      (PqxdhJointKdfGame.FixedHkdfDomain.ratchet.address hidden.toList)) unused]
  have sourceLaw := congrArg (fun work => Prod.map id PqxdhRecordLiftCtxProtocol.erasePrivate <$> work)
    (PqxdhRecordLiftGlobalMask.interpreter_realization setup.source ideal hidden setup codec query state parentIdeal)
  rw [PqxdhRecordLiftCtxProtocol.bare_query] at sourceLaw
  simp only [Functor.map_map] at sourceLaw
  change _ = _ at sourceLaw
  have updated : (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec ideal query).run (view hidden state) =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance state.masked.coordinate 1) true) query).run (view hidden state) := by
    cases query <;> first | contradiction | rfl
  exact sourceLaw.trans updated

/-- Every read uses one child cell whose contents track the actual persistent successor entry. -/
def CellMatches (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput) : Prop :=
  state.masked.before (advance state.masked.coordinate 1) = cell

def Ready (ideal : Coordinate (Slot n) → Bool) (state : PqxdhRecordLiftGlobalMask.State n) : Prop :=
  start state.masked.coordinate.direction ≤ state.masked.coordinate.position ∧
    ideal state.masked.coordinate = true ∧ ideal (advance state.masked.coordinate 1) = false

def putChild (state : PqxdhRecordLiftGlobalMask.State n) (child : FullOutput) :
    PqxdhRecordLiftGlobalMask.State n :=
  { state with
    masked := (PqxdhRecordLiftMaskedOracle.record state.masked
      (advance state.masked.coordinate 1) child)
    primitive := PqxdhRecordLiftChainOracle.charge state.primitive }

/-- The actual real child lookup overwrites its own cached response with the same supplied full76, charges its native KDF call, and keeps every other global field. -/
theorem lookup_child {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (child : FullOutput) (state : PqxdhRecordLiftGlobalMask.State n) (ready : Ready ideal state) :
    (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec
      (.lookup (advance state.masked.coordinate 1))).run state = pure ((), putChild state child) := by
  have different : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  have reads := (reads_iff (advance state.masked.coordinate 1) state.masked.coordinate ready.1 different).mpr rfl
  simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.withRecords,
    PqxdhRecordLiftGlobalMask.localInterpreter, PqxdhRecordLiftMaskedOracle.interpreter,
    PqxdhRecordLiftGlobalMask.records, StateT.run, PqxdhRecordLiftMaskedOracle.lookup,
    different, ite_false, ready.2.2, Bool.false_eq_true, reads, ite_true, pure_bind]
  rfl

noncomputable def relayQuery {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput) :=
  (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
    ((PqxdhRecordLiftChildRelay.interpreter setup.source ideal setup codec query).run state)).run cell

/-- The first real child read samples once; later reads reuse the exact full76 stored in the persistent cell. The source still executes and charges its own lookup each time. -/
theorem relay_child {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput) (ready : Ready ideal state) :
    relayQuery ideal setup codec (.lookup (advance state.masked.coordinate 1)) state cell =
      match cell with
      | some child => pure (((), putChild state child), some child)
      | none => (fun child => (((), putChild state child), some child)) <$> ($ᵗ FullOutput) := by
  have different : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  have reads := (reads_iff (advance state.masked.coordinate 1) state.masked.coordinate ready.1 different).mpr rfl
  have needs : PqxdhRecordLiftChildRelay.Needs ideal state (.lookup (advance state.masked.coordinate 1)) :=
    ⟨different, ready.2.2, reads⟩
  simp only [relayQuery, PqxdhRecordLiftChildRelay.interpreter, StateT.run, needs, ite_true,
    simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftDeferredChild.lazyImpl]
  change ((PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput) (.inl ()) >>= fun child =>
    simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
      (simulateQ PqxdhRecordLiftChildRelay.coinLift
        ((PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec
          (.lookup (advance state.masked.coordinate 1))).run state)))).run cell = _
  simp_rw [lookup_child ideal setup codec _ state ready]
  simp only [simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do let value ← (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput) (.inl ())).run cell
             pure (((), putChild state value.1), value.2)) = _
  cases cell <;> simp only [PqxdhRecordLiftDeferredChild.lazyImpl, StateT.run, bind_pure_comp, Functor.map_map, map_pure]
  rfl

/-- Restoring the parent commutes with the exact child cache write and erases only the native KDF count increment. -/
theorem view_putChild (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalMask.State n) (child : FullOutput) :
    view hidden (putChild state child) =
      { view hidden state with chain := (view hidden state).chain.cacheQuery (advance state.masked.coordinate 1) child } := by
  have different : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  simp only [view, PqxdhRecordLiftCtxProtocol.erasePrivate, PqxdhRecordLiftGlobalMask.realize,
    putChild, PqxdhRecordLiftMaskedOracle.record_realize _ _ _ _ different,
    PqxdhRecordLiftChainOracle.charge]

/-- The cache relation keeps the literal successor entry, not an independent projection sample. -/
theorem view_child (hidden : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput) (agrees : CellMatches state cell) :
    (view hidden state).chain (advance state.masked.coordinate 1) = cell := by
  have different : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  simpa only [view, PqxdhRecordLiftCtxProtocol.erasePrivate, PqxdhRecordLiftGlobalMask.realize,
    PqxdhRecordLiftMaskedOracle.table, PqxdhRecordLiftProjectionCut.realize,
    QueryCache.cacheQuery_of_ne _ _ different, CellMatches] using agrees

/-- At the selected child, the relay and the adjacent concrete ideal lookup return the same complete counter-erased source state for both misses and repeated hits. -/
theorem child_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : PqxdhSecretInputKdf.RootOutput) (state : PqxdhRecordLiftGlobalMask.State n)
    (cell : Option FullOutput) (ready : Ready ideal state) (agrees : CellMatches state cell) :
    (fun result => (result.1.1, view hidden result.1.2)) <$>
      relayQuery ideal setup codec (.lookup (advance state.masked.coordinate 1)) state cell =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance state.masked.coordinate 1) true)
        (.lookup (advance state.masked.coordinate 1))).run (view hidden state) := by
  rw [relay_child ideal setup codec state cell ready]
  simp only [PqxdhRecordLiftCtxProtocol.bareInterpreter, StateT.run,
    PqxdhRecordLiftCtxOracle.bareLookup, Function.update_self, ite_true,
    view_child hidden state cell agrees]
  cases cell with
  | none =>
      simp only [Functor.map_map, bind_pure_comp, view_putChild]
  | some child =>
      have cached := view_child hidden state (some child) agrees
      have unchanged : (view hidden state).chain.cacheQuery (advance state.masked.coordinate 1) child =
          (view hidden state).chain := by
        funext query
        by_cases same : query = advance state.masked.coordinate 1
        · subst query
          simp only [QueryCache.cacheQuery_self, cached]
        · exact QueryCache.cacheQuery_of_ne _ _ same
      simp only [map_pure, pure_bind, view_putChild, unchanged]


/-- The exact unavailable-parent condition singles out the structural successor on the source domain. -/
theorem needs_iff (ideal : Coordinate (Slot n) → Bool)
    (state : PqxdhRecordLiftGlobalMask.State n) (query : Service n) (ready : Ready ideal state) :
    PqxdhRecordLiftChildRelay.Needs ideal state query ↔ query = .lookup (advance state.masked.coordinate 1) := by
  cases query with
  | lookup coordinate =>
      change (coordinate ≠ state.masked.coordinate ∧ ideal coordinate = false ∧
        PqxdhRecordLiftMaskedReads.Reads coordinate state.masked.coordinate) ↔ _
      constructor
      · rintro ⟨different, _, reads⟩
        rw [(reads_iff coordinate state.masked.coordinate ready.1 different).mp reads]
      · intro same
        have equal := Service.lookup.inj same
        subst coordinate
        have different : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
          intro equal
          have positions := congrArg Coordinate.position equal
          simp only [advance] at positions
          omega
        exact ⟨different, ready.2.2,
          (reads_iff _ state.masked.coordinate ready.1 different).mpr rfl⟩
  | _ => simp only [PqxdhRecordLiftChildRelay.Needs, reduceCtorEq]

/-- Every other service has the unchanged concrete source law under the neighboring policy; no byte alias or successful-reply condition is imposed. -/
theorem different_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (child : FullOutput) (hidden : PqxdhSecretInputKdf.RootOutput)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n)
    (different : query ≠ .lookup (advance state.masked.coordinate 1)) (ready : Ready ideal state) :
    Prod.map id (view hidden) <$>
      (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec query).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance state.masked.coordinate 1) true) query).run (view hidden state) := by
  have unused := (needs_iff ideal state query ready).not.mpr different
  rw [PqxdhRecordLiftChildRelay.unused_source setup.source ideal setup codec query state child
    (PqxdhJointKdf.productionStream setup.source.crypto
      (PqxdhJointKdfGame.FixedHkdfDomain.ratchet.address hidden.toList)) unused]
  have sourceLaw := congrArg (fun work => Prod.map id PqxdhRecordLiftCtxProtocol.erasePrivate <$> work)
    (PqxdhRecordLiftGlobalMask.interpreter_realization setup.source ideal hidden setup codec query state ready.2.1)
  rw [PqxdhRecordLiftCtxProtocol.bare_query] at sourceLaw
  simp only [Functor.map_map] at sourceLaw
  apply sourceLaw.trans
  cases query with
  | lookup coordinate =>
      have unequal : coordinate ≠ advance state.masked.coordinate 1 := fun same => different (congrArg Service.lookup same)
      simp only [PqxdhRecordLiftCtxProtocol.bareInterpreter, PqxdhRecordLiftCtxOracle.bareLookup,
        StateT.run, Function.update_of_ne unequal]
      rfl
  | _ => rfl

/-- A service outside the selected child forwards its whole original computation and leaves the persistent cell unchanged. -/
theorem relay_different {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput)
    (different : query ≠ .lookup (advance state.masked.coordinate 1)) (ready : Ready ideal state) :
    relayQuery ideal setup codec query state cell =
      (fun result => (result, cell)) <$>
        (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal
          PqxdhRecordLiftChildRelay.unusedChild setup codec query).run state := by
  have unused := (needs_iff ideal state query ready).not.mpr different
  simp only [relayQuery, PqxdhRecordLiftChildRelay.interpreter, StateT.run, unused, ite_false, pure_bind]
  change (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
    (simulateQ PqxdhRecordLiftChildRelay.coinLift
      ((PqxdhRecordLiftGlobalMask.interpreter setup.source ideal PqxdhRecordLiftChildRelay.unusedChild
        setup codec query).run state))).run cell = _
  exact coin_lazy _ _ _

/-- Every private service of the lazy-child relay agrees with the adjacent concrete policy on the complete source byte/cache/log/effect state. -/
theorem query_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : PqxdhSecretInputKdf.RootOutput) (query : Service n)
    (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput)
    (ready : Ready ideal state) (agrees : CellMatches state cell) :
    (fun result => (result.1.1, view hidden result.1.2)) <$> relayQuery ideal setup codec query state cell =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance state.masked.coordinate 1) true) query).run (view hidden state) := by
  by_cases selected : query = .lookup (advance state.masked.coordinate 1)
  · subst query
    exact child_source ideal setup codec hidden state cell ready agrees
  · rw [relay_different ideal setup codec query state cell selected ready, Functor.map_map]
    exact different_source ideal setup codec _ hidden query state selected ready

/-- All other complete source services preserve the exact persistent child entry, including failed native operations and unrelated random lookups. -/
theorem different_entry {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (child : FullOutput) (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n)
    (different : query ≠ .lookup (advance state.masked.coordinate 1)) (ready : Ready ideal state)
    (result : (ServiceSpec n).Range query × PqxdhRecordLiftGlobalMask.State n)
    (supported : result ∈ support ((PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child
      setup codec query).run state)) :
    result.2.masked.before (advance result.2.masked.coordinate 1) =
      state.masked.before (advance state.masked.coordinate 1) := by
  have coordinate := PqxdhRecordLiftGlobalMask.interpreter_coordinate setup.source ideal child setup codec query state result supported
  have unused := (needs_iff ideal state query ready).not.mpr different
  rw [PqxdhRecordLiftChildRelay.unused_source setup.source ideal setup codec query state child
    (PqxdhJointKdf.productionStream setup.source.crypto
      (PqxdhJointKdfGame.FixedHkdfDomain.ratchet.address PqxdhRecordLiftMaskedOracle.filling.toList)) unused] at supported
  have actual : (result.1, PqxdhRecordLiftGlobalMask.realize PqxdhRecordLiftMaskedOracle.filling result.2) ∈
      support ((PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
        setup codec query).run (PqxdhRecordLiftGlobalMask.realize PqxdhRecordLiftMaskedOracle.filling state)) := by
    rw [← PqxdhRecordLiftGlobalMask.interpreter_realization setup.source ideal
      PqxdhRecordLiftMaskedOracle.filling setup codec query state ready.2.1, support_map]
    exact ⟨result, supported, rfl⟩
  have avoids : PqxdhRecordLiftFirstLookup.Avoids (advance state.masked.coordinate 1) query := by
    cases query <;> simp_all only [PqxdhRecordLiftFirstLookup.Avoids, ne_eq, Service.lookup.injEq, not_false_eq_true]
  have same := PqxdhRecordLiftFirstLookup.query_other setup.source ideal setup codec
    (advance state.masked.coordinate 1) query avoids _ _ actual
  have differentParent : advance state.masked.coordinate 1 ≠ state.masked.coordinate := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  have differentAfter : advance state.masked.coordinate 1 ≠ result.2.masked.coordinate := by
    rw [coordinate]
    exact differentParent
  rw [coordinate]
  simpa only [PqxdhRecordLiftGlobalMask.realize, PqxdhRecordLiftMaskedOracle.table,
    PqxdhRecordLiftProjectionCut.realize, coordinate,
    QueryCache.cacheQuery_of_ne _ _ differentParent, QueryCache.cacheQuery_of_ne _ _ differentAfter] using same

/-- The single-step relay keeps its exact selected coordinate and the child-cell/cache invariant under every actual reply. -/
theorem query_invariant {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n) (cell : Option FullOutput)
    (ready : Ready ideal state) (agrees : CellMatches state cell)
    (result : ((ServiceSpec n).Range query × PqxdhRecordLiftGlobalMask.State n) × Option FullOutput)
    (supported : result ∈ support (relayQuery ideal setup codec query state cell)) :
    result.1.2.masked.coordinate = state.masked.coordinate ∧
      Ready ideal result.1.2 ∧ CellMatches result.1.2 result.2 := by
  by_cases selected : query = .lookup (advance state.masked.coordinate 1)
  · subst query
    rw [relay_child ideal setup codec state cell ready] at supported
    cases cell with
    | none =>
        rw [support_map] at supported
        obtain ⟨child, _, rfl⟩ := supported
        refine ⟨rfl, ready, ?_⟩
        simp only [CellMatches, putChild, PqxdhRecordLiftMaskedOracle.record, QueryCache.cacheQuery_self]
    | some child =>
        rw [mem_support_pure_iff] at supported
        subst result
        refine ⟨rfl, ready, ?_⟩
        simp only [CellMatches, putChild, PqxdhRecordLiftMaskedOracle.record, QueryCache.cacheQuery_self]
  · rw [relay_different ideal setup codec query state cell selected ready, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have coordinate := PqxdhRecordLiftGlobalMask.interpreter_coordinate setup.source ideal
      PqxdhRecordLiftChildRelay.unusedChild setup codec query state inner member
    refine ⟨coordinate, ?_, ?_⟩
    · simpa only [Ready, coordinate] using ready
    · exact (different_entry ideal setup codec _ query state selected ready inner member).trans agrees

abbrev State (n : Nat) := PqxdhRecordLiftGlobalMask.State n × Option FullOutput

def Good (parent : Coordinate (Slot n)) (ideal : Coordinate (Slot n) → Bool) (state : State n) : Prop :=
  state.1.masked.coordinate = parent ∧ Ready ideal state.1 ∧ CellMatches state.1 state.2

/-- Flatten only the extra child-cell transformer, retaining every original field. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (State n) ProbComp) := fun query state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> relayQuery ideal setup codec query state.1 state.2

/-- The actual flattened relay preserves the fixed parent and exact child cache relation under every supported reply. -/
theorem step_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (parent : Coordinate (Slot n)) (query : Service n) (state : State n) (good : Good parent ideal state)
    (result : (ServiceSpec n).Range query × State n)
    (supported : result ∈ support ((interpreter ideal setup codec query).run state)) :
    Good parent ideal result.2 := by
  simp only [interpreter, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have actual := query_invariant ideal setup codec query state.1 state.2 good.2.1 good.2.2 inner member
  exact ⟨actual.1.trans good.1, actual.2⟩

/-- The entire adaptive relay equals the adjacent concrete source interpreter after only native/uniform count erasure and removal of the additional cell. -/
theorem schedule_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : PqxdhSecretInputKdf.RootOutput) (parent : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : State n) (good : Good parent ideal state) :
    Prod.map id (fun state : State n => view hidden state.1) <$>
      (simulateQ (interpreter ideal setup codec) client).run state =
      (simulateQ (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance parent 1) true)) client).run (view hidden state.1) := by
  apply map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (Good parent ideal)
    (fun state : State n => view hidden state.1)
    (step_good ideal setup codec parent) ?_ client state good
  intro query before ready
  have actual := query_source ideal setup codec hidden query before.1 before.2 ready.2.1 ready.2.2
  simpa only [interpreter, StateT.run, Functor.map_map, ready.1, Prod.map_def, id_eq] using actual

/-- Flattening the extra child-cell transformer preserves the literal complete execution, before any source-state projection. -/
theorem flatten_run {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalMask.State n)
    (cell : Option FullOutput) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhRecordLiftDeferredChild.lazyImpl ($ᵗ FullOutput))
        ((simulateQ (PqxdhRecordLiftChildRelay.interpreter setup.source ideal setup codec) client).run state)).run cell =
      (simulateQ (interpreter ideal setup codec) client).run (state, cell) := by
  induction client using OracleComp.inductionOn generalizing state cell with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      simp only [interpreter, StateT.run, bind_map_left, relayQuery]

/-- A uniformly supplied persistent child has the adjacent concrete mixed-policy law under every observation of the complete counter-erased source state. The hidden parent is restored only on the proof side. -/
theorem independent_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : PqxdhSecretInputKdf.RootOutput) (parent : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalMask.State n)
    (good : Good parent ideal (state, none)) :
    LazyOracleDiscard.LawEq
      (do let child ← $ᵗ FullOutput
          Prod.map id (view hidden) <$>
            (simulateQ (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec) client).run state)
      ((simulateQ (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec
        (Function.update ideal (advance parent 1) true)) client).run (view hidden state)) := by
  have deferred := LazyOracleDiscard.LawEq.map (Prod.map id (view hidden))
    (PqxdhRecordLiftChildRelay.deferred_source setup.source ideal setup codec ($ᵗ FullOutput) client state)
  have flattened := congrArg (fun work => Prod.map id (fun state : State n => view hidden state.1) <$> work)
    (flatten_run ideal setup codec client state none)
  rw [schedule_source ideal setup codec hidden parent client (state, none) good] at flattened
  simp only [Functor.map_map] at flattened deferred
  simp only [map_bind] at deferred
  exact deferred.symm.trans (LazyOracleDiscard.LawEq.of_eq flattened)

def observeBare {Result : Type} (finish : PqxdhRecordLiftGlobalCut.Observer Result)
    (result : Result × PqxdhRecordLiftCtxProtocol.Bare n) : ProbComp Bool :=
  finish result.1 result.2.cache result.2.produced result.2.pending

/-- The independent child endpoint agrees with the actual adjacent source suffix at the established observer boundary, preserving the complete client result, shared ROM and writer logs. -/
theorem independent_observed {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (ideal : Coordinate (Slot n) → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : PqxdhSecretInputKdf.RootOutput) (parent : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) Result) (state : PqxdhRecordLiftGlobalMask.State n)
    (good : Good parent ideal (state, none)) (finish : PqxdhRecordLiftGlobalCut.Observer Result) :
    LazyOracleDiscard.LawEq
      (do let child ← $ᵗ FullOutput
          (simulateQ (PqxdhRecordLiftGlobalMask.interpreter setup.source ideal child setup codec) client).run state >>=
            PqxdhRecordLiftGlobalCut.observeMasked finish)
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter
        (PqxdhRecordLiftChainOracle.lookup setup.source · (Function.update ideal (advance parent 1) true))
        setup codec) client).run (PqxdhRecordLiftGlobalMask.realize hidden state) >>=
          PqxdhRecordLiftGlobalCut.observe finish) := by
  have independent := (independent_source ideal setup codec hidden parent client state good).bind
    (fun result => LazyOracleDiscard.LawEq.refl (observeBare finish result))
  have concrete := congrArg (fun work => work >>= observeBare finish)
    (PqxdhRecordLiftCtxProtocol.bare_schedule setup codec (Function.update ideal (advance parent 1) true)
      client (PqxdhRecordLiftGlobalMask.realize hidden state))
  simp only [bind_assoc, bind_map_left] at independent concrete
  exact independent.trans (LazyOracleDiscard.LawEq.of_eq concrete.symm)

end BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.reads_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.reads_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.coin_lazy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.coin_lazy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.other_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.other_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.lookup_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.lookup_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.relay_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.relay_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.view_putChild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.view_putChild

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.view_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.view_child

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.child_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.child_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.needs_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.needs_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.different_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.different_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.relay_different' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.relay_different

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.different_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.different_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.query_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.query_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.step_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.flatten_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.flatten_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.independent_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.independent_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.independent_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChildPolicy.independent_observed
