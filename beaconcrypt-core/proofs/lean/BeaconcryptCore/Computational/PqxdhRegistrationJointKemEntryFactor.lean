import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorResume
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand
import BeaconcryptCore.Computational.PqxdhRootFirstEntry

/-!
# Entry 0's 108 bytes in the uniform-root world (item 2, stage S3b)

This module completes stage S3b of the item 2 plan: the uniform-root world H2 of stage S2 (`PqxdhCorrelatedExpandHybrid.uniformGame rootClient`) is the key-schedule game `PqxdhServerAuthKeySchedule.rootHybrid setup.source entryD` on an explicitly constructed distinguisher `entryD` of the 108 bytes of entry 0.

- `entryClient` is the root client of stage S2 with the factored services (`factoredServices`, plan section 18) in place of the native services: its value requests return 108-byte outputs, and on a hidden entry with value `value` the Server's response tail and the Beacon continuation are the factored forms at `PqxdhServerAuthCtxMaterial.factor value`, with the placeholder root in the hidden session's pending token. `rootClient_entry` (from `postSkel_factor`) shows that the root client is `entryClient` with every value request answered by the 108-byte output `PqxdhServerAuthKeySchedule.fromRoot setup.source` of a root request at the same coordinates.
- `firstTable value sampler` answers the first fresh coordinate with `value`, every later fresh coordinate with a draw of `sampler`, and every repeated coordinate from its table; `PqxdhRootFirstEntry.eagerImpl` is its instance at uniform roots (`eagerImpl_eq`). `firstTable_relabel` moves a relabelling of the answers into the table.
- `entryD setup … value` runs `entryClient` with entry 0, the first hidden coordinate in execution order, answered by `value`, and every later hidden coordinate by the 108-byte output of a fresh uniform root. Its arguments are the 108 bytes only; the uniform roots of the other entries are drawn inside it.
- `uniformGame_entry` (the plan's S3b statement `uniformGame rootClient = rootHybrid source entryD`, as an equality of output distributions): by stage S3a (`PqxdhRootFirstEntry.uniformGame_first`) entry 0's root is drawn first, and the game with that root is `entryD` at the root's 108-byte output. `rootClient_entryD` is the same statement for the advantage against any game.

Entry 0 is the Server's selected session whenever the Server's resumption derives its root, because that is the first hidden read of the post-challenge phase (plan section 11, risk 7); otherwise it is the first hidden Beacon finish. Hidden reads are identified by public handles only. These are program and distribution equalities; they charge nothing.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhRegistrationJointKemPostSkeleton (SkelSpec ValueOracle postSkel nativeServices sharedStart)

/-! ### Relabelled value requests of a root client -/

section Relabel

variable {D V W : Type}

/-- Answer a value request with values in `W` by the value request with values in `V` at the same point, mapped by `f`; coins are forwarded. -/
def relabelR (f : V → W) : QueryImpl (unifSpec + (D →ₒ W)) (OracleComp (unifSpec + (D →ₒ V))) :=
  QueryImpl.add
    (fun query => ((unifSpec + (D →ₒ V)).query (.inl query) : OracleComp (unifSpec + (D →ₒ V)) _) :
      QueryImpl unifSpec (OracleComp (unifSpec + (D →ₒ V))))
    (fun point => f <$> ((unifSpec + (D →ₒ V)).query (.inr point) : OracleComp (unifSpec + (D →ₒ V)) V) :
      QueryImpl (D →ₒ W) (OracleComp (unifSpec + (D →ₒ V))))

/-- Relabelling leaves lifted coins unchanged. -/
theorem relabelR_liftComp {α : Type} (f : V → W) (work : ProbComp α) :
    simulateQ (relabelR (D := D) f) (OracleComp.liftComp work (unifSpec + (D →ₒ W))) =
      OracleComp.liftComp work (unifSpec + (D →ₒ V)) := by
  rw [relabelR, QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftComp_left, OracleComp.liftComp_def]
  rfl

end Relabel

/-! ### The root client with value-valued hidden reads -/

section Local

variable {V : Type}

/-- The interface of a root client whose value requests at 128-byte coordinates return values in `V`. -/
abbrev EntrySpec (V : Type) := unifSpec + (PqxdhCorrelatedExtractFamily.Message →ₒ V)

/-- `PqxdhRegistrationJointKemRootExpand.publicLocal` for hidden values in `V`: coins and hidden reads are the client's own requests; a direct read is answered from a lazily sampled public table in the client's state. -/
noncomputable def publicLocalV (V : Type) :
    QueryImpl (SkelSpec V) (StateT HmacOracle.QueryCache (OracleComp (EntrySpec V))) :=
  (fun query => StateT.mk fun cache =>
      (fun reply => (reply, cache)) <$> ((EntrySpec V).query (.inl query) : OracleComp (EntrySpec V) _) :
      QueryImpl unifSpec (StateT HmacOracle.QueryCache (OracleComp (EntrySpec V)))) +
    ((fun message => StateT.mk fun cache =>
        (fun reply => (reply, cache)) <$> ((EntrySpec V).query (.inr message) : OracleComp (EntrySpec V) V) :
        QueryImpl (ValueOracle V) (StateT HmacOracle.QueryCache (OracleComp (EntrySpec V)))) +
      (fun point => StateT.mk fun cache => OracleComp.liftComp ((HmacOracle.randomOracle point).run cache) (EntrySpec V) :
        QueryImpl PqxdhExtractRomHiddenSuffix.TableOracle (StateT HmacOracle.QueryCache (OracleComp (EntrySpec V)))))

/-- `PqxdhRegistrationJointKemRootExpand.internalize` for hidden values in `V`. -/
noncomputable def internalizeV {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (post : C → OracleComp (SkelSpec V) Bool) : OracleComp (EntrySpec V) Bool := do
  let p ← OracleComp.liftComp start (EntrySpec V)
  (simulateQ (publicLocalV V) (post p.2)).run' p.1

/-- The root client's local interpretation followed by nothing else is the relabelled interpretation of the value-valued client. -/
theorem publicLocal_relabel {α : Type} (f : RootOutput → Output) (work : OracleComp (SkelSpec Output) α)
    (cache : HmacOracle.QueryCache) :
    (simulateQ PqxdhRegistrationJointKemRootExpand.publicLocal (simulateQ (relabelS f) work)).run cache =
      simulateQ (relabelR f) ((simulateQ (publicLocalV Output) work).run cache) := by
  rw [← QueryImpl.simulateQ_compose, simulateQ_mapRun]
  congr 2
  funext query
  apply StateT.ext
  intro current
  rcases query with coin | (point | point)
  · change (simulateQ PqxdhRegistrationJointKemRootExpand.publicLocal
        (((SkelSpec RootOutput).query (.inl coin) : OracleComp (SkelSpec RootOutput) _))).run current =
      simulateQ (relabelR f) ((fun reply => (reply, current)) <$>
        ((EntrySpec Output).query (.inl coin) : OracleComp (EntrySpec Output) _))
    rw [simulateQ_spec_query, simulateQ_map, simulateQ_spec_query]
    rfl
  · change (simulateQ PqxdhRegistrationJointKemRootExpand.publicLocal
        (f <$> ((SkelSpec RootOutput).query (.inr (.inl point)) : OracleComp (SkelSpec RootOutput) _))).run current =
      simulateQ (relabelR f) ((fun reply => (reply, current)) <$>
        ((EntrySpec Output).query (.inr point) : OracleComp (EntrySpec Output) _))
    rw [simulateQ_map, simulateQ_spec_query, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    change Prod.map f id <$> ((fun reply => (reply, current)) <$>
        ((EntrySpec RootOutput).query (.inr point) : OracleComp (EntrySpec RootOutput) _)) =
      (fun reply => (reply, current)) <$> (f <$> ((EntrySpec RootOutput).query (.inr point) :
        OracleComp (EntrySpec RootOutput) _))
    simp only [Functor.map_map, Prod.map_apply, id_eq]
  · change (simulateQ PqxdhRegistrationJointKemRootExpand.publicLocal
        (((SkelSpec RootOutput).query (.inr (.inr point)) : OracleComp (SkelSpec RootOutput) _))).run current =
      simulateQ (relabelR f) (OracleComp.liftComp ((HmacOracle.randomOracle point).run current) (EntrySpec Output))
    rw [simulateQ_spec_query, relabelR_liftComp]
    rfl

/-- A root client of a relabelled skeleton client is the relabelled root client of the value-valued skeleton client. -/
theorem internalize_relabel {C : Type} (f : RootOutput → Output) (start : ProbComp (HmacOracle.QueryCache × C))
    (post : C → OracleComp (SkelSpec Output) Bool) :
    PqxdhRegistrationJointKemRootExpand.internalize start (fun context => simulateQ (relabelS f) (post context)) =
      simulateQ (relabelR f) (internalizeV start post) := by
  unfold PqxdhRegistrationJointKemRootExpand.internalize internalizeV
  rw [simulateQ_bind, relabelR_liftComp]
  refine bind_congr fun p => ?_
  rw [StateT.run'_eq, StateT.run'_eq, simulateQ_map, publicLocal_relabel]

end Local

/-! ### The first-value table -/

section Table

variable {D R R' : Type} [DecidableEq D]

/-- The first-value table: the first fresh point receives `value`, every later fresh point a draw of `sampler`, and every repeated point its stored answer. -/
noncomputable def firstTable (value : R) (sampler : ProbComp R) :
    QueryImpl (unifSpec + (D →ₒ R)) (StateT (PqxdhRootFirstEntry.State D R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (PqxdhRootFirstEntry.State D R) ProbComp) +
    (fun point => StateT.mk fun state => match state.1 point with
      | some answer => Pure.pure (answer, state)
      | none => match state.2 with
        | none => Pure.pure (value, (state.1.cacheQuery point value, some point))
        | some first => do
            let answer ← sampler
            Pure.pure (answer, (state.1.cacheQuery point answer, some first)) :
      QueryImpl (D →ₒ R) (StateT (PqxdhRootFirstEntry.State D R) ProbComp))

/-- The eager table of stage S3a is the first-value table at uniform values. -/
theorem eagerImpl_eq [SampleableType R] (value : R) :
    PqxdhRootFirstEntry.eagerImpl (D := D) value = firstTable value ($ᵗ R) := rfl

/-- A table with its answers mapped by `f`. -/
def mapCache (f : R → R') (cache : (D →ₒ R).QueryCache) : (D →ₒ R').QueryCache :=
  QueryCache.ofFn fun point => (cache point).map f

omit [DecidableEq D] in
theorem mapCache_empty (f : R → R') : mapCache (D := D) f ∅ = ∅ := rfl

theorem mapCache_cacheQuery (f : R → R') (cache : (D →ₒ R).QueryCache) (point : D) (answer : R) :
    mapCache f (cache.cacheQuery point answer) = (mapCache f cache).cacheQuery point (f answer) := by
  apply QueryCache.ext
  intro other
  by_cases same : other = point
  · subst same
    simp only [mapCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_self, Option.map_some]
  · simp only [mapCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne, ne_eq, same, not_false_eq_true]

/-- Relabelling the answers of the first-value table: the table answering `f` of its values is the table of the mapped values and the mapped sampler. -/
theorem firstTable_relabel {α : Type} (f : R → R') (value : R) (sampler : ProbComp R)
    (client : OracleComp (unifSpec + (D →ₒ R')) α) (state : PqxdhRootFirstEntry.State D R) :
    Prod.map id (fun table : PqxdhRootFirstEntry.State D R => (mapCache f table.1, table.2)) <$>
        (simulateQ (firstTable value sampler) (simulateQ (relabelR f) client)).run state =
      (simulateQ (firstTable (f value) (f <$> sampler)) client).run (mapCache f state.1, state.2) := by
  rw [← QueryImpl.simulateQ_compose]
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun query current => ?_) client state
  rcases query with coin | point
  · change Prod.map id _ <$> (simulateQ (firstTable value sampler)
        (((unifSpec + (D →ₒ R)).query (.inl coin) : OracleComp (unifSpec + (D →ₒ R)) _))).run current = _
    rw [simulateQ_spec_query]
    simp [firstTable]
  · change Prod.map id _ <$> (simulateQ (firstTable value sampler)
        (f <$> ((unifSpec + (D →ₒ R)).query (.inr point) : OracleComp (unifSpec + (D →ₒ R)) R))).run current = _
    rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    obtain ⟨cache, first⟩ := current
    have mapped : mapCache f cache point = (cache point).map f := rfl
    rcases hit : cache point with _ | answer
    · rcases first with _ | first
      · simp [firstTable, hit, mapped, mapCache_cacheQuery]
      · simp [firstTable, hit, mapped, mapCache_cacheQuery]
    · simp [firstTable, hit, mapped]

end Table

/-! ### The distinguisher of entry 0 and stage S3b -/

section Entry

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRootExpand (rootClient)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The root client of stage S2 with the factored services: the prefix of the KEM-ideal branch and the skeleton's post-challenge phase with the factored services, with the public table at the cut held inside. Its value requests return 108-byte outputs. It has no candidate argument. -/
noncomputable def entryClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : OracleComp (EntrySpec Output) Bool :=
  internalizeV (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index)
    (fun context => postSkel setup codec checks decision count selected (factoredServices setup codec checks) context.1
      context.2.2 context.2.1)

/-- The root client of stage S2 is the factored root client with every value request answered by the 108-byte output of the root at the same coordinates. -/
theorem rootClient_entry (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index =
      simulateQ (relabelR (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index) := by
  unfold rootClient entryClient
  rw [← internalize_relabel]
  congr 1
  funext context
  exact postSkel_factor setup codec checks decision count selected context.1 context.2.2 context.2.1

/-- The key-schedule distinguisher of stage S3b: the factored root client with entry 0, the first hidden coordinate in execution order, answered by the given 108 bytes, and every later hidden coordinate by the 108-byte output of a fresh uniform root. -/
noncomputable def entryD (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : PqxdhServerAuthKeySchedule.Distinguisher :=
  fun value => (simulateQ (firstTable value (PqxdhServerAuthKeySchedule.fromRoot setup.source <$> ($ᵗ RootOutput)))
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' (∅, none)

/-- The eager run of the root client with entry 0's root drawn first is `entryD` at that root's 108-byte output. -/
theorem eager_entryD (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (root : RootOutput) :
    (simulateQ (PqxdhRootFirstEntry.eagerImpl root)
        (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index)).run' (∅, none) =
      entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root) := by
  rw [rootClient_entry, eagerImpl_eq, entryD, StateT.run'_eq, StateT.run'_eq]
  have moved := firstTable_relabel (PqxdhServerAuthKeySchedule.fromRoot setup.source) root ($ᵗ RootOutput)
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index)
    (∅, none)
  rw [mapCache_empty] at moved
  rw [← moved, Functor.map_map]
  rfl

/-- Stage S3b. The uniform-root world of stage S2 on the root client is the key-schedule game on entry 0's distinguisher: entry 0's 32-byte root is uniform, and the game reads it only through its 108-byte key-schedule output. An equality of output distributions; no value is programmed. -/
theorem uniformGame_entry (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[PqxdhCorrelatedExpandHybrid.uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)] =
      𝒟[PqxdhServerAuthKeySchedule.rootHybrid setup.source (entryD (Reader := Reader) setup codec checks ensureInit
        supplied decision work runtime count selected index)] := by
  rw [PqxdhRootFirstEntry.uniformGame_first]
  unfold PqxdhServerAuthKeySchedule.rootHybrid
  congr 2
  funext root
  exact eager_entryD setup codec checks ensureInit supplied decision work runtime count selected index root

/-- Stage S3b for advantages: against any game, the uniform-root world and the key-schedule game on entry 0's distinguisher have the same advantage. -/
theorem rootClient_entryD (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (other : ProbComp Bool) :
    other.boolDistance (PqxdhCorrelatedExpandHybrid.uniformGame (rootClient (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index)) =
      other.boolDistance (PqxdhServerAuthKeySchedule.rootHybrid setup.source (entryD (Reader := Reader) setup codec
        checks ensureInit supplied decision work runtime count selected index)) := by
  unfold ProbComp.boolDistance
  rw [uniformGame_entry]

end Entry

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelR_liftComp' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.relabelR_liftComp

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.publicLocal_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.publicLocal_relabel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.internalize_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.internalize_relabel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.eagerImpl_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.eagerImpl_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapCache_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapCache_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapCache_cacheQuery' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mapCache_cacheQuery

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.firstTable_relabel' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.firstTable_relabel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.rootClient_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.rootClient_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.eager_entryD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.eager_entryD

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.uniformGame_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.uniformGame_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.rootClient_entryD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.rootClient_entryD
