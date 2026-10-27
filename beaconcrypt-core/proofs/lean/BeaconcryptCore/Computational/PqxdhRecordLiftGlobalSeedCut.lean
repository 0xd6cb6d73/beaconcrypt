-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftGlobalCut

/-! Actual first allocation and complete directional seed continuations. The private seed mask retains the opposite half and all source state; no sampled reachable-state or independent-family premise is introduced. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut
open PqxdhRecordLiftInterface PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
open PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf
variable {n : Nat}

/-- Private representation of a selected allocation. At the actual cut, prepare retains the opposite directional half and leaves the selected cache entry absent; all source ledgers, unselected seeds, chain outputs and frame logs remain in before. -/
structure Mask (n : Nat) where
  before : PqxdhRecordLiftProtocol.Private n
  slot : Slot n
  direction : Bool
  other : RootOutput

/-- Restoration changes only the selected seed entry. Source sampling and logical lookup counts are retained separately in before. -/
noncomputable def realize (hidden : RootOutput) (state : Mask n) : PqxdhRecordLiftProtocol.Private n :=
  { state.before with seeds :=
    (state.before.seeds.1.cacheQuery state.slot
      (PqxdhRecordLiftSeedCut.restore state.direction state.other hidden), state.before.seeds.2) }

/-- This exact structural reader is the only source chain input that uses the unavailable directional seed half. -/
def Reads (state : Mask n) (coordinate : PqxdhRecordLiftWorldCompiler.Label n) : Prop :=
  coordinate.slot = state.slot ∧ coordinate.direction = state.direction ∧
    coordinate.position = start coordinate.direction

instance readsDecidable (state : Mask n) (coordinate : PqxdhRecordLiftWorldCompiler.Label n) :
    Decidable (Reads state coordinate) := inferInstanceAs (Decidable
      (coordinate.slot = state.slot ∧ coordinate.direction = state.direction ∧
        coordinate.position = start coordinate.direction))

/-- The actual Protocol cache reader sees the restored pair at the selected slot and the original pair at every other slot. -/
theorem seed_read (state : Mask n) (hidden : RootOutput) (slot : Slot n) :
    PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state) slot =
      if slot = state.slot then PqxdhRecordLiftSeedCut.restore state.direction state.other hidden
      else PqxdhRecordLiftProtocol.cachedSeeds state.before slot := by
  by_cases same : slot = state.slot
  · subst slot
    simp [PqxdhRecordLiftProtocol.cachedSeeds, realize]
  · simp [PqxdhRecordLiftProtocol.cachedSeeds, realize, same, QueryCache.cacheQuery_of_ne]

/-- Only the exact selected initial coordinate changes its source KDF input. Every other chain input, including all table fallbacks, is independent of the selected half. -/
theorem chain_read (state : Mask n) (hidden filling : RootOutput) (table : Table (Slot n))
    (coordinate : PqxdhRecordLiftWorldCompiler.Label n) :
    chain (PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state)) table coordinate =
      if Reads state coordinate then RawCtxFreshChainCut.concreteChain hidden
      else chain (PqxdhRecordLiftProtocol.cachedSeeds (realize filling state)) table coordinate := by
  by_cases initial : coordinate.position = start coordinate.direction
  · by_cases selected : coordinate.slot = state.slot
    · cases direction : state.direction <;> cases actual : coordinate.direction <;>
        simp [chain, seed_read, Reads, initial, selected, direction, actual,
          PqxdhRecordLiftSeedCut.restore, PqxdhRecordLiftSeedCut.split]
    · simp [chain, seed_read, Reads, initial, selected]
  · simp [chain, Reads, initial]

/-- The complete deterministic response uses the hidden32 only at the same exact initial reader. Public source evaluation elsewhere remains literal. -/
theorem output_read (source : FixedHkdfSha512NoSaltSource) (state : Mask n)
    (hidden filling : RootOutput) (coordinate : PqxdhRecordLiftWorldCompiler.Label n) :
    PqxdhRecordLiftRealTable.output source
      (PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state)) state.before.chain coordinate =
      if Reads state coordinate then
        PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)
      else PqxdhRecordLiftRealTable.output source
        (PqxdhRecordLiftProtocol.cachedSeeds (realize filling state)) state.before.chain coordinate := by
  simp only [PqxdhRecordLiftRealTable.output, PqxdhRecordLiftRealTable.request,
    chain_read state hidden filling]
  split_ifs <;> simp only [RawCtxSelectedChainGame.source_address]

/-- A chain callback changes only the original chain and primitive fields, retaining both seed counters and all frame logs. -/
def putLookup (state : Mask n) (table : Table (Slot n))
    (primitive : PqxdhRecordLiftWorld.Primitive) : Mask n :=
  { state with before := { state.before with chain := table, primitive := primitive } }

/-- Only a real selected initial lookup uses the supplied full child response. Ideal hits and misses, unselected real work and every native KDF charge remain literal. -/
noncomputable def lookup (source : FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : RootOutput)
    (child : FullOutput) (coordinate : PqxdhRecordLiftWorldCompiler.Label n) :
    StateT (Mask n) ProbComp Unit := fun state => do
  let primitive := PqxdhRecordLiftChainOracle.charge state.before.primitive
  if ideal coordinate then
    match state.before.chain coordinate with
    | some _ => pure ((), putLookup state state.before.chain primitive)
    | none =>
        let result ← PqxdhRecordLiftChainOracle.sample.run primitive
        pure ((), putLookup state (state.before.chain.cacheQuery coordinate result.1) result.2)
  else
    let output := if Reads state coordinate then child
      else PqxdhRecordLiftRealTable.output source
        (PqxdhRecordLiftProtocol.cachedSeeds (realize filling state)) state.before.chain coordinate
    pure ((), putLookup state (state.before.chain.cacheQuery coordinate output) primitive)

/-- With the actual child response, the masked lookup recovers the complete concrete source poststate, discarding only the original unused full-output reply. No coordinate-order, table-validity or byte-separation premise is needed. -/
theorem lookup_realization (source : FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling hidden : RootOutput)
    (coordinate : PqxdhRecordLiftWorldCompiler.Label n) (state : Mask n) :
    Prod.map id (realize hidden) <$>
      (lookup source ideal filling (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) coordinate).run state =
      (fun result => ((), { realize hidden state with chain := result.2.1, primitive := result.2.2 })) <$>
        (PqxdhRecordLiftChainOracle.lookup source
          (PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state)) ideal coordinate).run
            (state.before.chain, state.before.primitive) := by
  cases selected : ideal coordinate with
  | false =>
      simp only [lookup, PqxdhRecordLiftChainOracle.lookup, StateT.run, selected,
        Bool.false_eq_true, ite_false, output_read source state hidden filling]
      simp [putLookup, realize, Prod.map]
  | true =>
      cases found : state.before.chain coordinate <;>
        simp [lookup, PqxdhRecordLiftChainOracle.lookup, StateT.run, selected,
          found, putLookup, realize, Prod.map, bind_pure_comp, Functor.map_map]

/-- Public and caller-known work changes the complete original private state while retaining the selected structural coordinate and retained half. -/
def withPrivate {Result : Type}
    (work : StateT (PqxdhRecordLiftProtocol.Private n) ProbComp Result) :
    StateT (Mask n) ProbComp Result := fun state => do
  let result ← work.run state.before
  pure (result.1, { state with before := result.2 })

/-- A repeat of the selected allocation is a literal cache hit whose Unit reply reveals no seed bytes. Other allocations use the original counted source sampler. -/
noncomputable def allocate (slot : Slot n) : StateT (Mask n) ProbComp Unit := fun state =>
  if slot = state.slot then
    pure ((), { state with before := { state.before with seeds :=
      (state.before.seeds.1, ⟨state.before.seeds.2.lookups + 1, state.before.seeds.2.draws⟩) } })
  else
    (withPrivate (fun secret => do
      let result ← (PqxdhRecordLiftProtocol.sampled
        ((PqxdhRecordLiftLazyTable.impl slot).run secret.seeds)).run secret
      pure ((), { result.2 with seeds := result.1.2 }))).run state

/-- Restoring the selected entry commutes with a cache write at every distinct slot, without comparing seed byte values. -/
theorem seed_cache_commute (cache : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache)
    (selected slot : Slot n) (hidden value : PqxdhRecordLiftSeed.Seed)
    (different : slot ≠ selected) :
    (cache.cacheQuery slot value).cacheQuery selected hidden =
      (cache.cacheQuery selected hidden).cacheQuery slot value := by
  apply QueryCache.ext
  intro query
  by_cases here : query = selected
  · subst query
    simp [Ne.symm different]
  · by_cases there : query = slot
    · subst query
      simp [different]
    · simp [here, there]

/-- Both repeated selected allocations and fresh unrelated allocations retain the literal complete source state and its counted random calls. -/
theorem allocate_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (hidden : RootOutput) (slot : Slot n) (state : Mask n) :
    Prod.map id (realize hidden) <$> (allocate slot).run state =
      (PqxdhRecordLiftProtocol.interpreter policy setup codec (.allocate slot)).run
        (realize hidden state) := by
  have pure_apply {X : Type} (value : X) (count : Nat) :
      (pure value : StateT Nat ProbComp X) count = pure (value, count) := rfl
  have map_apply {X Y : Type} (f : X → Y) (work : StateT Nat ProbComp X) (count : Nat) :
      (f <$> work) count = (fun result => (f result.1, result.2)) <$> work count := by
    exact StateT.run_map _ _ _
  by_cases same : slot = state.slot
  · subst slot
    simp [allocate, PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
      realize, PqxdhRecordLiftLazyTable.impl, QueryImpl.withCachingAux, StateT.mk,
      PqxdhRecordLiftLazyTable.hit, StateT.run, Prod.map, pure_apply]
  · cases found : state.before.seeds.1 slot <;>
      simp [allocate, same, withPrivate, PqxdhRecordLiftProtocol.interpreter,
        PqxdhRecordLiftProtocol.sampled, realize, PqxdhRecordLiftLazyTable.impl,
        QueryImpl.withCachingAux, StateT.mk, QueryCache.cacheQuery_of_ne, found,
        PqxdhRecordLiftLazyTable.hit, PqxdhRecordLiftLazyTable.miss, StateT.run,
        Prod.map, bind_pure_comp, Functor.map_map, pure_apply, map_apply,
        seed_cache_commute _ _ _ _ _ same]

/-- The unchanged global service interface is interpreted without the selected seed half. Only allocation and chain lookup need special handling; all other actual services run on the retained private state. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (child : FullOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (Mask n) ProbComp)
  | .allocate slot => allocate slot
  | .lookup coordinate => lookup source ideal filling child coordinate
  | query => withPrivate (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec query)

/-- Restoring the selected half recovers every actual optional reply and the complete private poststate, including all source caches, counters and attempted writer frames. -/
theorem interpreter_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling hidden : RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : Mask n) :
    Prod.map id (realize hidden) <$>
      (interpreter source ideal filling (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec query).run state =
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec query).run (realize hidden state) := by
  have map_apply {X Y : Type} (f : X → Y)
      (work : StateT (PqxdhRecordLiftProtocol.RecordState n) ProbComp X)
      (records : PqxdhRecordLiftProtocol.RecordState n) :
      (f <$> work) records = (fun result => (f result.1, result.2)) <$> work records :=
    StateT.run_map _ _ _
  cases query with
  | allocate slot => exact allocate_realization _ setup codec hidden slot state
  | lookup coordinate =>
      simpa only [interpreter, PqxdhRecordLiftProtocol.interpreter,
        PqxdhRecordLiftProtocol.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
        PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.recordState,
        PqxdhRecordLiftProtocol.putRecord, PqxdhRecordLiftLoggedAdapters.liftLookup,
        StateT.run, map_apply, bind_pure_comp, Functor.map_map, realize, Prod.map, id_eq]
        using lookup_realization source ideal filling hidden coordinate state
  | _ =>
      simp only [interpreter, withPrivate, PqxdhRecordLiftProtocol.interpreter,
        PqxdhRecordLiftProtocol.sampled, PqxdhRecordLiftProtocol.withRecord,
        PqxdhRecordLiftProtocol.primitiveWork, StateT.run, bind_pure_comp, Functor.map_map,
        Prod.map, id_eq, realize, PqxdhRecordLiftProtocol.recordState,
        PqxdhRecordLiftProtocol.putRecord, PqxdhRecordLiftProtocol.publish, map_pure]
      all_goals simp only [PqxdhRecordLiftProtocol.localInterpreter,
        PqxdhRecordLiftOpaqueDrivers.interpreter]
      all_goals first
        | rw [PqxdhRecordLiftMaskedReads.receive_open_seeds _ _
            (PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state))]
        | rw [PqxdhRecordLiftMaskedReads.send_seal_seeds _ _
            (PqxdhRecordLiftProtocol.cachedSeeds (realize hidden state))]
      all_goals rfl

/-- Every adaptive continuation of the original client runs without the selected seed half. Restoration gives the exact whole source execution, without a reachability or byte-separation premise. -/
theorem schedule_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling hidden : RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : Mask n) :
    Prod.map id (realize hidden) <$>
      (simulateQ (interpreter source ideal filling (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec) client).run state =
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) client).run (realize hidden state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (realize hidden)
    (interpreter_realization source ideal filling hidden setup codec) client state

open PqxdhRecordLiftProtocol (ServiceSpec Private initialPrivate)
variable {Result : Type}

abbrev Cut (n : Nat) (Result : Type) := PqxdhRecordLiftFirstLookup.Cut n Result

/-- Stop the literal adaptive client before the selected slot's first allocation. The complete original Unit continuation is retained. -/
noncomputable def scan (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    OracleComp (ServiceSpec n) (Cut n Result) :=
  OracleComp.recOn client
    (fun result => pure (.complete result))
    (fun query next recurse => match query with
      | .allocate slot =>
          if slot = target then pure (.pending next) else do
            let reply ← (ServiceSpec n).query (.allocate slot)
            recurse reply
      | query => do
          let reply ← (ServiceSpec n).query query
          recurse reply)

noncomputable def finish (target : Slot n) : Cut n Result → OracleComp (ServiceSpec n) Result
  | .complete result => pure result
  | .pending next => (ServiceSpec n).query (.allocate target) >>= next

/-- The first-allocation suspension followed by its original request is exactly the original complete source client, including branches that never allocate the selected slot. -/
theorem scan_finish (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    (scan target client >>= finish target) = client := by
  induction client using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
      cases query with
      | allocate slot =>
          change ((if slot = target then pure (.pending next) else
            (((ServiceSpec n).query (.allocate slot) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) >>= finish target) = _
          split_ifs with same
          · subst slot; rfl
          · simp only [bind_assoc, ih]
      | _ =>
          change ((((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) >>= finish target) = _
          simp only [bind_assoc, ih]

/-- Only allocation at this literal slot can install its seed. -/
def Avoids (target : Slot n) : (ServiceSpec n).Domain → Prop
  | .allocate slot => slot ≠ target
  | _ => True

/-- The selected allocation never occurs in the suspended prefix, on every typed reply branch. -/
theorem scan_avoids (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    (scan target client).AllQueriesSatisfy (Avoids target) := by
  induction client using OracleComp.inductionOn with
  | pure result => exact (show (pure (PqxdhRecordLiftFirstLookup.Cut.complete result) :
      OracleComp (ServiceSpec n) _).AllQueriesSatisfy (Avoids target) by
        simp only [allQueriesSatisfy_pure])
  | query_bind query next ih =>
      cases query with
      | allocate slot =>
          change OracleComp.AllQueriesSatisfy (if slot = target then pure (.pending next) else
            (((ServiceSpec n).query (.allocate slot) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) (Avoids target)
          split_ifs with same <;>
            simp only [allQueriesSatisfy_pure, allQueriesSatisfy_query_bind_iff, Avoids,
              ih, implies_true]
          exact ⟨same, trivial⟩
      | _ =>
          change OracleComp.AllQueriesSatisfy (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) (Avoids target)
          simp only [allQueriesSatisfy_query_bind_iff, Avoids, true_and, ih, implies_true]

/-- Every actual source query except this slot's allocation preserves its seed entry. Random sampling, source counters and callback replies are retained in the support judgment. -/
theorem query_other {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (query : (ServiceSpec n).Domain) (avoids : Avoids target query)
    (secret : Private n) (result : (ServiceSpec n).Range query × Private n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec query).run secret)) :
    result.2.seeds.1 target = secret.seeds.1 target := by
  cases query with
  | allocate slot =>
      simp only [PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
        StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run secret.seeds) := by
        rw [← PqxdhRecordLiftWorld.countCoin_forget
          ((PqxdhRecordLiftLazyTable.impl slot).run secret.seeds) secret.primitive.1.uniform, support_map]
        exact ⟨inner, member, rfl⟩
      cases found : secret.seeds.1 slot with
      | some value =>
          rw [PqxdhRecordLiftLazyTable.run_hit slot secret.seeds value found,
            mem_support_pure_iff] at original
          exact congrArg (fun pair => pair.2.1 target) original
      | none =>
          rw [PqxdhRecordLiftLazyTable.run_miss slot secret.seeds found, support_map] at original
          obtain ⟨value, _, same⟩ := original
          simp only [← same, QueryCache.cacheQuery_of_ne _ _ (Ne.symm avoids)]
  | _ =>
      simp only [PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
        PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork,
        StateT.run, bind_pure_comp, Functor.map_map, support_map, mem_support_pure_iff] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      rfl

/-- A complete adaptive prefix that has not allocated the selected slot preserves its exact seed entry under the actual mixed source interpreter. -/
theorem avoids_preserves {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result)
    (avoids : client.AllQueriesSatisfy (Avoids target)) (secret : Private n) (result : Result × Private n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run secret)) :
    result.2.seeds.1 target = secret.seeds.1 target := by
  induction client using OracleComp.inductionOn generalizing secret with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at avoids
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      exact (ih middle.1 (avoids.2 middle.1) middle.2 supported).trans
        (query_other source ideal setup codec target query avoids.1 secret middle reached)

/-- The source prefix starts from the real empty seed cache, so its selected allocation is a genuine first draw. All earlier native, known-key, public and allocation effects remain in its actual private state. -/
theorem scan_initial_missing {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) (result : Cut n Result × Private n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate)) :
    result.2.seeds.1 target = none :=
  avoids_preserves source ideal setup codec target (scan target client) (scan_avoids target client)
    initialPrivate result supported

/-- Attach the derived miss proof to the actual prefix, without rejecting, conditioning or changing any execution. -/
noncomputable def sampledPrefix {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    ProbComp { result : Cut n Result × Private n // result.2.seeds.1 target = none } :=
  (fun reached => ⟨reached.val, scan_initial_missing source ideal setup codec target client reached.val reached.property⟩) <$>
    PFunctor.FreeM.attachSupp ((simulateQ (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate)

/-- Erasing only the miss certificate leaves the exact evaluated prefix and complete private state. -/
theorem prefix_forget {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    Subtype.val <$> sampledPrefix source ideal setup codec target client =
      (simulateQ (PqxdhRecordLiftProtocol.interpreter
        (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run initialPrivate := by
  simp only [sampledPrefix, Functor.map_map]
  exact PFunctor.FreeM.map_attachSupp _

/-- The certified actual prefix followed by its suspended allocation and original continuation recovers the complete source execution. -/
theorem resume_prefix {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    (sampledPrefix source ideal setup codec target client >>= fun reached =>
      (simulateQ (PqxdhRecordLiftProtocol.interpreter
        (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec)
        (finish target reached.val.1)).run reached.val.2) =
      (simulateQ (PqxdhRecordLiftProtocol.interpreter
        (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) client).run initialPrivate := by
  have original := congrArg (fun work =>
    (simulateQ (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) work).run initialPrivate)
    (scan_finish target client)
  rw [simulateQ_bind, StateT.run_bind, ← prefix_forget] at original
  simpa only [bind_map_left] using original

/-- The actual fresh allocation charges one logical lookup, one seed draw and all sixty-four underlying byte queries. No native, effect, ROM, chain or frame field changes. -/
def afterAllocation (secret : Private n) : Private n :=
  { secret with
    seeds := (secret.seeds.1, ⟨secret.seeds.2.lookups + 1, secret.seeds.2.draws + 1⟩)
    primitive := ({ secret.primitive.1 with uniform := secret.primitive.1.uniform + 64 }, secret.primitive.2) }

def install (secret : Private n) (target : Slot n) (seed : PqxdhRecordLiftSeed.Seed) : Private n :=
  { afterAllocation secret with seeds := (secret.seeds.1.cacheQuery target seed, (afterAllocation secret).seeds.2) }

def prepare (secret : Private n) (target : Slot n) (direction : Bool) (other : RootOutput) : Mask n :=
  ⟨afterAllocation secret, target, direction, other⟩

/-- The actual Protocol allocator installs one complete seed pair and preserves its exact whole source state and costs. -/
theorem allocate_miss {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (secret : Private n) (missing : secret.seeds.1 target = none) :
    (PqxdhRecordLiftProtocol.interpreter policy setup codec (.allocate target)).run secret =
      (fun seed => ((), install secret target seed)) <$> ($ᵗ PqxdhRecordLiftSeed.Seed) := by
  have miss := PqxdhRecordLiftLazyTable.run_miss target secret.seeds missing
  simp only [StateT.run] at miss
  simp only [PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
    StateT.run, miss, simulateQ_map, bind_pure_comp, Functor.map_map]
  have mapped := StateT.run_map
    (fun seed : PqxdhRecordLiftSeed.Seed => (seed, (secret.seeds.1.cacheQuery target seed,
      (⟨secret.seeds.2.lookups + 1, secret.seeds.2.draws + 1⟩ : PqxdhRecordLiftLazyTable.Counts))))
    (simulateQ PqxdhRecordLiftWorld.countCoin ($ᵗ PqxdhRecordLiftSeed.Seed)) secret.primitive.1.uniform
  have counted := PqxdhRecordLiftWorldBudget.sample_seed secret.primitive.1.uniform
  simp only [StateT.run] at mapped counted
  rw [mapped, counted, Functor.map_map, Functor.map_map]
  rfl

/-- Rejoining either directional split restores the complete actual allocator poststate, not only its seed marginal. -/
theorem prepare_realize (secret : Private n) (target : Slot n) (direction : Bool)
    (seed : PqxdhRecordLiftSeed.Seed) :
    realize (PqxdhRecordLiftSeedCut.secret direction seed)
      (prepare secret target direction (PqxdhRecordLiftSeedCut.retained direction seed)) =
        install secret target seed := by
  simp only [realize, prepare, afterAllocation, install, PqxdhRecordLiftSeedCut.restore_split]

/-- At the actual first allocation, either directional half is an independent uniform32 under the entire continuation, retaining the opposite32 and complete source state. -/
theorem miss_continuation {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (secret : Private n) (missing : secret.seeds.1 target = none)
    (continuation : Unit × Private n → ProbComp Result) :
    LazyOracleDiscard.LawEq
      ((PqxdhRecordLiftProtocol.interpreter policy setup codec (.allocate target)).run secret >>= continuation)
      (do let other ← $ᵗ RootOutput
          let hidden ← $ᵗ RootOutput
          continuation ((), realize hidden (prepare secret target direction other))) := by
  rw [allocate_miss policy setup codec target secret missing, bind_map_left]
  intro Observed _ observe
  simp only [bind_assoc]
  refine EvalDistEq.evalDist_eq ?_
  simpa only [prepare_realize] using PqxdhRecordLiftSeedCut.split_continuation direction
    (fun other hidden => continuation ((), realize hidden (prepare secret target direction other)) >>= observe)

/-- Split the pair only when the actual client reaches its selected allocation. A completed prefix keeps its original state and performs no seed sampling. -/
noncomputable def splitRun {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result) :
    ProbComp (Result × Private n) := do
  let reached ← sampledPrefix source ideal setup codec target client
  match reached.val.1 with
  | .complete result => pure (result, reached.val.2)
  | .pending next => do
      let other ← $ᵗ RootOutput
      let hidden ← $ᵗ RootOutput
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) (next ())).run (realize hidden (prepare reached.val.2 target direction other))

/-- The genuine first allocator prefix supplies either independent directional half under the complete original adaptive source continuation and full private state. -/
theorem source_split {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result) :
    LazyOracleDiscard.LawEq
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) client).run initialPrivate)
      (splitRun source ideal setup codec target direction client) := by
  rw [← resume_prefix source ideal setup codec target client]
  unfold splitRun
  apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
  intro reached
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [finish, simulateQ_pure, StateT.run_pure]
      exact LazyOracleDiscard.LawEq.refl _
  | pending next =>
      simp only [finish, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact miss_continuation _ setup codec target direction reached.val.2 reached.property
        (fun result => (simulateQ (PqxdhRecordLiftProtocol.interpreter
          (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (next result.1)).run result.2)

/-- The same explicit observer boundary as the parent-chain cut retains the client result, shared ROM and frame logs. It does not reveal hidden seeds or table bytes. -/
abbrev Observer (Result : Type) := PqxdhRecordLiftGlobalCut.Observer Result

def observeMasked (observer : Observer Result) (result : Result × Mask n) : ProbComp Bool :=
  observer result.1 result.2.before.primitive.2 result.2.before.produced result.2.before.pending

/-- The entire source suffix and permitted later observer use the selected half only through its supplied full child response. Full source restoration precedes the explicit private-state projection. -/
theorem continuation_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling hidden : RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : Mask n) (observer : Observer Result) :
    ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
      setup codec) client).run (realize hidden state) >>= PqxdhRecordLiftGlobalCut.observe observer) =
      ((simulateQ (interpreter source ideal filling (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec) client).run state >>= observeMasked observer) := by
  rw [← schedule_realization source ideal filling hidden setup codec client state, bind_map_left]
  rfl

abbrev Context (n : Nat) (Result : Type) := Cut n Result × Private n

/-- The suffix receives the actual reached prefix and retained opposite half. It never receives the selected32; its sole selected KDF argument is the supplied full child. -/
noncomputable def seedObserver {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (observer : Observer Result) :
    FullObserver (Context n Result × RootOutput) := fun input child =>
  match input.1.1 with
  | .complete result => PqxdhRecordLiftGlobalCut.observe observer (result, input.1.2)
  | .pending next =>
      (simulateQ (interpreter source ideal filling child setup codec) (next ())).run
        (prepare input.1.2 target direction input.2) >>= observeMasked observer

/-- Sample the actual source prefix first and retain the independent opposite directional half. The attached miss proof adds no work. -/
noncomputable def retainedContext {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) :
    ProbComp (Context n Result × RootOutput) := do
  let reached ← sampledPrefix source ideal setup codec target client
  let other ← $ᵗ RootOutput
  pure (reached.val, other)

noncomputable def seedReal {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) : ProbComp Bool := do
  let context ← retainedContext source ideal setup codec target client
  let hidden ← $ᵗ RootOutput
  seedObserver source ideal filling setup codec target direction observer context
    (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList))

/-- The ordinary source event is exactly the constructed secret-input experiment. Extra unused reduction draws on a completed prefix do not change the observed law. -/
theorem observed_real {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) :
    LazyOracleDiscard.LawEq
      ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) client).run initialPrivate >>= PqxdhRecordLiftGlobalCut.observe observer)
      (seedReal source ideal filling setup codec target direction client observer) := by
  apply ((source_split source ideal setup codec target direction client).bind
    (fun result => LazyOracleDiscard.LawEq.refl (PqxdhRecordLiftGlobalCut.observe observer result))).trans
  simp only [splitRun, seedReal, retainedContext, bind_assoc, pure_bind]
  apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
  intro reached
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [seedObserver, stopped, pure_bind]
      exact ((LazyOracleDiscard.lawEq_drop ($ᵗ RootOutput) _).trans
        (LazyOracleDiscard.lawEq_drop ($ᵗ RootOutput)
          (PqxdhRecordLiftGlobalCut.observe observer (result, reached.val.2)))).symm
  | pending next =>
      simp only [seedObserver, stopped, bind_assoc]
      simp_rw [continuation_source source ideal filling _ setup codec]
      exact LazyOracleDiscard.LawEq.refl _

/-- The primitive input has only Unit context. Its observer independently samples the actual source prefix, retains the opposite32 and resumes the original continuation. -/
noncomputable def reductionObserver {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) : FullObserver Unit := fun _ child => do
  let context ← retainedContext source ideal setup codec target client
  seedObserver source ideal filling setup codec target direction observer context child

/-- The genuine global seed cut has the ordinary uniform32 source-input law; the actual prefix and retained directional half are sampled by the explicit reduction observer. -/
theorem observed_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) :
    𝒟[((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) client).run initialPrivate >>= PqxdhRecordLiftGlobalCut.observe observer)] =
      𝒟[sourceFullGame source .ratchet PqxdhServerAuthKeySchedule.uniform32
        (reductionObserver source ideal filling setup codec target direction client observer)] := by
  have actual := (observed_real source ideal filling setup codec target direction client observer).evalDist_eq
  rw [actual]
  refine EvalDistEq.evalDist_eq ?_
  simpa only [seedReal, sourceFullGame, PqxdhServerAuthKeySchedule.uniform32,
    reductionObserver, bind_assoc, pure_bind] using
    evalSPMF_sample_comm (retainedContext source ideal setup codec target client) ($ᵗ RootOutput)
      (fun context hidden => seedObserver source ideal filling setup codec target direction observer context
        (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)))

/-- The independent endpoint supplies one uniform full child to the same masked actual continuation. Identifying it with a neighboring source policy is a separate operational obligation. -/
noncomputable def seedUniform {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) : ProbComp Bool := do
  let context ← retainedContext source ideal setup codec target client
  let child ← $ᵗ FullOutput
  seedObserver source ideal filling setup codec target direction observer context child

/-- The independent component game retains the actual prefix/opposite-half/suffix law and discards only its unused independent primitive input. -/
theorem uniform_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) :
    𝒟[seedUniform source ideal filling setup codec target direction client observer] =
      𝒟[independentFullGame PqxdhServerAuthKeySchedule.uniform32
        (reductionObserver source ideal filling setup codec target direction client observer)] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [seedUniform, independentFullGame, PqxdhServerAuthKeySchedule.uniform32,
    reductionObserver, bind_assoc, pure_bind]
  exact (evalSPMF_sample_comm (retainedContext source ideal setup codec target client) ($ᵗ FullOutput)
    (seedObserver source ideal filling setup codec target direction observer)).trans
      (OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _).symm

/-- Either directional global seed cut has a coefficient-one ordinary uniform32 Extract and two-query uniform-secret-key HMAC bound. The sole source premise is the existing functional HKDF implementation equality; this is not yet an adjacent-policy or global security theorem. -/
theorem observed_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) :
    (((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
      setup codec) client).run initialPrivate >>= PqxdhRecordLiftGlobalCut.observe observer)).boolDistance
      (seedUniform source ideal filling setup codec target direction client observer) ≤
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (reductionObserver source ideal filling setup codec target direction client observer))).boolDistance
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (reductionObserver source ideal filling setup codec target direction client observer))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer))).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer))) := by
  simpa only [ProbComp.boolDistance,
    observed_source source ideal filling setup codec target direction client observer,
    uniform_source source ideal filling setup codec target direction client observer] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer)

/-- Suspending the actual allocator cannot increase any selective all-reply query allowance of the original source client. -/
theorem scan_bound (target : Slot n) (client : OracleComp (ServiceSpec n) Result)
    (predicate : (ServiceSpec n).Domain → Prop) [DecidablePred predicate]
    (cap : Nat) (bounded : client.IsQueryBoundP predicate cap) :
    (scan target client).IsQueryBoundP predicate cap := by
  induction client using OracleComp.inductionOn generalizing cap with
  | pure result => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      cases query with
      | allocate slot =>
          change OracleComp.IsQueryBoundP (if slot = target then pure (.pending next) else
            (((ServiceSpec n).query (.allocate slot) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => scan target (next reply))) predicate cap
          split_ifs with same
          · trivial
          · rw [isQueryBoundP_query_bind_iff]
            exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      | _ =>
          change OracleComp.IsQueryBoundP (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => scan target (next reply)) predicate cap
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- Attaching the derived miss certificate preserves every selective allowance of the actual evaluated prefix. -/
theorem sampledPrefix_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : ((simulateQ (PqxdhRecordLiftProtocol.interpreter
      (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec) (scan target client)).run
        initialPrivate).IsQueryBoundP predicate cap) :
    (sampledPrefix source ideal setup codec target client).IsQueryBoundP predicate cap := by
  rw [← prefix_forget] at bounded
  exact (isQueryBoundP_map_iff _ Subtype.val cap).mp bounded

/-- The concrete reduction pays for every actual prefix draw, the retained32 and the complete supported suffix. A suffix allowance is required only for contexts reached by this exact prefix. -/
theorem reductionObserver_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (sampledPrefix source ideal setup codec target client),
      ∀ other child, (seedObserver source ideal filling setup codec target direction observer
        (reached.val, other) child).IsTotalQueryBound qSuffix)
    (context : Unit) (output : FullOutput) :
    (reductionObserver source ideal filling setup codec target direction client observer context output).IsTotalQueryBound
      (qPrefix + (32 + qSuffix)) := by
  simp only [reductionObserver, retainedContext, bind_assoc, pure_bind]
  exact isTotalQueryBound_bind_of_mem_support prefixBound (fun reached supported =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun other => suffixBound reached supported other output))

/-- The original observed source experiment pays for its actual prefix, the complete 64-byte seed allocation if reached, and every supported suffix query. Early completion spends no seed queries. -/
theorem observed_query_bound {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (sampledPrefix source ideal setup codec target client),
      ∀ other child, (seedObserver source ideal filling setup codec target direction observer
        (reached.val, other) child).IsTotalQueryBound qSuffix) :
    ((simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
      setup codec) client).run initialPrivate >>= PqxdhRecordLiftGlobalCut.observe observer).IsTotalQueryBound
      (qPrefix + (64 + qSuffix)) := by
  rw [← resume_prefix source ideal setup codec target client, bind_assoc]
  apply isTotalQueryBound_bind_of_mem_support prefixBound
  intro reached supported
  cases stopped : reached.val.1 with
  | complete result =>
      have bounded := (suffixBound reached supported filling
        (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address filling.toList))).mono
          (Nat.le_add_left qSuffix 64)
      simpa only [finish, simulateQ_pure, StateT.run_pure, pure_bind, seedObserver, stopped] using bounded
  | pending next =>
      simp only [finish, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        allocate_miss _ setup codec target reached.val.2 reached.property, bind_map_left, bind_assoc]
      apply isTotalQueryBound_bind PqxdhRecordLiftSeedCut.seed_bound
      intro seed
      rw [← prepare_realize reached.val.2 target direction seed,
        continuation_source source ideal filling _ setup codec]
      simpa only [seedObserver, stopped] using suffixBound reached supported
        (PqxdhRecordLiftSeedCut.retained direction seed)
        (PqxdhJointKdf.productionStream source.crypto
          (FixedHkdfDomain.ratchet.address (PqxdhRecordLiftSeedCut.secret direction seed).toList))

/-- The explicit HMAC reduction makes at most two challenge calls. Uniform input32, actual prefix work, retained32 and the supported suffix are charged separately. -/
theorem reduction_bounds {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (filling : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (sampledPrefix source ideal setup codec target client),
      ∀ other child, (seedObserver source ideal filling setup codec target direction observer
        (reached.val, other) child).IsTotalQueryBound qSuffix) :
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer)).IsQueryBoundP IsHmacUniformQuery
        (32 + (qPrefix + (32 + qSuffix))) := by
  refine ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ ?_
      (reductionObserver_bound source ideal filling setup codec target direction client observer
        qPrefix qSuffix prefixBound suffixBound)⟩
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)

/-- All four challenger worlds retain the full actual-prefix/suffix allowance and sample complete 64-byte HMAC keys or replies, including the complete second reply whose source expansion uses only 12 bytes. -/
theorem challenger_bounds {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool) (filling : RootOutput)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (target : Slot n) (direction : Bool) (client : OracleComp (ServiceSpec n) Result)
    (observer : Observer Result) (qPrefix qSuffix : Nat)
    (prefixBound : (sampledPrefix source ideal setup codec target client).IsTotalQueryBound qPrefix)
    (suffixBound : ∀ reached ∈ support (sampledPrefix source ideal setup codec target client),
      ∀ other child, (seedObserver source ideal filling setup codec target direction observer
        (reached.val, other) child).IsTotalQueryBound qSuffix) :
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (reductionObserver source ideal filling setup codec target direction client observer))).IsTotalQueryBound
        (32 + (qPrefix + (32 + qSuffix))) ∧
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (reductionObserver source ideal filling setup codec target direction client observer))).IsTotalQueryBound
        (32 + (64 + (qPrefix + (32 + qSuffix)))) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer))).IsTotalQueryBound
        (64 + (32 + (qPrefix + (32 + qSuffix)))) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (reductionObserver source ideal filling setup codec target direction client observer))).IsTotalQueryBound
        (32 + (64 + (64 + (qPrefix + (32 + qSuffix))))) := by
  have inputBound : PqxdhServerAuthKeySchedule.uniform32.IsTotalQueryBound 32 :=
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)
  have observerBound := reductionObserver_bound source ideal filling setup codec target direction client observer
    qPrefix qSuffix prefixBound suffixBound
  exact ⟨isTotalQueryBound_bind inputBound (fun pair => observerBound pair.1 _),
    fullExtractUniform_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ inputBound observerBound⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.seed_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.seed_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.output_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.output_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.lookup_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.lookup_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.seed_cache_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.seed_cache_commute

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.allocate_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.allocate_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.interpreter_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.interpreter_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.schedule_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.schedule_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_avoids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_avoids

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.query_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.query_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.avoids_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.avoids_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_initial_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_initial_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.prefix_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.prefix_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.resume_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.resume_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.allocate_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.allocate_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.prepare_realize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.prepare_realize

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.miss_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.miss_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.source_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.source_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.continuation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.uniform_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.scan_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.sampledPrefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.sampledPrefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.reductionObserver_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.reductionObserver_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.observed_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut.challenger_bounds
