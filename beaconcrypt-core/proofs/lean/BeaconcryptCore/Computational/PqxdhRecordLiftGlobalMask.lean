-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol
import BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle

/-! Global private interpretation without a selected ideal parent's next32. The actual source client is unchanged, and every native effect, seed allocation and writer log remains explicit. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask
open PqxdhRecordLiftInterface PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhSecretInputKdf
variable {n : Nat}

structure State (n : Nat) where
  masked : PqxdhRecordLiftProjectionCut.Mask (Slot n)
  primitive : PqxdhRecordLiftWorld.Primitive
  seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  pending : List PqxdhDeploymentNative.Frame

noncomputable def realize (hidden : RootOutput) (state : State n) : PqxdhRecordLiftProtocol.Private n :=
  ⟨state.primitive, state.seeds, PqxdhRecordLiftMaskedOracle.table state.masked hidden,
    state.produced, state.pending⟩

noncomputable def cachedSeeds (state : State n) : PqxdhRecordLiftChainTable.Seeds (Slot n) :=
  fun slot => (state.seeds.1 slot).getD Classical.ofNonempty

def sampled {Result : Type} (work : ProbComp Result) : StateT (State n) ProbComp Result := fun state => do
  let result ← (simulateQ PqxdhRecordLiftWorld.countCoin work).run state.primitive.1.uniform
  pure (result.1, { state with primitive :=
    ({ state.primitive.1 with uniform := result.2 }, state.primitive.2) })

def records (state : State n) : PqxdhRecordLiftMaskedOracle.ServicePrivate (Slot n) :=
  (state.masked, (state.primitive, state.pending))

def putRecords (state : State n) (result : PqxdhRecordLiftMaskedOracle.ServicePrivate (Slot n)) : State n :=
  { state with masked := result.1, primitive := result.2.1, pending := result.2.2 }

def withRecords {Result : Type}
    (work : StateT (PqxdhRecordLiftMaskedOracle.ServicePrivate (Slot n)) ProbComp Result) :
    StateT (State n) ProbComp Result := fun state => do
  let result ← work.run (records state)
  pure (result.1, putRecords state result.2)

def nativeWork {Result : Type}
    (work : StateT PqxdhRecordLiftMaskedOracle.LoggedPrimitive ProbComp Result) :
    StateT (State n) ProbComp Result := fun state => do
  let result ← work.run (state.primitive, state.pending)
  pure (result.1, { state with primitive := result.2.1, pending := result.2.2 })

noncomputable def localInterpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (child : FullOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (state : State n) :=
  PqxdhRecordLiftMaskedOracle.interpreter source (cachedSeeds state) ideal child
    (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
    (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftProtocol.recordNative setup codec))

/-- Allocation and public effects retain their actual state and costs. Hidden local callbacks use the reviewed mask service; caller-known operations keep native source evaluation. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (child : FullOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (State n) ProbComp)
  | .allocate slot => fun state => do
      let result ← (sampled ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)).run state
      pure ((), { result.2 with seeds := result.1.2 })
  | .coin coin => sampled (unifSpec.query coin : ProbComp _)
  | .hash bytes => fun state => do
      let result ← (sampled ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2)).run state
      pure (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })
  | .charge kind => fun state => pure ((), { state with primitive :=
      ({ state.primitive.1 with effects := Function.update state.primitive.1.effects kind (state.primitive.1.effects kind + 1) }, state.primitive.2) })
  | .lookup coordinate => fun state =>
      (withRecords (localInterpreter source ideal child setup codec state (.inl coordinate))).run state
  | .opening pending => fun state =>
      (withRecords (localInterpreter source ideal child setup codec state (.inr (.inl pending)))).run state
  | .sealing pending => fun state =>
      (withRecords (localInterpreter source ideal child setup codec state (.inr (.inr pending)))).run state
  | .knownSend kernel context => nativeWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftProtocol.recordNative setup codec))
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))
  | .knownReceive kernel target context => nativeWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context)))
  | .publish tag => fun state => pure ((), { state with
      produced := state.produced ++ state.pending.map (fun frame => (tag, frame)), pending := [] })

/-- The local mask relation retains all global fields outside the active table/native/writer tuple. -/
theorem local_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (hidden : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftProtocol.LocalSpec n).Domain) (state : State n)
    (parentIdeal : ideal state.masked.coordinate = true) :
    Prod.map id (realize hidden) <$>
      (withRecords (localInterpreter source ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec state query)).run state =
      (PqxdhRecordLiftProtocol.withRecord
        (PqxdhRecordLiftProtocol.localInterpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
          setup codec (cachedSeeds state) query)).run (realize hidden state) := by
  have fact := congrArg (fun program => (fun result =>
      (result.1, PqxdhRecordLiftProtocol.putRecord (realize hidden state) result.2)) <$> program)
    (PqxdhRecordLiftMaskedOracle.interpreter_realization source (cachedSeeds state) ideal hidden
      (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      query (records state) parentIdeal)
  simpa only [withRecords, PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, localInterpreter, PqxdhRecordLiftProtocol.localInterpreter,
    realize, putRecords, records, PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.putRecord,
    PqxdhRecordLiftMaskedOracle.realizeService] using fact

/-- Every actual global service reply and complete private state agrees after restoring the selected parent32. -/
theorem interpreter_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (hidden : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : State n)
    (parentIdeal : ideal state.masked.coordinate = true) :
    Prod.map id (realize hidden) <$>
      (interpreter source ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec query).run state =
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec query).run (realize hidden state) := by
  cases query with
  | lookup coordinate =>
      exact local_realization source ideal hidden setup codec (.inl coordinate) state parentIdeal
  | opening pending =>
      exact local_realization source ideal hidden setup codec (.inr (.inl pending)) state parentIdeal
  | sealing pending =>
      exact local_realization source ideal hidden setup codec (.inr (.inr pending)) state parentIdeal
  | _ =>
      simp only [interpreter, PqxdhRecordLiftProtocol.interpreter, sampled,
        PqxdhRecordLiftProtocol.sampled, nativeWork, PqxdhRecordLiftProtocol.withRecord,
        PqxdhRecordLiftProtocol.primitiveWork, StateT.run, bind_pure_comp, Functor.map_map,
        Prod.map, id_eq, realize, PqxdhRecordLiftProtocol.recordState,
        PqxdhRecordLiftProtocol.putRecord, PqxdhRecordLiftProtocol.publish, map_pure]

/-- All services keep the same selected parent coordinate, including failed optional callbacks and new unrelated allocations. -/
theorem interpreter_coordinate {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (child : FullOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : State n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × State n)
    (supported : result ∈ support ((interpreter source ideal child setup codec query).run state)) :
    result.2.masked.coordinate = state.masked.coordinate := by
  cases query <;>
    simp only [interpreter, withRecords, nativeWork, sampled, StateT.run, bind_pure_comp,
      Functor.map_map, support_map, Set.mem_image, support_pure, Set.mem_singleton_iff] at supported
  all_goals first
    | rcases supported with rfl; rfl
    | obtain ⟨inner, supported, rfl⟩ := supported
      try rfl
  all_goals
    exact PqxdhRecordLiftMaskedOracle.interpreter_coordinate source (cachedSeeds state) ideal child
      (PqxdhRecordLiftWorldCompiler.receiveNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      (PqxdhRecordLiftWorldCompiler.sendNative (PqxdhRecordLiftProtocol.recordNative setup codec))
      _ (records state) inner supported

/-- The same source client runs without the unavailable parent32 through every adaptive service continuation; realization restores the entire concrete global poststate. -/
theorem schedule_realization {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (hidden : RootOutput) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : State n)
    (parentIdeal : ideal state.masked.coordinate = true) :
    Prod.map id (realize hidden) <$>
      (simulateQ (interpreter source ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) setup codec) client).run state =
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal)
        setup codec) client).run (realize hidden state) := by
  exact map_run_simulateQ_eq_of_query_map_eq_inv' _ _
    (fun before : State n => ideal before.masked.coordinate = true) (realize hidden)
    (fun query before beforeIdeal result supported =>
      (congrArg ideal (interpreter_coordinate source ideal _ setup codec query before result supported)).trans beforeIdeal)
    (fun query before beforeIdeal => interpreter_realization source ideal hidden setup codec query before beforeIdeal)
    client state parentIdeal

end BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.local_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.local_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.interpreter_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.interpreter_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.interpreter_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.interpreter_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.schedule_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftGlobalMask.schedule_realization
