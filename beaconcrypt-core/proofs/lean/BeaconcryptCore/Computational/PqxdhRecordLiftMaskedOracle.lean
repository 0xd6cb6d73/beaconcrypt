-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle
import BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads
import BeaconcryptCore.Computational.RawCtxSelectedChainGame
import BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers
import BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters

/-! A private coordinate service can retain one ideal parent's key32/nonce12 while its next32 remains unavailable. The service discards unused full76 replies and preserves the whole primitive state; the successor answer is supplied separately. These are exact source interpreter equations, before the global selected-input game join. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftProjectionCut
open PqxdhRecordLiftMaskedReads PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf
variable {Slot : Type} [DecidableEq Slot]

abbrev Private (Slot : Type) := Mask Slot × PqxdhRecordLiftWorld.Primitive

noncomputable def table (masked : Mask Slot) (hidden : RootOutput) : Table Slot :=
  (realize .chain masked hidden).2.1

def record (masked : Mask Slot) (coordinate : Coordinate Slot) (output : FullOutput) : Mask Slot :=
  { masked with before := masked.before.cacheQuery coordinate output }

/-- An unselected cache write commutes with realization of the unavailable parent field. -/
theorem record_realize (masked : Mask Slot) (hidden : RootOutput)
    (coordinate : Coordinate Slot) (output : FullOutput) (different : coordinate ≠ masked.coordinate) :
    table (record masked coordinate output) hidden = (table masked hidden).cacheQuery coordinate output := by
  apply QueryCache.ext
  intro query
  by_cases parent : query = masked.coordinate
  · subst query
    simp [table, record, realize, QueryCache.cacheQuery_of_ne, Ne.symm different]
  · by_cases selected : query = coordinate
    · subst query
      simp [table, record, realize, QueryCache.cacheQuery_of_ne, different]
    · simp [table, record, realize, QueryCache.cacheQuery_of_ne, parent, selected]

/-- The real source evaluates the unavailable next32 only at its exact structural reader. -/
theorem output_read (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (masked : Mask Slot) (hidden : RootOutput) (coordinate : Coordinate Slot) :
    PqxdhRecordLiftRealTable.output source seeds (table masked hidden) coordinate =
      if Reads coordinate masked.coordinate then
        PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address hidden.toList)
      else PqxdhRecordLiftRealTable.output source seeds masked.before coordinate := by
  simp only [PqxdhRecordLiftRealTable.output, PqxdhRecordLiftRealTable.request, table, chain_next_read]
  split_ifs <;> simp only [RawCtxSelectedChainGame.source_address]

/-- Realize only the private table; all actual primitive fields remain literal. -/
noncomputable def realizeState (hidden : RootOutput) (state : Private Slot) :
    PqxdhRecordLiftChainCompiler.Execution Slot PqxdhRecordLiftWorld.Primitive :=
  (table state.1 hidden, state.2)

/-- The private service never reads the hidden parent32. It repeats the parent without returning its full76, supplies the child response at its reader, and keeps all other real source evaluations and ideal cache behavior. -/
noncomputable def lookup (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (child : FullOutput) (coordinate : Coordinate Slot) :
    StateT (Private Slot) ProbComp Unit := fun state => do
  let primitive := PqxdhRecordLiftChainOracle.charge state.2
  if coordinate = state.1.coordinate then pure ((), (state.1, primitive)) else
    if ideal coordinate then
      match state.1.before coordinate with
      | some _ => pure ((), (state.1, primitive))
      | none =>
          let result ← PqxdhRecordLiftChainOracle.sample.run primitive
          pure ((), (record state.1 coordinate result.1, result.2))
    else
      let output := if Reads coordinate state.1.coordinate then child
        else PqxdhRecordLiftRealTable.output source seeds state.1.before coordinate
      pure ((), (record state.1 coordinate output, primitive))

/-- With the actual source child answer, this private service is exactly the concrete mixed callback with only its unused reply discarded. Parent ideality is the predecessor-order fact supplied by the ordered hybrid. -/
theorem lookup_realization (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (hidden : RootOutput) (coordinate : Coordinate Slot)
    (state : Private Slot) (parentIdeal : ideal state.1.coordinate = true) :
    Prod.map id (realizeState hidden) <$>
      (lookup source seeds ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) coordinate).run state =
      (fun result => ((), result.2)) <$>
        (PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run (realizeState hidden state) := by
  by_cases parent : coordinate = state.1.coordinate
  · subst coordinate
    simp [StateT.run, lookup, PqxdhRecordLiftChainOracle.lookup, parentIdeal, realizeState, table, realize]
  · cases selected : ideal coordinate with
    | false =>
        simp only [StateT.run, lookup, PqxdhRecordLiftChainOracle.lookup, parent, ite_false, selected,
          Bool.false_eq_true, map_pure]
        simp only [Prod.map, id_eq, realizeState, record_realize _ _ _ _ parent, output_read]
    | true =>
        have observed : table state.1 hidden coordinate = state.1.before coordinate := by
          simp [table, realize, QueryCache.cacheQuery_of_ne, parent]
        simp only [StateT.run, lookup, PqxdhRecordLiftChainOracle.lookup, parent, ite_false, selected,
          ite_true, realizeState, observed]
        cases found : state.1.before coordinate <;>
          simp only [map_pure, bind_pure_comp, Functor.map_map, Prod.map, id_eq,
            realizeState, record_realize _ _ _ _ parent]

set_option maxRecDepth 4096 in
/-- The selected mask coordinate survives every actual lookup response. -/
theorem lookup_coordinate (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (child : FullOutput) (coordinate : Coordinate Slot)
    (state : Private Slot) (reply : Unit × Private Slot)
    (supported : reply ∈ support ((lookup source seeds ideal child coordinate).run state)) :
    reply.2.1.coordinate = state.1.coordinate := by
  unfold lookup StateT.run at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst reply
    rfl
  · split at supported
    · split at supported <;> simp_all only [support_pure, Set.mem_singleton_iff, record]
      simp only [bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨value, supported, rfl⟩ := supported
      rfl
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst reply
      rfl

abbrev LoggedPrimitive := PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames
abbrev ServicePrivate (Slot : Type) := Mask Slot × LoggedPrimitive
abbrev ServiceSpec (Slot : Type) := PqxdhRecordLiftOpaqueDrivers.ServiceSpec Slot
  RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted

/-- A fixed public filling is used only for native material reads, which ignore the selected next32. -/
def filling : RootOutput := List.Vector.replicate 32 0

noncomputable def realizeService (hidden : RootOutput) (state : ServicePrivate Slot) :
    PqxdhRecordLiftChainCompiler.Execution Slot LoggedPrimitive := (table state.1 hidden, state.2)

/-- This actual local service interpreter has no unavailable parent32 parameter. The native callbacks retain the original optional replies, primitive state and attempted writer-frame log. -/
noncomputable def interpreter (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (child : FullOutput)
    (opening : PqxdhRecordLiftNativeAdapters.ReceiveNative LoggedPrimitive)
    (sealing : PqxdhRecordLiftNativeAdapters.SendNative LoggedPrimitive) :
    QueryImpl (ServiceSpec Slot) (StateT (ServicePrivate Slot) ProbComp)
  | .inl coordinate => fun state => do
      let result ← (lookup source seeds ideal child coordinate).run (state.1, state.2.1)
      pure ((), (result.2.1, (result.2.2, state.2.2)))
  | .inr (.inl pending) => fun state => do
      let result ← (PqxdhRecordLiftNativeAdapters.receiveOpen opening
        (PqxdhRecordLiftMaterialTable.eraseOpening seeds (table state.1 filling) pending)).run state.2
      pure (result.1, (state.1, result.2))
  | .inr (.inr pending) => fun state => do
      let result ← (PqxdhRecordLiftNativeAdapters.sendSeal sealing
        (PqxdhRecordLiftMaterialTable.eraseSeal seeds (table state.1 filling) pending)).run state.2
      pure (result.1, (state.1, result.2))

/-- Every private service query recovers the actual concrete callback, including the complete writer log. -/
theorem interpreter_realization (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (hidden : RootOutput)
    (opening : PqxdhRecordLiftNativeAdapters.ReceiveNative LoggedPrimitive)
    (sealing : PqxdhRecordLiftNativeAdapters.SendNative LoggedPrimitive)
    (query : (ServiceSpec Slot).Domain) (state : ServicePrivate Slot)
    (parentIdeal : ideal state.1.coordinate = true) :
    Prod.map id (realizeService hidden) <$>
      ((interpreter source seeds ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) opening sealing) query).run state =
      ((PqxdhRecordLiftOpaqueDrivers.interpreter seeds
        (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup source seeds ideal))
        (PqxdhRecordLiftNativeAdapters.receiveOpen opening) (PqxdhRecordLiftNativeAdapters.sendSeal sealing)) query).run
          (realizeService hidden state) := by
  rcases query with coordinate | pending
  · have extended := congrArg (fun distribution =>
      (fun reply : Unit × PqxdhRecordLiftChainCompiler.Execution Slot PqxdhRecordLiftWorld.Primitive =>
        ((), (reply.2.1, (reply.2.2, state.2.2)))) <$> distribution)
        (lookup_realization source seeds ideal hidden coordinate (state.1, state.2.1) parentIdeal)
    change _ = (do
      let reply ← (PqxdhRecordLiftLoggedAdapters.liftLookup
        (PqxdhRecordLiftChainOracle.lookup source seeds ideal) coordinate).run (realizeService hidden state)
      pure ((), reply.2))
    simpa only [interpreter, PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, bind_pure_comp,
      Functor.map_map, Prod.map, id_eq, realizeService, realizeState, Function.comp_def] using extended
  · rcases pending with pending | pending
    · simp only [interpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        realizeService, table, bind_pure_comp, Functor.map_map]
      rw [receive_open_chain_invariant opening state.1 filling hidden seeds pending]
      rfl
    · simp only [interpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        realizeService, table, bind_pure_comp, Functor.map_map]
      rw [send_seal_chain_invariant sealing state.1 filling hidden seeds pending]
      rfl

/-- Every callback preserves the same selected coordinate, even when native opening or sealing fails. -/
theorem interpreter_coordinate (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (child : FullOutput)
    (opening : PqxdhRecordLiftNativeAdapters.ReceiveNative LoggedPrimitive)
    (sealing : PqxdhRecordLiftNativeAdapters.SendNative LoggedPrimitive)
    (query : (ServiceSpec Slot).Domain) (state : ServicePrivate Slot)
    (reply : (ServiceSpec Slot).Range query × ServicePrivate Slot)
    (supported : reply ∈ support ((interpreter source seeds ideal child opening sealing query).run state)) :
    reply.2.1.coordinate = state.1.coordinate := by
  rcases query with coordinate | pending
  · simp only [interpreter, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨result, supported, rfl⟩ := supported
    exact lookup_coordinate source seeds ideal child coordinate (state.1, state.2.1) result supported
  · rcases pending with pending | pending <;>
      simp only [interpreter, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
    all_goals
      obtain ⟨result, supported, rfl⟩ := supported
      rfl

/-- The complete evaluated adaptive local program is simulated without the selected parent32; realizing it restores the actual table and all primitive and writer-log effects. The sole local state premise is the ordered hybrid's parent-ideal marker. -/
theorem schedule_realization {Result : Type} (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (hidden : RootOutput)
    (opening : PqxdhRecordLiftNativeAdapters.ReceiveNative LoggedPrimitive)
    (sealing : PqxdhRecordLiftNativeAdapters.SendNative LoggedPrimitive)
    (client : OracleComp (ServiceSpec Slot) Result) (state : ServicePrivate Slot)
    (parentIdeal : ideal state.1.coordinate = true) :
    Prod.map id (realizeService hidden) <$>
      (simulateQ (interpreter source seeds ideal (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address hidden.toList)) opening sealing) client).run state =
      (simulateQ (PqxdhRecordLiftOpaqueDrivers.interpreter seeds
        (PqxdhRecordLiftLoggedAdapters.liftLookup (PqxdhRecordLiftChainOracle.lookup source seeds ideal))
        (PqxdhRecordLiftNativeAdapters.receiveOpen opening) (PqxdhRecordLiftNativeAdapters.sendSeal sealing)) client).run
          (realizeService hidden state) := by
  exact map_run_simulateQ_eq_of_query_map_eq_inv' _ _
    (fun before : ServicePrivate Slot => ideal before.1.coordinate = true) (realizeService hidden)
    (fun query before beforeIdeal result supported =>
      (congrArg ideal (interpreter_coordinate source seeds ideal _ opening sealing query before result supported)).trans beforeIdeal)
    (fun query before beforeIdeal => interpreter_realization source seeds ideal hidden opening sealing query before beforeIdeal)
    client state parentIdeal

end BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.record_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.record_realize

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.output_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.output_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.lookup_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.lookup_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.lookup_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.lookup_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.interpreter_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.interpreter_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.interpreter_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.interpreter_coordinate

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.schedule_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedOracle.schedule_realization
