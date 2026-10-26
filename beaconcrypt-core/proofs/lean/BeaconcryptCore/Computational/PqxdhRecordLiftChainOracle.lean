-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget

/-! Private mixed real/uniform coordinate callbacks for ordered chain hybrids. Every logical callback keeps the complete primitive state and charges its native KDF call. Uniform replacement is confined to designated hidden coordinates; no public KDF function is randomized. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainCompiler
open PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {Slot : Type} [DecidableEq Slot]

/-- The actual native KDF ledger increment, preserving all other counts and the complete shared cache. -/
def charge (state : PqxdhRecordLiftWorld.Primitive) : PqxdhRecordLiftWorld.Primitive :=
  ({ state.1 with native := Function.update state.1.native .kdf (state.1.native .kdf + 1) }, state.2)

/-- Sample the complete correlated76 reply while retaining the literal underlying uniform-query instrumentation. -/
noncomputable def sample : StateT PqxdhRecordLiftWorld.Primitive ProbComp FullOutput := fun state => do
  let result ← (simulateQ PqxdhRecordLiftWorld.countCoin ($ᵗ FullOutput)).run state.1.uniform
  pure (result.1, ({ state.1 with uniform := result.2 }, state.2))

/-- Real coordinates execute the deterministic native function on every call. Ideal coordinates reuse their entire stored output, sampling once on a miss. -/
noncomputable def lookup (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) : Lookup Slot PqxdhRecordLiftWorld.Primitive := fun coordinate state => do
  let primitive := charge state.2
  if ideal coordinate then
    match state.1 coordinate with
    | some output => pure (output, (state.1, primitive))
    | none =>
        let result ← sample.run primitive
        pure (result.1, (state.1.cacheQuery coordinate result.1, result.2))
  else
    let output := PqxdhRecordLiftRealTable.output source seeds state.1 coordinate
    pure (output, (state.1.cacheQuery coordinate output, primitive))

/-- The actual76 sampler preserves the ROM and native/effect ledgers and increments only uniform by76. -/
theorem sample_exact (state : PqxdhRecordLiftWorld.Primitive) :
    sample.run state = (fun output => (output,
      ({ state.1 with uniform := state.1.uniform + 76 }, state.2))) <$> ($ᵗ FullOutput) := by
  have counted := PqxdhRecordLiftWorldBudget.sample_fixed_bytes 76 state.1.uniform
  simp only [StateT.run] at counted
  simp only [sample, StateT.run, counted, bind_pure_comp, Functor.map_map]

/-- Real coordinates retain their deterministic response at the interpreted predecessor, even when other coordinates are ideal. -/
def Consistent (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (table : Table Slot) : Prop :=
  ∀ coordinate value, ideal coordinate = false → table coordinate = some value →
    value = PqxdhRecordLiftRealTable.output source seeds table coordinate

/-- Operational table validity: predecessor closure and real-response consistency. -/
def Valid (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (table : Table Slot) : Prop :=
  Closed table ∧ Consistent source seeds ideal table

/-- A persistent reply preserves mixed validity when a real coordinate receives its actual native output. -/
theorem stored_valid (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (table : Table Slot) (valid : Valid source seeds ideal table)
    (coordinate : Coordinate Slot) (available : Available table coordinate) (value : FullOutput)
    (mono : table ≤ table.cacheQuery coordinate value)
    (real : ideal coordinate = false → value = PqxdhRecordLiftRealTable.output source seeds table coordinate) :
    Valid source seeds ideal (table.cacheQuery coordinate value) := by
  constructor
  · intro prior output found
    by_cases same : prior = coordinate
    · subst prior
      exact available_mono table _ mono coordinate available
    · exact available_mono table _ mono prior
        (valid.1 prior output ((QueryCache.cacheQuery_of_ne table value same).symm.trans found))
  · intro prior output isReal found
    by_cases same : prior = coordinate
    · subst prior
      have equal : output = value := by
        simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using found.symm
      exact equal.trans ((real isReal).trans
        (PqxdhRecordLiftRealTable.output_mono source seeds table _ mono coordinate available).symm)
    · have old : table prior = some output :=
        (QueryCache.cacheQuery_of_ne table value same).symm.trans found
      exact (valid.2 prior output isReal old).trans
        (PqxdhRecordLiftRealTable.output_mono source seeds table _ mono prior (valid.1 prior output old)).symm

omit [DecidableEq Slot] in
/-- Empty mixed annotations have no response-consistency or predecessor obligation. -/
theorem valid_empty (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) : Valid source seeds ideal (∅ : Table Slot) := by
  exact ⟨closed_empty, by simp [Consistent]⟩

/-- Every real or ideal callback derives persistent table validity, including repeated ideal hits and repeated real calls. -/
theorem lookup_preserves (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) :
    LookupPreserves (Valid source seeds ideal) (lookup source seeds ideal) := by
  intro coordinate state valid available result supported
  cases selected : ideal coordinate with
  | false =>
    simp only [lookup, StateT.run, selected, Bool.false_eq_true, ite_false,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    have mono : state.1 ≤ state.1.cacheQuery coordinate
        (PqxdhRecordLiftRealTable.output source seeds state.1 coordinate) := by
      intro prior value found
      by_cases same : prior = coordinate
      · subst prior
        simp only [QueryCache.cacheQuery_self, valid.2 coordinate value selected found]
      · exact (QueryCache.cacheQuery_of_ne state.1 _ same).trans found
    exact ⟨mono, QueryCache.cacheQuery_self _ _ _,
      stored_valid source seeds ideal state.1 valid coordinate available _ mono (fun _ => rfl)⟩
  | true =>
    cases found : state.1 coordinate with
    | some value =>
      simp only [lookup, StateT.run, selected, ite_true, found,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨le_refl _, found, valid⟩
    | none =>
      simp only [lookup, StateT.run, selected, ite_true, found,
        bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      have mono := QueryCache.le_cacheQuery (u := inner.1) state.1 found
      exact ⟨mono, QueryCache.cacheQuery_self _ _ _,
        stored_valid source seeds ideal state.1 valid coordinate available inner.1 mono
          (by simp [selected])⟩

/-- A real coordinate always evaluates its exact native function, including a repeat. -/
theorem lookup_real (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot)
    (state : Execution Slot PqxdhRecordLiftWorld.Primitive) (real : ideal coordinate = false) :
    (lookup source seeds ideal coordinate).run state =
      pure (PqxdhRecordLiftRealTable.output source seeds state.1 coordinate,
        (PqxdhRecordLiftRealTable.record source seeds state.1 coordinate, charge state.2)) := by
  simp only [lookup, StateT.run, real, Bool.false_eq_true, ite_false,
    PqxdhRecordLiftRealTable.record]

/-- An ideal hit repeats the complete stored76 bytes, charging the callback but no new randomness. -/
theorem lookup_hit (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot)
    (state : Execution Slot PqxdhRecordLiftWorld.Primitive) (selected : ideal coordinate = true)
    (value : FullOutput) (found : state.1 coordinate = some value) :
    (lookup source seeds ideal coordinate).run state = pure (value, (state.1, charge state.2)) := by
  simp only [lookup, StateT.run, selected, ite_true, found]

/-- An ideal miss samples exactly one full correlated reply and preserves all unrelated primitive fields. -/
theorem lookup_miss (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot)
    (state : Execution Slot PqxdhRecordLiftWorld.Primitive) (selected : ideal coordinate = true)
    (missing : state.1 coordinate = none) :
    (lookup source seeds ideal coordinate).run state =
      (fun value => (value, (state.1.cacheQuery coordinate value,
        ({ (charge state.2).1 with uniform := state.2.1.uniform + 76 }, state.2.2)))) <$> ($ᵗ FullOutput) := by
  have sampled := sample_exact (charge state.2)
  simp only [StateT.run, charge] at sampled
  simp only [lookup, StateT.run, selected, ite_true, missing, sampled,
    bind_pure_comp, Functor.map_map, charge]

/-- The all-real callback is exactly the local source compiler driven by the actual instrumented World KDF. This equality retains the full primitive state. -/
theorem lookup_source {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (seeds : Seeds Slot) :
    lookup setup.source seeds (fun _ => false) =
      realLookup seeds (fun request => PqxdhRecordLiftRealTable.fromResponse <$>
        PqxdhRecordLiftWorld.primitives setup codec (.inl request)) := by
  funext coordinate state
  change (lookup setup.source seeds (fun _ => false) coordinate).run state = _
  rw [lookup_real setup.source seeds (fun _ => false) coordinate state rfl]
  have native : (PqxdhRecordLiftWorld.primitives setup codec
      (.inl (PqxdhRecordLiftRealTable.request seeds state.1 coordinate))).run state.2 =
      pure (RawCtxSourceHkdf.response setup.source.crypto
        (PqxdhRecordLiftRealTable.request seeds state.1 coordinate), charge state.2) := by
    simp [PqxdhRecordLiftWorld.primitives, PqxdhDeploymentNative.primitives,
      RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
      RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl, RawCtxMixedOwner.callKind,
      OracleSpec.query, StateT.run, charge]
    rfl
  change pure (PqxdhRecordLiftRealTable.output setup.source seeds state.1 coordinate,
      (PqxdhRecordLiftRealTable.record setup.source seeds state.1 coordinate, charge state.2)) =
    ((fun result => (PqxdhRecordLiftRealTable.fromResponse result.1, result.2)) <$>
      (PqxdhRecordLiftWorld.primitives setup codec
        (.inl (PqxdhRecordLiftRealTable.request seeds state.1 coordinate))).run state.2) >>= fun reply =>
      pure (reply.1, (state.1.cacheQuery coordinate reply.1, reply.2))
  rw [native, map_pure, pure_bind, ← PqxdhRecordLiftRealTable.output_source,
    PqxdhRecordLiftRealTable.from_fullResponse]
  rfl

/-- Only a missing ideal coordinate requires a fresh full76 sample. -/
def freshCost (ideal : Coordinate Slot → Bool) (table : Table Slot) (coordinate : Coordinate Slot) : Nat :=
  if ideal coordinate then PqxdhRecordLiftLazyTable.freshCost table coordinate else 0

/-- Every supported callback charges one native KDF call, retains the whole ROM/effect state, and charges exactly76 underlying uniform draws only on an ideal miss. -/
theorem lookup_primitive (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot)
    (state : Execution Slot PqxdhRecordLiftWorld.Primitive)
    (result : FullOutput × Execution Slot PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((lookup source seeds ideal coordinate).run state)) :
    result.2.2 = ({ (charge state.2).1 with
      uniform := state.2.1.uniform + 76 * (freshCost ideal state.1 coordinate) }, state.2.2) := by
  cases selected : ideal coordinate with
  | false =>
    rw [lookup_real source seeds ideal coordinate state selected, support_pure,
      Set.mem_singleton_iff] at supported
    subst result
    simp [freshCost, selected, charge]
  | true =>
    cases found : state.1 coordinate with
    | some value =>
      rw [lookup_hit source seeds ideal coordinate state selected value found,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      simp [freshCost, PqxdhRecordLiftLazyTable.freshCost, selected, found, charge]
    | none =>
      rw [lookup_miss source seeds ideal coordinate state selected found, support_map] at supported
      obtain ⟨value, _, rfl⟩ := supported
      simp [freshCost, PqxdhRecordLiftLazyTable.freshCost, selected, found]

set_option maxRecDepth 2048 in
/-- All underlying sampler queries are charged: real calls and ideal hits use zero, while an ideal miss uses at most76. -/
theorem lookup_uniform_bound (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (ideal : Coordinate Slot → Bool) (coordinate : Coordinate Slot)
    (state : Execution Slot PqxdhRecordLiftWorld.Primitive) :
    ((lookup source seeds ideal coordinate).run state).IsTotalQueryBound
      (76 * freshCost ideal state.1 coordinate) := by
  cases selected : ideal coordinate with
  | false =>
    rw [lookup_real source seeds ideal coordinate state selected]
    trivial
  | true =>
    cases found : state.1 coordinate with
    | some value =>
      rw [lookup_hit source seeds ideal coordinate state selected value found]
      trivial
    | none =>
      rw [lookup_miss source seeds ideal coordinate state selected found]
      simp only [freshCost, selected, ite_true, PqxdhRecordLiftLazyTable.freshCost,
        found, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.mul_one]
      exact (isQueryBound_map_iff _ _ _ _ _).mpr
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)

/-- The all-ideal callback is the persistent lazy full76 oracle, with its fresh-draw bill transported to the actual primitive ledger. -/
theorem lookup_lazy (source : FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (coordinate : Coordinate Slot) (state : Execution Slot PqxdhRecordLiftWorld.Primitive) :
    (lookup source seeds (fun _ => true) coordinate).run state =
      (fun result : FullOutput × PqxdhRecordLiftChainTable.State Slot =>
        (result.1, (result.2.1,
          ({ (charge state.2).1 with uniform := state.2.1.uniform + 76 * result.2.2.draws }, state.2.2)))) <$>
        (PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) coordinate).run
          (state.1, ⟨0, 0⟩) := by
  cases found : state.1 coordinate with
  | some value =>
    rw [lookup_hit source seeds (fun _ => true) coordinate state rfl value found,
      PqxdhRecordLiftLazyTable.run_hit coordinate (state.1, ⟨0, 0⟩) value found, map_pure]
    simp [charge]
  | none =>
    rw [lookup_miss source seeds (fun _ => true) coordinate state rfl found,
      PqxdhRecordLiftLazyTable.run_miss coordinate (state.1, ⟨0, 0⟩) found, Functor.map_map]
    rfl

end BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.sample_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.sample_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.stored_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.stored_valid
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.valid_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.valid_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_real
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_hit
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_miss
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_primitive
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_uniform_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainOracle.lookup_lazy
