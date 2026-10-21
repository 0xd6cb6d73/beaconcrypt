import BeaconcryptCore.Computational.RawCtxSourceMaterialLabels
import BeaconcryptCore.Computational.PqxdhOrderedChainHybrids

/-!
Fixed-source complete-response memoization at unchanged input/info addresses. The exact arbitrary-stateful continuation law erases only the private table. Initial64 and ongoing76 views share one response; the existing full-output partition retains every byte under arbitrary continuations.

This is functional source equality, not a random publicly evaluable HKDF replacement. The table contains prior chain inputs and next-chain outputs and cannot be passed wholesale to a secret-input observer or exposed by a new network/reveal capability. Local memoization/HMAC/byte work and any sampled unused tail must be accounted separately. No selected-input freshness, restore policy, evolving-key or global-security conclusion follows here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxKdfRequestTable
open PqxdhRefinement PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open BeaconcryptCore.Refinement.RepresentationBridge BeaconcryptCore.Refinement.ProtocolComposition

abbrev Label := RawCtxSourceMaterialLabels.Label

def address (request : Label) : JointKdfAddress :=
  ⟨absBytes request.info, absBytes request.input⟩

def fullResponse (output : FullOutput) : RatchetKdfResponse :=
  ⟨⟨output.toList.map concreteByte, by simp⟩⟩

def initialResponse (output : FullOutput) : pqxdh.concrete.InitialRatchetKdfResponse :=
  ⟨⟨(output.toList.take 64).map concreteByte, by simp⟩⟩

/-- Full response conversion keeps every actual source byte. -/
theorem fullResponse_bytes (output : FullOutput) :
    absBytes (fullResponse output).bytes = output.toList := by
  simp [fullResponse, absBytes, List.map_map, Function.comp_def]

/-- Initial conversion is the actual shared 64-byte prefix, not another derivation. -/
theorem initialResponse_bytes (output : FullOutput) :
    absBytes (initialResponse output).bytes = output.toList.take 64 := by
  simp [initialResponse, absBytes, List.map_map, Function.comp_def]

/-- Every original request retains its input, info and exact 76-byte source response. -/
theorem fullResponse_source (source : FixedHkdfSha512NoSaltSource) (request : Label) :
    fullResponse (productionStream source.crypto (address request)) = RawCtxSourceHkdf.response source.crypto request := by
  rfl

/-- The actual initialization request and later same-address step share their whole first block. -/
theorem initialResponse_source (source : FixedHkdfSha512NoSaltSource)
    (input : Std.Array Std.U8 32#usize) :
    initialResponse (productionStream source.crypto (address ⟨input, ratchet.SYM_RATCHET_INFO⟩)) =
      RawCtxSourceHkdf.initialResponse source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩ := by
  have bytes : absBytes (initialResponse (productionStream source.crypto
      (address ⟨input, ratchet.SYM_RATCHET_INFO⟩))).bytes =
      absBytes (RawCtxSourceHkdf.initialResponse source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩).bytes := by
    rw [initialResponse_bytes, RawCtxSourceHkdf.initialResponse_prefix]
    rw [RawCtxSourceHkdf.response_stream]
    rfl
  have arrays := Subtype.ext ((absBytes_inj_iff _ _).mp bytes)
  exact congrArg pqxdh.concrete.InitialRatchetKdfResponse.mk arrays

abbrev Table := JointKdfRO.QueryCache

def Consistent (source : FixedHkdfSha512NoSaltSource) (table : Table) : Prop :=
  ∀ request output, table request = some output → output = productionStream source.crypto request

/-- The real table starts without extra input/output assumptions. -/
theorem consistent_empty (source : FixedHkdfSha512NoSaltSource) : Consistent source ∅ := by
  intro request output found
  simp at found

/-- Recording the actual complete output preserves every earlier functional binding. -/
theorem consistent_record (source : FixedHkdfSha512NoSaltSource) (table : Table)
    (consistent : Consistent source table) (request : JointKdfAddress) :
    Consistent source (table.cacheQuery request (productionStream source.crypto request)) := by
  intro previous output found
  by_cases same : previous = request
  · subst previous
    simpa using found.symm
  · rw [QueryCache.cacheQuery_of_ne table _ same] at found
    exact consistent previous output found

noncomputable def memoImpl (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl JointKdfRO (StateT Table ProbComp) :=
  QueryImpl.withCaching (spec := JointKdfRO)
    (fun request => (pure (productionStream source.crypto request) : ProbComp _))

/-- Actual fixed-source memoization preserves the entire prior table and exact reply on hits and misses. -/
theorem memo_step (source : FixedHkdfSha512NoSaltSource) (table : Table)
    (consistent : Consistent source table) (request : JointKdfAddress) :
    (memoImpl source request).run table =
      pure (productionStream source.crypto request,
        table.cacheQuery request (productionStream source.crypto request)) := by
  cases found : table request with
  | none => simp [memoImpl, found]
  | some output =>
    have actual := consistent request output found
    subst output
    have retained : table.cacheQuery request (productionStream source.crypto request) = table := by
      funext previous
      by_cases same : previous = request
      · subst previous
        simpa using found.symm
      · exact QueryCache.cacheQuery_of_ne table _ same
    simp [memoImpl, found, retained]

/-- Identical addresses retain the same complete response for every later projection. -/
theorem recorded_lookup (table : Table) (request : JointKdfAddress) (output : FullOutput) :
    (table.cacheQuery request output) request = some output :=
  QueryCache.cacheQuery_self table request output

abbrev KeyPart := List.Vector UInt8 32
abbrev ChainPart := List.Vector UInt8 32
abbrev NoncePart := List.Vector UInt8 12
abbrev Parts := KeyPart × ChainPart × NoncePart

def assemble (parts : Parts) : FullOutput :=
  PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm parts

/-- The existing full-output equivalence retains the target key and both local coordinates without information loss. -/
theorem assemble_parts (output : FullOutput) :
    assemble (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv output) = output :=
  PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm_apply_apply output

/-- A uniform full response partitions into a target key, local next chain and nonce under any complete continuation. -/
theorem full_partition {Result : Type} (next : FullOutput → ProbComp Result) :
    EvalDistEq (do let output ← $ᵗ FullOutput; next output)
      (do let key ← $ᵗ KeyPart
            let chain ← $ᵗ ChainPart
            let nonce ← $ᵗ NoncePart
            next (assemble (key, chain, nonce))) := by
  have uniform : EvalDistEq (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm <$> ($ᵗ Parts : ProbComp Parts))
      ($ᵗ FullOutput : ProbComp FullOutput) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.symm.bijective
  have observed := uniform.bind_left next
  simpa only [bind_map_left, ← pairSample, bind_assoc, pure_bind, assemble] using observed.symm

/-- Erase only memoization state; every other primitive retains its original stateful handler. -/
noncomputable def directImpl {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl (spec + JointKdfRO) (StateT State ProbComp)
  | .inl query => other query
  | .inr request => pure (productionStream source.crypto request)

/-- One private memo table is shared across every complete-stream request. -/
noncomputable def tableImpl {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl (spec + JointKdfRO) (StateT (State × Table) ProbComp)
  | .inl query => fun state => do
      let result ← (other query).run state.1
      pure (result.1, (result.2, state.2))
  | .inr request => fun state => do
      let result ← (memoImpl source request).run state.2
      pure (result.1, (state.1, result.2))

/-- All adaptive continuations retain the exact original result and primitive state. -/
theorem table_complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (table : Table)
    (consistent : Consistent source table) :
    (simulateQ (directImpl source other) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source other) client).run (state, table) := by
  induction client using OracleComp.inductionOn generalizing state table with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      change ((other query).run state >>= fun result =>
        (simulateQ (directImpl source other) (next result.1)).run result.2) =
        (fun result => (result.1, result.2.1)) <$>
          (((other query).run state >>= fun result => pure (result.1, (result.2, table))) >>=
            fun result => (simulateQ (tableImpl source other) (next result.1)).run result.2)
      simp only [bind_assoc, pure_bind, map_bind]
      exact congrArg (fun continuation => (other query).run state >>= continuation)
        (funext fun result => ih result.1 result.2 table consistent)
    | inr request =>
      change (simulateQ (directImpl source other) (next (productionStream source.crypto request))).run state =
        (fun result => (result.1, result.2.1)) <$>
          (((memoImpl source request).run table >>= fun result => pure (result.1, (state, result.2))) >>=
            fun result => (simulateQ (tableImpl source other) (next result.1)).run result.2)
      simpa only [memo_step source table consistent, pure_bind] using
        ih (productionStream source.crypto request) state
          (table.cacheQuery request (productionStream source.crypto request))
          (consistent_record source table consistent request)

end BeaconcryptCore.Computational.RawCtxKdfRequestTable

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.fullResponse_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.fullResponse_bytes

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.initialResponse_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.initialResponse_bytes

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.fullResponse_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.fullResponse_source

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.initialResponse_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.initialResponse_source

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.consistent_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.consistent_empty

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.consistent_record' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.consistent_record

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.memo_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.memo_step

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.recorded_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.recorded_lookup

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.assemble_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.assemble_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.full_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.full_partition

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestTable.table_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestTable.table_complete
