import BeaconcryptCore.Computational.RawCtxSelectiveKdfFamily
import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf

/-!
The complete original finite native family and reveal program runs under one shared private full 76-byte cache and a selected-direction cursor. Only a private cache miss at the cursor's exact ratchet address can be randomized, and only before the chosen stage depth. All other misses remain fixed-source evaluations. Hits retain complete earlier bindings. A matching original call advances the cursor through that same reply's next 32-byte projection; nonmatching calls leave its position unchanged. Public HKDF bypasses the private table and remains real.

Stage zero retains the complete native execution, shared primitive state, all role/history fields and the complete private cache after erasing only cursor instrumentation. Adjacent stages differ only at an actual matching miss at their common selected depth. These are exact operational games, not a proof that a chosen logical record reaches a fresh miss, that native byte values cannot alias, or that the selected initial input has the required computational distribution. The consuming protocol reduction must discharge those source and freshness conditions, then instantiate the explicit Extract/PRF observer. No later descendant or unrelated-direction miss is made uniform merely by being a private KDF request. Snapshot, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveChainGame
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxKdfRequestTable

/-- The selected direction's next actual private input and number of matched derivations. -/
structure Cursor where
  input : RootOutput
  depth : Nat

def cursorAddress (cursor : Cursor) : JointKdfAddress := FixedHkdfDomain.ratchet.address cursor.input.toList

def matched (cursor : Cursor) (request : JointKdfAddress) : Bool := decide (request = cursorAddress cursor)

def advance (cursor : Cursor) (request : JointKdfAddress) (output : FullOutput) : Cursor :=
  if matched cursor request then
    ⟨(PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv output).2.1, cursor.depth + 1⟩
  else cursor

abbrev Store := Table × Cursor

/-- Hits retain their original binding. Only a matched selected-prefix miss draws a complete fresh response. -/
noncomputable def privateStep (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) : ProbComp (FullOutput × Store) := do
  let output ← match store.1 request with
    | some output => pure output
    | none => if matched store.2 request && decide (store.2.depth < stage)
        then $ᵗ FullOutput else pure (productionStream source.crypto request)
  pure (output, (store.1.cacheQuery request output, advance store.2 request output))

/-- Repeated private addresses keep their complete response, even when they match the current cursor. -/
theorem private_hit (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (output : FullOutput) (found : store.1 request = some output) :
    privateStep source stage request store =
      pure (output, (store.1.cacheQuery request output, advance store.2 request output)) := by
  simp [privateStep, found]

/-- A selected-prefix miss samples exactly one full response before advancing through its actual next 32-byte projection. -/
theorem private_selected (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (missing : store.1 request = none)
    (selected : matched store.2 request = true) (before : store.2.depth < stage) :
    privateStep source stage request store =
      (fun output => (output, (store.1.cacheQuery request output, advance store.2 request output))) <$> ($ᵗ FullOutput) := by
  simp [privateStep, missing, selected, before, bind_pure_comp]

/-- Every unselected miss remains the actual fixed source computation. -/
theorem private_real (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (missing : store.1 request = none)
    (unselected : matched store.2 request = false ∨ stage ≤ store.2.depth) :
    privateStep source stage request store =
      pure (productionStream source.crypto request,
        (store.1.cacheQuery request (productionStream source.crypto request),
          advance store.2 request (productionStream source.crypto request))) := by
  rcases unselected with unselected | unselected <;> simp [privateStep, missing, unselected, Nat.not_lt_of_ge]

/-- Recording a hit does not change any prior table entry. -/
theorem cache_hit (table : Table) (request : JointKdfAddress) (output : FullOutput)
    (found : table request = some output) : table.cacheQuery request output = table := by
  funext previous
  by_cases same : previous = request
  · subst previous
    simpa using found.symm
  · exact QueryCache.cacheQuery_of_ne table _ same

/-- Stage zero is the original fixed memoized callback with only private cursor bookkeeping added. -/
theorem private_zero (source : FixedHkdfSha512NoSaltSource) (request : JointKdfAddress) (store : Store) :
    privateStep source 0 request store =
      (fun result => (result.1, (result.2, advance store.2 request result.1))) <$>
        (memoImpl source request).run store.1 := by
  cases found : store.1 request with
  | none => simp [privateStep, memoImpl, found]
  | some output => simp [privateStep, memoImpl, found, cache_hit store.1 request output found]

/-- Every other backend operation preserves the private table and cursor; every private derivation retains the same common backend state. -/
noncomputable def handler {ι State : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat) (other : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl (spec + JointKdfRO) (StateT (State × Store) ProbComp)
  | .inl query => fun state => do
      let result ← (other query).run state.1
      pure (result.1, (result.2, state.2))
  | .inr request => fun state => do
      let result ← privateStep source stage request state.2
      pure (result.1, (state.1, result.2))

def project {State Result : Type} (result : Result × (State × Store)) : Result × (State × Table) :=
  (result.1, (result.2.1, result.2.2.1))

/-- Zero selected substitutions retain the complete original result, common state and prior table under every adaptive continuation. -/
theorem zero_complete {ι State Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (other : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp (spec + JointKdfRO) Result) (state : State) (table : Table) (cursor : Cursor) :
    project <$> ((simulateQ (handler source 0 other) client).run (state, (table, cursor))) =
      (simulateQ (tableImpl source other) client).run (state, table) := by
  induction client using OracleComp.inductionOn generalizing state table cursor with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl query =>
      simp only [simulateQ_bind, simulateQ_spec_query, handler, tableImpl,
        StateT.run_bind, map_bind]
      simp only [StateT.run, bind_assoc, pure_bind]
      apply congrArg ((other query state) >>= ·)
      funext result
      exact ih result.1 result.2 table cursor
    | inr request =>
      simp only [simulateQ_bind, simulateQ_spec_query, handler, tableImpl,
        StateT.run_bind, private_zero, bind_map_left, map_bind]
      simp only [StateT.run, bind_assoc, pure_bind]
      apply congrArg (((memoImpl source request).run table) >>= ·)
      funext result
      exact ih result.1 state result.2 (advance cursor request result.1)

/-- The only point where adjacent stages may differ is an actual matched miss at the selected logical depth. -/
def Eligible (stage : Nat) (request : JointKdfAddress) (store : Store) : Prop :=
  store.1 request = none ∧ matched store.2 request = true ∧ store.2.depth = stage

theorem adjacent_same (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (ineligible : ¬ Eligible stage request store) :
    privateStep source stage request store = privateStep source (stage + 1) request store := by
  cases found : store.1 request with
  | some output => rw [private_hit source stage request store output found, private_hit source (stage + 1) request store output found]
  | none =>
    cases selected : matched store.2 request with
    | false => simp [privateStep, found, selected]
    | true =>
      have different : store.2.depth ≠ stage := by simpa [Eligible, found, selected] using ineligible
      have thresholds : (store.2.depth < stage) = (store.2.depth < stage + 1) := propext (by omega)
      simp only [privateStep, found, selected, thresholds]

/-- An eligible adjacent hop changes one real full response to one uniform full response, retaining the same actual table and cursor update continuation. -/
theorem adjacent_splice (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (eligible : Eligible stage request store) :
    privateStep source stage request store =
      pure (productionStream source.crypto request,
        (store.1.cacheQuery request (productionStream source.crypto request),
          advance store.2 request (productionStream source.crypto request))) ∧
    privateStep source (stage + 1) request store =
      (fun output => (output, (store.1.cacheQuery request output, advance store.2 request output))) <$> ($ᵗ FullOutput) := by
  have depth := eligible.2.2
  exact ⟨private_real source stage request store eligible.1 (Or.inr (by omega)),
    private_selected source (stage + 1) request store eligible.1 eligible.2.1 (by omega)⟩

/-- Every supported private reply retains exactly its complete cache update and actual cursor transition. -/
theorem private_state (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (result : FullOutput × Store)
    (supported : result ∈ support (privateStep source stage request store)) :
    result.2 = (store.1.cacheQuery request result.1, advance store.2 request result.1) := by
  cases found : store.1 request with
  | some output =>
    rw [private_hit source stage request store output found, mem_support_pure_iff] at supported
    subst result
    rfl
  | none =>
    by_cases chosen : (matched store.2 request && decide (store.2.depth < stage)) = true
    · simp only [privateStep, found, chosen, ite_true, mem_support_bind_iff, mem_support_pure_iff] at supported
      rcases supported with ⟨output, _, rfl⟩
      rfl
    · simp only [privateStep, found, chosen, pure_bind] at supported
      subst result
      rfl

/-- Nonmatching calls leave the selected logical position unchanged; a matching original call advances it once. -/
theorem advance_depth (cursor : Cursor) (request : JointKdfAddress) (output : FullOutput) :
    (advance cursor request output).depth = cursor.depth + (if matched cursor request then 1 else 0) := by
  simp only [advance]
  split <;> simp_all

set_option maxRecDepth 2048 in
/-- The full 76-byte reservation is charged even though the selected-direction cursor uses only its next 32-byte projection. -/
theorem private_uniform (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) :
    (privateStep source stage request store).IsTotalQueryBound 76 := by
  cases found : store.1 request with
  | some output => rw [private_hit source stage request store output found]; trivial
  | none =>
    simp only [privateStep, found]
    split
    · simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76
    · simp only [pure_bind]
      trivial

/-- The actual finite native role/reveal program runs unchanged under the selected private-table stage. -/
noncomputable def family {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :=
  (simulateQ (handler source stage (RawCtxProtocolBackend.backend source writer))
    (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state)).run (primitive, store)

/-- Zero substitutions preserve the complete private table as well as every native state field and original reply. -/
theorem family_zero {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table) (cursor : Cursor) :
    project <$> family source writer 0 serverCount beaconCount senderId route decode client state primitive (table, cursor) =
      (simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
        (RawCtxSelectiveKdfFamily.program serverCount beaconCount senderId route decode client state)).run (primitive, table) := by
  exact zero_complete source _ _ primitive table cursor

/-- Erasing only analysis cache/cursor recovers the original native family with its full role, history and shared primitive state. -/
theorem source_zero {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table) (cursor : Cursor)
    (consistent : Consistent source table) :
    (fun result => (result.1, result.2.1)) <$>
      (project <$> family source writer 0 serverCount beaconCount senderId route decode client state primitive (table, cursor)) =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount senderId route decode) client).run
          (state, primitive) := by
  rw [family_zero]
  exact (RawCtxSelectiveKdfFamily.source_complete source writer serverCount beaconCount senderId route decode
    client state primitive table consistent).symm

end BeaconcryptCore.Computational.RawCtxSelectiveChainGame

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_real

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.cache_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.cache_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.zero_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.zero_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.adjacent_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.adjacent_same

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.adjacent_splice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.adjacent_splice

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_state

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.advance_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.advance_depth

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.private_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.family_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.family_zero

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveChainGame.source_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveChainGame.source_zero
