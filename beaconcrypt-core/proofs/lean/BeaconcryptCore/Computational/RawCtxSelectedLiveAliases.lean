import BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler
import BeaconcryptCore.Computational.RawCtxSelectedAliasInitial

/-!
The same compiled live continuation routes every matching original primitive address to one supplied full76 response. Public label mismatches remain actual fixed evaluation, and read replies are unchanged by alias routing. The bound uses the original complete candidate list, including prior entries; known equal-value chain/skipped-key disclosures count even when no hidden marker is present.

Direct hidden-current-chain disclosure is a separate sticky event. An already-set initial exposure flag is preserved, not reset. The combined bound retains that actual event plus the masked continuation's original candidate event. The native corollary starts from the original fixed-source owner/public/read program and uses its actual production response; it does not call that response uniform or either event unlikely. These are full-state bounds for a supplied selected-kernel representation and one owner. The reached native prefix, uniform-response stopped law, complete earlier root/ancestor classification, first32/initial aliases, other owners and final global freshness-gated security theorem remain separate. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveAliases
open RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def alternate {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl query => RawCtxSelectedAliasPrimitives.alternate source writer output query
  | .inr query => handler source writer output reader (.inr query)

noncomputable def consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (target : RootOutput) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxSelectedAliasCoupling.routed (handler source writer output reader)
    (alternate source writer output reader) inputs target

/-- Actual primitive aliases retain the existing exact label/input routing and complete common cache. -/
theorem primitive_consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (target : RootOutput)
    (query : RawCtxSelectedAliasPrimitives.Spec.Domain) :
    consistent (Auxiliary := Auxiliary) source writer output reader target (.inl query) =
      RawCtxSelectedAliasPrimitives.consistent source writer output target query := rfl

/-- A read keeps its exact optional reply even when that already available value equals the selected bytes. -/
theorem read_consistent {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (target : RootOutput) (query : ReadInput) :
    consistent (Auxiliary := Auxiliary) source writer output reader target (.inr query) =
      pure (reader query.1 query.2) := by
  simp [consistent, RawCtxSelectedAliasCoupling.routed, alternate, handler]
  rfl

noncomputable def consistentGame {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    ProbComp (Result × RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :=
  regroup <$> (simulateQ (RawCtxSelectedQueryTrace.recorded (consistent source writer output reader target) inputs)
    ((simulateQ (compiler sender decode owner) client).run (splitState state).1)).run (splitState state).2

/-- Alias routing in this same live source continuation is charged to its actual full final candidate list, including every prior entry. -/
theorem source_distance {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner reader) client).run state)
      (consistentGame source writer output reader target sender decode owner client state) ≤
      Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner reader) client).run state)}[target ∈ result.2.1.1.2.2].toReal := by
  rw [← source_project source writer output reader sender decode owner client state]
  simp only [prEvent_map, regroup, joinState, consistentGame]
  exact (tvDist_map_le regroup _ _).trans
    (RawCtxSelectedAliasInitial.recorded_distance_initial
      (handler source writer output reader) (alternate source writer output reader) inputs target
      ((simulateQ (compiler sender decode owner) client).run (splitState state).1) (splitState state).2)

private theorem observed_bad {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount)
    (bad : state.2 = true) (result : Result × RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
      sender decode owner reader) client).run state)) : result.2.2 = true := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact bad
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    exact ih reply.1 reply.2 (sticky source writer _ sender decode owner reader query state bad reply head) result tail

/-- Prior direct exposure is retained from the starting state; otherwise the same complete live-read coupling applies. -/
theorem exposure_distance_initial {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner (nativeReader target)) client).run state)
      ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner labelRead) client).run state) ≤
      Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner (nativeReader target)) client).run state)}[result.2.2 = true].toReal := by
  rcases state with ⟨state, prior⟩
  cases prior with
  | false => exact exposure_distance source writer _ sender decode owner target client state
  | true =>
    have one : Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner (nativeReader target)) client).run (state, true))}[result.2.2 = true] = 1 := by
      exact OracleComp.prEvent_eq_one_of_forall_mem_support _ _
        (observed_bad source writer output (nativeReader target) sender decode owner client (state, true) rfl)
    simpa only [one, ENNReal.toReal_one] using
      tvDist_le_one ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner (nativeReader target)) client).run (state, true))
        ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner labelRead) client).run (state, true))

/-- Direct exposure and available-byte aliasing are separate events of the same live continuation; both prior histories survive. -/
theorem exposure_alias_distance {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (target : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner (nativeReader target)) client).run state)
      (consistentGame source writer output labelRead (RawCtxSelectedQueryTrace.rootVector target)
        sender decode owner client state) ≤
      Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner (nativeReader target)) client).run state)}[result.2.2 = true].toReal +
      Pr{let result ← ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
          sender decode owner labelRead) client).run state)}[RawCtxSelectedQueryTrace.rootVector target ∈ result.2.1.1.2.2].toReal := by
  exact (tvDist_triangle _
    ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
      sender decode owner labelRead) client).run state) _).trans
    (add_le_add (exposure_distance_initial source writer output sender decode owner target client state)
      (source_distance source writer output labelRead (RawCtxSelectedQueryTrace.rootVector target)
        sender decode owner client state))

noncomputable def nativeOutput (source : FixedHkdfSha512NoSaltSource) (target : RatchetChain) : FullOutput :=
  PqxdhJointKdf.productionStream source.crypto (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest target))

/-- The bound starts from the actual fixed-source native owner/public/read program and retains its complete state after projection. No native output is assumed uniform. -/
theorem native_distance {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (target : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (RawCtxSelectedLiveSource.sourceImpl source writer sender decode owner) client).run
        (RawCtxSelectedLiveSource.project target state))
      (Prod.map id (RawCtxSelectedLiveSource.project target) <$>
        consistentGame source writer (nativeOutput source target) labelRead (RawCtxSelectedQueryTrace.rootVector target)
          sender decode owner client state) ≤
      Pr{let result ← ((simulateQ (observedImpl source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner (nativeReader target)) client).run state)}[result.2.2 = true].toReal +
      Pr{let result ← ((simulateQ (observedImpl source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner labelRead) client).run state)}[RawCtxSelectedQueryTrace.rootVector target ∈ result.2.1.1.2.2].toReal := by
  rw [RawCtxSelectedLiveSource.source_schedule]
  have projected := (tvDist_map_le (Prod.map id (RawCtxSelectedLiveSource.project target))
    ((simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse (nativeOutput source target))
      sender decode owner (nativeReader target)) client).run state)
    (consistentGame source writer (nativeOutput source target) labelRead (RawCtxSelectedQueryTrace.rootVector target)
      sender decode owner client state)).trans
    (exposure_alias_distance source writer (nativeOutput source target) target sender decode owner client state)
  simpa only [nativeOutput, RawCtxKdfRequestTable.fullResponse_source] using projected

end BeaconcryptCore.Computational.RawCtxSelectedLiveAliases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.primitive_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.primitive_consistent

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.read_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.read_consistent

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.source_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.exposure_distance_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.exposure_distance_initial

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.exposure_alias_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.exposure_alias_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.native_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAliases.native_distance
