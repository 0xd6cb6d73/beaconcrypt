import BeaconcryptCore.Computational.RawCtxPendingOwnerQueries

/-!
The full pending owner interface also retains the existing selected owner's adaptive live reads, original history and exposure bit. Erasure reconstructs the same original compiler before any private state or public reply is projected. Private full pending payloads are not network or reveal capabilities. This is an operational interface theorem; reached-input freshness and cryptographic hybrids remain separate consuming obligations. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingLiveQueries
open RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxSelectedLiveTrace
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Spec := RawCtxPendingOwnerQueries.Spec Slot + RawCtxSelectedLiveCompiler.ReadQueries
abbrev OuterState := RawCtxSelectedLiveCompiler.OuterState

def primitiveForward : QueryImpl (RawCtxPendingOwnerQueries.Spec Slot) (OracleComp Spec) :=
  fun query => Spec.query (.inl query)

def erase : QueryImpl Spec (OracleComp RawCtxSelectedLiveCompiler.Spec)
  | .inl query => simulateQ RawCtxSelectedLiveCompiler.primitiveForward
      (RawCtxPendingOwnerQueries.erase query)
  | .inr query => RawCtxSelectedLiveCompiler.Spec.query (.inr query)

noncomputable def compiler {Metadata : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (OuterState Metadata serverCount beaconCount) (OracleComp Spec)) :=
  fun query state => match query with
  | .inl request => do
      let result ← simulateQ primitiveForward ((RawCtxPendingOwnerQueries.compiler sender decode request).run state.1.1)
      pure (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))
  | .inr read => do
      let entry := some state.1.1.kernel
      let reply ← Spec.query (.inr (read, entry))
      pure (reply, ((state.1.1, RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
        state.2 || exposed read entry))

/-- Erasing a full pending primitive retains the existing original primitive's whole reply interface. -/
theorem primitive_erase : erase ∘ₛ primitiveForward =
    RawCtxSelectedLiveCompiler.primitiveForward ∘ₛ RawCtxPendingOwnerQueries.erase := by
  funext query
  exact _root_.simulateQ_spec_query erase (.inl query)

/-- All live/public/record steps retain exact optional replies, owner fields, chronology and exposure bookkeeping. -/
theorem step_erase {Metadata : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : SourceSpec.Domain) (state : OuterState Metadata serverCount beaconCount) :
    simulateQ erase ((compiler sender decode owner query).run state) =
      (RawCtxSelectedLiveCompiler.compiler sender decode owner query).run state := by
  cases query with
  | inl request =>
      simp only [compiler, RawCtxSelectedLiveCompiler.compiler, StateT.run, bind_pure_comp]
      refine (simulateQ_map _ _ _).trans ?_
      rw [← QueryImpl.simulateQ_compose, primitive_erase, QueryImpl.simulateQ_compose]
      exact congrArg (fun work => (fun result => (result.1,
        ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$>
          simulateQ RawCtxSelectedLiveCompiler.primitiveForward work)
        (RawCtxPendingOwnerQueries.step_erase sender decode request state.1.1)
  | inr read =>
      simp [compiler, RawCtxSelectedLiveCompiler.compiler, StateT.run, erase, OracleSpec.query]

/-- Every finite adaptive live schedule erases before projecting any retained private state or public result. -/
theorem schedule_erase {Metadata Result : Type} {serverCount beaconCount : Nat}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : OuterState Metadata serverCount beaconCount) :
    simulateQ erase ((simulateQ (compiler sender decode owner) client).run state) =
      (simulateQ (RawCtxSelectedLiveCompiler.compiler sender decode owner) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact congrArg (fun impl : QueryImpl SourceSpec
    (StateT (OuterState Metadata serverCount beaconCount) (OracleComp RawCtxSelectedLiveCompiler.Spec)) =>
      (simulateQ impl client).run state)
    (funext fun query => funext fun outer => step_erase sender decode owner query outer)

/-- Full pending queries produce the same original live source trace and complete owner/history/primitive/candidate state. -/
theorem source_project {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (output : FullOutput) (reader : Reader) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    RawCtxSelectedLiveCompiler.regroup <$>
      (simulateQ (RawCtxSelectedLiveCompiler.recorded source writer output reader ∘ₛ erase)
        ((simulateQ (compiler sender decode owner) client).run (RawCtxSelectedLiveCompiler.splitState state).1)).run
          (RawCtxSelectedLiveCompiler.splitState state).2 =
      (simulateQ (observedImpl source writer (RawCtxKdfRequestTable.fullResponse output)
        sender decode owner reader) client).run state := by
  rw [QueryImpl.simulateQ_compose, schedule_erase]
  exact RawCtxSelectedLiveCompiler.source_project source writer output reader sender decode owner client state

def originalQuery : Spec.Domain → RawCtxSelectedLiveCompiler.Spec.Domain
  | .inl request => .inl (RawCtxPendingOwnerQueries.originalQuery request)
  | .inr read => .inr read

set_option backward.isDefEq.respectTransparency false in
/-- Enrichment preserves each query class on the full all-reply adaptive program, including live reads and repeated calls. -/
theorem query_bound_iff {Result : Type} (client : OracleComp Spec Result)
    (predicate : RawCtxSelectedLiveCompiler.Spec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (simulateQ erase client).IsQueryBoundP predicate budget ↔
      client.IsQueryBoundP (fun query => predicate (originalQuery query)) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      rcases query with ((pending | opening) | ((pending | sealing) | externalRequest)) | read
      all_goals simp only [simulateQ_bind, simulateQ_spec_query, erase,
        RawCtxPendingOwnerQueries.erase, RawCtxSelectedLiveCompiler.primitiveForward,
        isQueryBoundP_query_bind_iff, originalQuery, RawCtxPendingOwnerQueries.originalQuery, ih]
      all_goals rfl

end BeaconcryptCore.Computational.RawCtxPendingLiveQueries

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveQueries.primitive_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveQueries.primitive_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveQueries.step_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveQueries.step_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveQueries.schedule_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveQueries.schedule_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveQueries.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveQueries.source_project

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingLiveQueries.query_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingLiveQueries.query_bound_iff
