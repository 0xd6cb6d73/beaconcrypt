import BeaconcryptCore.Computational.RawCtxSelectedLiveTrace

/-!
One selected established owner's original record operations, the actual public backend and actual live chain/skipped-key reads are recovered from the same selected trace by a complete state projection. The projection retains all native owner fields, every optional result, the full shared primitive state and the original read observations/timestamps. It removes only the private selected-slot representation and added candidate/exposure instrumentation; it does not fabricate another role state or replay operations.

The supplied target is interpreted using the existing fixed functional source response. The arbitrary adaptive equality is literal OracleComp equality, so every selective underlying query bound is preserved. Its exposure corollary retains the probability of the actual first hidden-current-chain read and does not assume this event unlikely. The selected-kernel representation and one fixed owner are explicit; the global reached-prefix law, first32/initial-prefix aliases, other owners, earlier root/ancestor knowledge and source-to-uniform hybrid remain separate. Snapshot, persistence and restoration services are excluded. Native library/error contracts remain those of the imported fixed-source implementation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveSource
open RawCtxSelectedChain RawCtxSelectedLiveRead RawCtxSelectedLiveTrace

abbrev NativeState (Metadata Auxiliary : Type) (serverCount beaconCount : Nat) :=
  (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) ×
    RawCtxProtocolReveals.History serverCount beaconCount

def project {Metadata Auxiliary : Type} {serverCount beaconCount : Nat} (target : RatchetChain)
    (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    NativeState Metadata Auxiliary serverCount beaconCount :=
  ((RawCtxChainOwner.nativeState (nativeKernel target) state.1.1.1, state.1.1.2.1), state.1.2)

noncomputable def sourceImpl {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (NativeState Metadata Auxiliary serverCount beaconCount) ProbComp) :=
  fun query state => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, (result.2, RawCtxProtocolReveals.tick state.2))) <$>
        (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer) sender decode request).run state.1
  | .inl (.inr request) => do
      let result ← ((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) request).run state.1.2
      pure (result.1, ((state.1.1, result.2), RawCtxProtocolReveals.tick state.2))
  | .inr read =>
      let reply := nativeRead read (some state.1.1.owner.kernel)
      pure (reply, (state.1, RawCtxProtocolReveals.note (observation owner read reply) state.2))

set_option backward.isDefEq.respectTransparency false in
/-- The full original fixed-source record/public/read step is recovered by removing only private slots and added candidate/exposure instrumentation. -/
theorem source_step {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (query : SourceSpec.Domain) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    (sourceImpl source writer sender decode owner query).run (project target state) =
      Prod.map id (project target) <$>
        (observedImpl source writer (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner (nativeReader target) query).run state := by
  rcases query with (request | request) | read
  case inl.inl =>
    have step := RawCtxSelectedTraceOwner.native_schedule source writer target sender decode
      (RawCtxMixedOwner.SourceSpec.query request) state.1.1
    simp only [simulateQ_spec_query] at step
    have lifted := congrArg (fun work => (fun result => (result.1, (result.2, RawCtxProtocolReveals.tick state.1.2))) <$> work) step
    simpa only [sourceImpl, observedImpl, RawCtxSelectedPublicTrace.sourceImpl, project,
      StateT.run, simulateQ_spec_query, Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
      SourceSpec, RawCtxSelectedPublicTrace.SourceSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim] using lifted
  case inl.inr =>
    have lifted := congrArg (fun work => (fun result => (result.1,
      ((RawCtxChainOwner.nativeState (nativeKernel target) state.1.1.1, result.2),
        RawCtxProtocolReveals.tick state.1.2))) <$> work)
      (RawCtxSelectedPublicTrace.public_erase source writer request state.1.1.2).symm
    simpa only [sourceImpl, observedImpl, RawCtxSelectedPublicTrace.sourceImpl, project,
      StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
      SourceSpec, RawCtxSelectedPublicTrace.SourceSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim] using lifted
  case inr =>
    simp only [sourceImpl, observedImpl, project, nativeReader, StateT.run, map_pure,
      Prod.map_def, id_eq, RawCtxChainOwner.nativeState, Option.map_some]

/-- The same arbitrary adaptive source continuation retains its entire native state and original read history. -/
theorem source_schedule {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount) :
    (simulateQ (sourceImpl source writer sender decode owner) client).run (project target state) =
      Prod.map id (project target) <$>
        (simulateQ (observedImpl source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner (nativeReader target)) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq _ _ (project target)
    (fun query state => (source_step source writer sender decode owner target query state).symm)
    client state).symm

/-- Erasing the added trace preserves every selective bound on the actual underlying uniform program. -/
theorem source_query_bounds {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : RawCtxSelectedLiveTrace.State Metadata Auxiliary serverCount beaconCount)
    (kind : unifSpec.Domain → Prop) [DecidablePred kind] (budget : Nat) :
    ((simulateQ (sourceImpl source writer sender decode owner) client).run (project target state)).IsQueryBoundP kind budget ↔
      ((simulateQ (observedImpl source writer
        (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
        sender decode owner (nativeReader target)) client).run state).IsQueryBoundP kind budget := by
  rw [source_schedule]
  exact isQueryBound_map_iff _ _ _ _ _

/-- The same original native source differs from masked live reads by at most its directly recorded exposure probability. This probability is retained, not assumed small. -/
theorem source_exposure_distance {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : BaseState Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (sourceImpl source writer sender decode owner) client).run (project target (state, false)))
      (Prod.map id (project target) <$>
        (simulateQ (observedImpl source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner labelRead) client).run (state, false)) ≤
      Pr{let result ← ((simulateQ (observedImpl source writer
          (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest target))
          sender decode owner (nativeReader target)) client).run (state, false))}[result.2.2 = true].toReal := by
  rw [source_schedule]
  exact (tvDist_map_le (Prod.map id (project target)) _ _).trans
    (exposure_distance source writer _ sender decode owner target client state)

end BeaconcryptCore.Computational.RawCtxSelectedLiveSource

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_exposure_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveSource.source_exposure_distance
