import BeaconcryptCore.Computational.RawCtxSelectedParentOwner
import BeaconcryptCore.Computational.RawCtxGenericLiveRead

/-!
Complete retained-parent owner/public/live-read continuations preserve the actual owner, read history and shared primitive state. Both public interfaces use the real fixed-source backend. The label observer adds an exposure flag; its projection removes only that private ghost, since known byte aliases need not have the same flag as a hidden slot. Native reads retain their actual optional bytes and all observations. No input uniformity, reached-cut provenance or freshness conclusion is assumed or inferred here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open RawCtxSelectedLiveRead
open PqxdhJointKdfGame PqxdhSecretInputKdf

abbrev SourceSpec := RawCtxSelectedLiveTrace.SourceSpec
abbrev NativeState (Metadata : Type) (serverCount beaconCount : Nat) :=
  Owner RatchetChain Metadata × RawCtxProtocolReveals.History serverCount beaconCount
abbrev LabelState (Metadata : Type) (serverCount beaconCount : Nat) :=
  RawCtxGenericLiveRead.OuterState Slot Metadata serverCount beaconCount

def project {Metadata : Type} {serverCount beaconCount : Nat} (target : RootOutput)
    (state : LabelState Metadata serverCount beaconCount) : NativeState Metadata serverCount beaconCount :=
  (mapOwner target state.1.1, state.1.2)

noncomputable def nativeImpl {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) :
    QueryImpl SourceSpec (StateT (NativeState Metadata serverCount beaconCount)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :=
  fun query state => match query with
  | .inl request =>
      (fun result => (result.1, (result.2, RawCtxProtocolReveals.tick state.2))) <$>
        (nativeOwner source writer prior entry target sender decode request).run state.1
  | .inr read =>
      let reply := RawCtxGenericLiveRead.nativeReader read (some state.1.kernel)
      pure (reply, (state.1, RawCtxProtocolReveals.note (observation owner read reply) state.2))

noncomputable def labelImpl {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : RawCtxGenericLiveRead.Reader Slot) :
    QueryImpl SourceSpec (StateT (LabelState Metadata serverCount beaconCount)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :=
  fun query state => match query with
  | .inl request =>
      (fun result => (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$>
        (labelOwner source writer prior entry response sender decode request).run state.1.1
  | .inr read =>
      let reply := reader read (some state.1.1.kernel)
      pure (reply, ((state.1.1, RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
        state.2 || exposed read (some state.1.1.kernel)))

/-- Native byte lookup is the same original read after interpreting the private kernel, including absent slots. -/
theorem reader_map (target : RootOutput) (read : Read) (entry : Option (Kernel Slot)) :
    RawCtxGenericLiveRead.nativeReader read (entry.map (nativeKernel target)) =
      RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target) read entry := by
  cases entry <;> rfl

/-- One actual record/public/read operation retains its optional result, complete owner and native history; only the label exposure ghost is projected away. -/
theorem step_map {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (query : SourceSpec.Domain) (state : LabelState Metadata serverCount beaconCount) :
    (nativeImpl (Auxiliary := Auxiliary) source writer prior entry target sender decode owner query).run (project target state) =
      Prod.map id (project target) <$>
        (labelImpl source writer prior entry (childResponse prior entry target) sender decode owner
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) query).run state := by
  cases query with
  | inl request =>
    simp only [nativeImpl, labelImpl, project, StateT.run]
    have equation := RawCtxSelectedParentOwner.step_map (Auxiliary := Auxiliary) source writer prior entry target sender decode request state.1.1
    simp only [StateT.run] at equation
    rw [equation, Functor.map_map, Functor.map_map]
    rfl
  | inr read =>
    simp only [nativeImpl, labelImpl, project, StateT.run, map_pure]
    rfl

/-- The same full adaptive live client preserves all original history and shared effects through retained private lookup and real public evaluation. -/
theorem schedule_map {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (client : OracleComp SourceSpec Result) (state : LabelState Metadata serverCount beaconCount) :
    (simulateQ (nativeImpl (Auxiliary := Auxiliary) source writer prior entry target sender decode owner) client).run (project target state) =
      Prod.map id (project target) <$>
        (simulateQ (labelImpl source writer prior entry (childResponse prior entry target) sender decode owner
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target))) client).run state :=
  (map_run_simulateQ_eq_of_query_map_eq _ _ (project target)
    (fun query state => (step_map source writer prior entry target sender decode owner query state).symm)
    client state).symm

end BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.reader_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.reader_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.step_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.step_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLiveSource.schedule_map
