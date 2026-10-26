import BeaconcryptCore.Computational.PqxdhInitialNativeLog
import BeaconcryptCore.Computational.RawCtxSourcePublishedPath

/-!
The complete original pending interface preserves the actual private cache across all external effects. Its record operations use exactly the previously checked selective family source, retaining the additional private state and root cache. Executed send paths and successful publication paths are derived from that same supported source execution before any final lineage checker runs.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativePath
open PqxdhJointKdfGame PqxdhInitialNativeLog RawCtxCursorLineage PqxdhSecretInputKdf
variable {ι M P I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every actual full-interface callback preserves all prior private cache bindings, including callbacks outside the ratchet interface. -/
theorem step_extends (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) :
    Extends state.1.1.2.1 result.2.1.1.2.1 := by
  cases query with
  | inl query =>
    rw [live_handler] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨reply, actual, rfl⟩ := supported
    exact (RawCtxSelectiveReplay.logged source writer stage
      (((RawCtxPendingSelectiveFamily.Spec S B).query query) : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) _) state.1 reply
      (by simpa only [simulateQ_spec_query] using actual)).1
  | inr query =>
    rw [external_handler] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨reply, actual, rfl⟩ := supported
    exact fun _ _ known => known

/-- The same complete supported original source execution retains every earlier private binding before its final observer. -/
theorem program_extends (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result) (state : State A N C)
    (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external) client).run state)) :
    Extends state.1.1.2.1 result.2.1.1.2.1 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact fun _ _ known => known
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, head, tail⟩ := supported
    have first := step_extends source writer stage external query state reply head
    have later := ih reply.1 reply.2 result tail
    exact fun address output known => later address output (first address output known)

/-- The full recorded primitive schedule retains exactly the original logged LIVE execution and both additional ambient fields. -/
theorem live_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result) (state : State A N C) :
    (simulateQ (handler source writer stage external)
      (simulateQ PqxdhInitialPendingPost.liveForward client)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state.1) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, PqxdhInitialPendingPost.liveForward, StateT.run_bind,
      map_bind]
    rw [PqxdhInitialNativeLog.live_handler source writer stage external query state]
    simp only [bind_map_left]
    exact bind_congr fun reply => ih reply.1 (reply.2, state.2)

/-- Removing only ambient metadata from a complete record primitive execution gives the same actual selective source computation. -/
theorem live_projection (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result) (state : State A N C) :
    (fun result => (result.1, result.2.1.1)) <$>
      ((simulateQ (handler source writer stage external) (simulateQ PqxdhInitialPendingPost.liveForward client)).run state) =
      (simulateQ (RawCtxPendingSelectiveFamily.handler source writer stage) client).run state.1.1 := by
  rw [live_run]
  simpa only [Functor.map_map, Function.comp_def] using
    RawCtxSelectiveFamilyLog.program_projection source writer stage client state.1.1 state.1.2

noncomputable def records (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B) :=
  simulateQ (handler source writer stage external)
    (simulateQ PqxdhInitialPendingPost.liveForward
      ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry))

/-- An actual original record request is exactly the selective family source operation after projecting only its additional ambient metadata. -/
theorem records_projection (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B)
    (state : State A N C) :
    (fun result => (result.1, result.2.1.1)) <$>
      ((records source writer stage external sender route decode query entry).run state) =
      ((RawCtxSourceFamilyPath.impl source writer stage sender route decode query).run entry).run state.1.1 := by
  rw [records, live_projection]
  have actual := congrArg (fun work => work.run state.1.1)
    (RawCtxPendingFamilyNative.program_interpretation (RawCtxPendingSelectiveFamily.backend source writer stage)
      sender route decode (((RawCtxProtocolReveals.SourceSpec S B).query query) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) entry)
  simpa only [RawCtxPendingFamilyLiveTails.program, simulateQ_spec_query,
    RawCtxPendingSelectiveFamily.handler, RawCtxSourceFamilyPath.impl, RawCtxSourceSendPath.native] using actual

/-- The same actual full-state record reply preserves the initialized sender path and places every newly published target in the already executed private cache. -/
theorem records_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B)
    (state : State A N C) (valid : RawCtxSourceFamilyPath.Good root selected entry.1 state.1.1)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxSourceFamilyPath.LiveState M P I D K S B) × State A N C)
    (supported : result ∈ support ((records source writer stage external sender route decode query entry).run state)) :
    Extends state.1.1.2.1 result.2.1.1.2.1 ∧
      RawCtxSourceFamilyPath.Good root selected result.1.2.1 result.2.1.1 ∧
      ∀ number, (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1 →
        RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1 := by
  have actual : (result.1, result.2.1.1) ∈ support
      (((RawCtxSourceFamilyPath.impl source writer stage sender route decode query).run entry).run state.1.1) := by
    rw [← records_projection source writer stage external sender route decode query entry state, support_map]
    exact ⟨result, supported, rfl⟩
  have kept := RawCtxSourceFamilyPath.step source writer stage root selected sender route decode query entry state.1.1
    valid (result.1, result.2.1.1) actual
  exact ⟨kept.1, kept.2, fun number recorded => RawCtxSourcePublishedPath.step source writer stage root selected number
    sender route decode query entry state.1.1 valid (result.1, result.2.1.1) actual recorded⟩

/-- A whole pending owner primitive program has the same source projection, with all private callback responses and effects retained. -/
theorem primitive_projection (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain) Result) (state : State A N C) :
    (fun result => (result.1, result.2.1.1)) <$>
      ((simulateQ (handler (S := S) (B := B) source writer stage external)
        (simulateQ PqxdhInitialPendingPost.primitiveForward client)).run state) =
      (simulateQ (RawCtxPendingNativeCalls.pending (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)) client).run state.1.1 := by
  have forwards : (PqxdhInitialPendingPost.liveForward : QueryImpl (RawCtxPendingSelectiveFamily.Spec S B)
      (OracleComp (Spec extra RatchetChain I D K X Response Shared S B))) ∘ₛ RawCtxPendingFamilyLiveQueries.primitiveForward =
      PqxdhInitialPendingPost.primitiveForward := by
    funext query
    simp [QueryImpl.compose, PqxdhInitialPendingPost.liveForward, RawCtxPendingFamilyLiveQueries.primitiveForward,
      PqxdhInitialPendingPost.primitiveForward, OracleSpec.query]
  rw [← forwards, QueryImpl.simulateQ_compose, live_projection]
  simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
    ← QueryImpl.simulateQ_compose, RawCtxPendingFamilyLiveQueries.primitive_handler, RawCtxSourceSendPath.native]
private theorem actual_rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (root : RootOutput) :
    RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native (A := A) source writer stage))
      (fun before after => Extends before.2.1 after.2.1)
      (fun kernel state => RawCtxSourceSendPath.Path root ⟨kernel⟩ state.2.1) where
  refl := fun _ _ _ known => known
  trans := fun _ _ _ first later _ _ known => later _ _ (first _ _ known)
  mono := fun kernel _ _ extension valid => RawCtxSourceSendPath.path_extends root ⟨kernel⟩ _ _ valid extension
  receive := fun entry target context state result supported =>
    let checked := RawCtxSourcePathCalls.receive_call source writer stage entry target context state result supported
    ⟨checked.1, checked.2 root⟩
  send := fun entry context state result supported =>
    let checked := RawCtxSourcePathCalls.send_call source writer stage entry context state result supported
    ⟨checked.1, checked.2 root⟩


/-- The actual complete first raw receive preserves its initialized sender path, including malformed, rejected and failed-opening outcomes. -/
theorem raw_path {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (root : RootOutput) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) Metadata)
    (state : State A N C) (valid : RawCtxSourceSendPath.Path root ⟨entry.kernel⟩ state.1.1.2.1)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State (RawCtxPendingOwnerQueries.Kernel RatchetChain) Metadata) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      ((RawCtxChainOwner.rawReceive PqxdhInitialPendingPost.calls decode raw).run entry)).run state)) :
    Extends state.1.1.2.1 result.2.1.1.2.1 ∧ RawCtxSourceSendPath.Path root ⟨result.1.2.kernel⟩ result.2.1.1.2.1 := by
  have projected : (result.1, result.2.1.1) ∈ support
      ((simulateQ (RawCtxPendingNativeCalls.pending (RawCtxSourceSendPath.native source writer stage)
        (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift))
          ((RawCtxChainOwner.rawReceive RawCtxPendingOwnerQueries.calls decode raw).run entry)).run state.1.1) := by
    rw [← primitive_projection source writer stage external _ state, support_map]
    refine ⟨result, ?_, rfl⟩
    simpa only [PqxdhInitialPendingPost.calls, RawCtxGenericOwnerInterpretation.raw_interpretation] using supported
  rw [RawCtxGenericOwnerInterpretation.raw_interpretation, RawCtxPendingNativeCalls.calls_interpretation] at projected
  have preserved := RawCtxFamilyStateInvariant.raw _ _ _ (actual_rules source writer stage root)
    decode raw entry state.1.1 (result.1, result.2.1.1) projected
  exact ⟨preserved.1, preserved.2 valid⟩

end BeaconcryptCore.Computational.PqxdhInitialNativePath

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.step_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.step_extends

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.program_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.program_extends

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.live_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.live_run

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.live_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.live_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.records_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.records_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.records_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.records_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.primitive_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.primitive_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativePath.raw_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativePath.raw_path
