import BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath

/-!
The full actual post source retains the selected installed session's initialized send path and every successful selected-origin publication in its already executed private cache. Beacon finishes are tied to their actual prepared initializer coordinate. The invariant includes all earlier publications, so later callbacks and the final checker cannot supply missing source derivations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginPostPath
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialOriginPost PqxdhInitialOriginFinishPath RawCtxCursorLineage
variable {ι M P I D K X Response A N Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Front (M P I D K : Type) (S B : Nat) := PqxdhInitialPendingPost.Front RatchetChain M P I D K S B
abbrev State (A N : Type) := PqxdhInitialNativeLog.State A N RootOracle.QueryCache
abbrev Snapshot (M P I D K : Type) (S B : Nat) := Front M P I D K S B × Trace Bool S B

noncomputable def rootFor (serverRoot previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (selected : RawCtxProtocolReveals.Owner S B) : RootOutput :=
  match selected with
  | .server _ _ => serverRoot
  | .beacon _ => sendRoot previousRoot response

def Active (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (state : State A N) : Prop :=
  before.2.installed selected = some true → RawCtxSourceFamilyPath.Good root selected before.1.roles.1 state.1.1

def Invariant (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (state : State A N) : Prop :=
  Active root selected before state ∧ ∀ number, ((selected, number), true) ∈ before.2.published →
    RawCtxSourcePublishedPath.Cached root number state.1.1.2.1

private theorem active_mono (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (left right : State A N)
    (valid : Active root selected before left) (extension : Extends left.1.1.2.1 right.1.1.2.1) :
    Active root selected before right := by
  intro installed kernel present
  exact RawCtxSourceSendPath.path_extends root ⟨kernel⟩ _ _ (valid installed kernel present) extension

private theorem invariant_mono (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (left right : State A N)
    (valid : Invariant root selected before left) (extension : Extends left.1.1.2.1 right.1.1.2.1) :
    Invariant root selected before right :=
  ⟨active_mono root selected before left right valid.1 extension,
   fun number recorded => RawCtxSourcePublishedPath.cached_extends root number _ _ (valid.2 number recorded) extension⟩

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Snapshot M P I D K S B) :=
  simulateQ (PqxdhInitialNativeLog.handler source writer stage (withInitial source selected previousRoot response other))
    ((PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark source selected) sender route decode query).run before)


/-- Every actual successful or rejected finish preserves the installed-session path and all prior publications. -/
theorem finish_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (serverRoot : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : Snapshot M P I D K S B) (state : State A N)
    (valid : Invariant (rootFor serverRoot previousRoot response selected) selected before state)
    (result : (Option Pqxdh.Bytes × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode (.inr (.finish index raw)) before).run state)) :
    Invariant (rootFor serverRoot previousRoot response selected) selected result.1.2 result.2 := by
  have extension := PqxdhInitialNativePath.program_extends source writer stage
    (withInitial source selectedMessage previousRoot response other) _ state result supported
  change result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
    (withInitial source selectedMessage previousRoot response other)) (do
      let finished ← PqxdhInitialFinishOrigin.owner (PqxdhInitialSelectedOrigin.mark source selectedMessage)
        PqxdhInitialPendingPost.preForward PqxdhInitialPendingPost.calls PqxdhInitialPendingPost.applicationForward
        PqxdhInitialPendingPost.initialForward decode raw (before.1.roles.1.2 index)
      pure (finished.1.1, (PqxdhInitialPendingPost.install index before.1 finished.1.2,
        PqxdhInitialOriginPost.finish before.2 index finished.2)))).run state) at supported
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨finished, reached, rfl⟩ := supported
  constructor
  · intro marked kernel found
    cases selected with
    | server selectedIndex peer =>
      have old : before.2.installed (.server selectedIndex peer) = some true := by
        cases origin : finished.1.2 <;>
          simpa only [PqxdhInitialOriginPost.finish, origin, Function.update_of_ne (show (RawCtxProtocolReveals.Owner.server selectedIndex peer : RawCtxProtocolReveals.Owner S B) ≠ .beacon index by simp)] using marked
      exact RawCtxSourceSendPath.path_extends _ ⟨kernel⟩ _ _ (valid.1 old kernel found) extension
    | beacon selectedIndex =>
      by_cases same : selectedIndex = index
      · subst selectedIndex
        have current : beaconKernel finished.1.1.2 = some kernel := by
          change RawCtxGenericRoleFamily.selectedKernel (.beacon index)
            ((before.1.roles.1.1, Function.update before.1.roles.1.2 index finished.1.1.2)) = some kernel at found
          simp only [RawCtxGenericRoleFamily.selectedKernel, Function.update_self] at found
          cases phase : finished.1.1.2.beacon.phase <;> simp_all only [beaconKernel]
        cases origin : finished.1.2 with
        | none =>
          have old : before.2.installed (.beacon index) = some true := by
            simpa only [PqxdhInitialOriginPost.finish, origin] using marked
          have unchanged := unmarked_kernel _ _ decode raw (before.1.roles.1.2 index) state finished reached origin kernel current
          exact RawCtxSourceSendPath.path_extends _ ⟨kernel⟩ _ _ (valid.1 old kernel (by
            cases phase : (before.1.roles.1.2 index).beacon.phase <;>
              simpa only [RawCtxGenericRoleFamily.selectedKernel, beaconKernel, phase] using unchanged)) extension
        | some value =>
          have valueEq : value = true := by
            simpa only [PqxdhInitialOriginPost.finish, origin, Function.update_self, Option.some.injEq] using marked
          subst value
          obtain ⟨actual, present, path⟩ := marked_finish_path source writer stage selectedMessage previousRoot response
            other decode raw (before.1.roles.1.2 index) state finished reached origin
          have sameKernel : actual = kernel := Option.some.inj (present.symm.trans current)
          subst actual
          exact path
      · have old : before.2.installed (.beacon selectedIndex) = some true := by
          cases origin : finished.1.2 <;>
            simpa only [PqxdhInitialOriginPost.finish, origin,
              Function.update_of_ne (show (RawCtxProtocolReveals.Owner.beacon selectedIndex : RawCtxProtocolReveals.Owner S B) ≠ .beacon index by simpa using same)] using marked
        have unchanged : RawCtxGenericRoleFamily.selectedKernel (.beacon selectedIndex) before.1.roles.1 = some kernel := by
          simpa only [PqxdhInitialPendingPost.install, RawCtxGenericRoleFamily.selectedKernel,
            Function.update_of_ne same] using found
        exact RawCtxSourceSendPath.path_extends _ ⟨kernel⟩ _ _ (valid.1 old kernel unchanged) extension
  · intro number published
    have old : ((selected, number), true) ∈ before.2.published := by
      cases origin : finished.1.2 <;>
        simpa only [PqxdhInitialOriginPost.finish, origin] using published
    exact RawCtxSourcePublishedPath.cached_extends _ number _ _ (valid.2 number old) extension


/-- The actual record operation preserves the active source path and records only already derived successful selected-origin sends. -/
theorem records_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Snapshot M P I D K S B) (state : State A N)
    (valid : Invariant root selected before state)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode (.inl (.inl query)) before).run state)) :
    Invariant root selected result.1.2 result.2 := by
  have extension := PqxdhInitialNativePath.program_extends source writer stage
    (withInitial source selectedMessage previousRoot response other) _ state result supported
  change result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
    (withInitial source selectedMessage previousRoot response other)) (do
      let completed ← simulateQ PqxdhInitialPendingPost.liveForward
        ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run before.1.roles)
      pure (completed.1, ({ before.1 with roles := completed.2 },
        PqxdhInitialOriginPost.record before.2 query completed.1)))).run state) at supported
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨completed, reached, rfl⟩ := supported
  have preserved (marked : before.2.installed selected = some true) :=
    PqxdhInitialNativePath.records_path source writer stage (withInitial source selectedMessage previousRoot response other)
      root selected sender route decode query before.1.roles state (valid.1 marked) completed reached
  refine ⟨fun marked => (preserved marked).2.1, ?_⟩
  intro number published
  obtain old | ⟨actual, marked⟩ := (PqxdhInitialOriginPost.record_member before.2 query completed.1.1 (selected, number) true).mp published
  · exact RawCtxSourcePublishedPath.cached_extends root number _ _ (valid.2 number old) extension
  · exact (preserved marked).2.2 number actual

/-- Every complete original post operation preserves the same selected installation and publication invariant, including initializer failures and other owners' finishes. -/
theorem step_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (serverRoot : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Snapshot M P I D K S B) (state : State A N)
    (valid : Invariant (rootFor serverRoot previousRoot response selected) selected before state)
    (result : ((PqxdhInitialGenericPost.Spec extra S B).Range query × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode query before).run state)) :
    Invariant (rootFor serverRoot previousRoot response selected) selected result.1.2 result.2 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · exact records_invariant source writer stage selectedMessage previousRoot response other _ selected
      sender route decode query before state valid result supported
  · have extension := PqxdhInitialNativePath.program_extends source writer stage
      (withInitial source selectedMessage previousRoot response other) _ state result supported
    change result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
      (withInitial source selectedMessage previousRoot response other))
      ((fun reply => (reply, before)) <$> PqxdhInitialPendingPost.selectorForward query)).run state) at supported
    simp only [simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact invariant_mono _ selected before state completed.2 valid extension
  · exact finish_invariant source writer stage selectedMessage previousRoot response other serverRoot selected
      sender route decode index raw before state valid result supported

noncomputable def program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Snapshot M P I D K S B) :=
  simulateQ (PqxdhInitialNativeLog.handler source writer stage (withInitial source selectedMessage previousRoot response other))
    ((simulateQ (PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark source selectedMessage)
      sender route decode) client).run before)

/-- The whole original adaptive post client retains its selected-session path and pre-checker successful-publication cache, from the same full source prefix state. -/
theorem program_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (serverRoot : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Snapshot M P I D K S B) (state : State A N)
    (valid : Invariant (rootFor serverRoot previousRoot response selected) selected before state)
    (result : (Result × Snapshot M P I D K S B) × State A N)
    (supported : result ∈ support ((program source writer stage selectedMessage previousRoot response other
      sender route decode client before).run state)) :
    Invariant (rootFor serverRoot previousRoot response selected) selected result.1.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing before state with
  | pure value =>
    simp only [program, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | query_bind query next ih =>
    simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    exact ih completed.1.1 completed.1.2 completed.2
      (step_invariant source writer stage selectedMessage previousRoot response other serverRoot selected
        sender route decode query before state valid completed reached) rest

end BeaconcryptCore.Computational.PqxdhInitialOriginPostPath

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.finish_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.finish_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.records_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.records_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.step_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.step_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginPostPath.program_invariant
