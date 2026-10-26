import BeaconcryptCore.Computational.PqxdhInitialCounterBudget

/-!
The complete original first Server builder and adaptive post establish selected-origin sender counters from actual zero-state initial constructors. Matching Beacon finishes retain their exact source coordinate and first receive. Sends advance only after their real private callback is logged, while receives preserve sender fields. Successful publications therefore have positions bounded by the original source callback allowance, even when cached chains cycle. The final finite-sum law retains any chosen same final source event and charges adaptive publication-position selection explicitly.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialCounterPublication
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialNativeLog PqxdhInitialPendingPost PqxdhInitialOriginFinishPath
variable {ι Chain M P I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem opening_kernel (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : KernelOf Chain)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : PqxdhInitialGenericBeacon.Staged (KernelOf Chain))
    (found : PqxdhInitialGenericBeacon.afterOpening candidate kernel reply = some staged) : staged.kernel = kernel := by
  cases reply with
  | none => cases found
  | some opened =>
    simp only [PqxdhInitialGenericBeacon.afterOpening] at found
    split at found
    · cases found
    · split at found
      · split at found
        · cases found
        · cases found; rfl
      · cases found


private theorem finish_some (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K)
    (staged : Option (PqxdhInitialGenericBeacon.Staged (KernelOf Chain))) :
    (beaconKernel (PqxdhInitialGenericBeacon.finish control before staged).2).isSome =
      (PqxdhInitialGenericBeacon.finish control before staged).1.isSome := by
  cases staged with
  | none => rfl
  | some staged =>
    simp only [PqxdhInitialGenericBeacon.finish]
    split
    · rfl
    · split <;> rfl

/-- Every actual first receive retains the zero-initialized counter bound. -/
theorem after_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : KernelOf RatchetChain)
    (state : State A N C) (valid : kernel.control.send_sequence.val ≤ state.1.2.length)
    (result : Option (PqxdhInitialGenericBeacon.Staged (KernelOf RatchetChain)) × State A N C)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage external)
      (PqxdhInitialGenericBeacon.afterInitial calls applicationForward decode pending kernel)).run state)) :
    ∀ staged, result.1 = some staged → staged.kernel.control.send_sequence.val ≤ result.2.1.2.length := by
  simp only [PqxdhInitialGenericBeacon.afterInitial, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨application, first, rest⟩ := supported
  have extension := PqxdhInitialCounterBudget.program_mono source writer stage external (applicationForward pending.response)
    state application first
  have valid' := valid.trans extension
  cases found : application.1 with
  | none =>
    simp only [found, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at rest
    subst result
    intro staged impossible
    cases impossible
  | some raw =>
    simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨received, actual, finished⟩ := rest
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at finished
    subst result
    have preserved := PqxdhInitialCounterBudget.raw_counter source writer stage external decode raw
      (PqxdhInitialGenericBeacon.localOwner (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernel)
      application.2 valid' received actual
    intro staged produced
    rw [opening_kernel _ _ _ staged produced]
    exact preserved


/-- A matching source initializer returns a kernel with counter zero before the complete first receive. -/
theorem selected_tail_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared)
    (chosen : PqxdhInitialSelectedOrigin.mark source selected pending.root = true)
    (state : State A N RootOracle.QueryCache)
    (result : Option (PqxdhInitialGenericBeacon.Staged (KernelOf RatchetChain)) × State A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialGenericBeacon.tail calls applicationForward initialForward decode pending)).run state)) :
    ∀ staged, result.1 = some staged →
      staged.kernel.control.send_sequence.val ≤ result.2.1.2.length := by
  simp only [PqxdhInitialGenericBeacon.tail, simulateQ_bind, StateT.run_bind] at supported
  rw [initial_selected source writer stage selected previousRoot response other pending.root chosen state] at supported
  simp only [pure_bind] at supported
  exact after_counter source writer stage (withInitial source selected previousRoot response other)
    decode pending _ state (by rw [PqxdhInitialNativeInitializer.kernel_send_zero source]; exact Nat.zero_le _) result supported


/-- A successful selected-origin finish installs a kernel bounded by the same actual private-call log. -/
theorem marked_finish_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (KernelOf RatchetChain) I D K)
    (state : State A N RootOracle.QueryCache)
    (result : PqxdhInitialFinishOrigin.Result (KernelOf RatchetChain) Bool I D K × State A N RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialFinishOrigin.owner (PqxdhInitialSelectedOrigin.mark source selected)
        preForward calls applicationForward initialForward decode raw entry)).run state))
    (marked : result.1.2 = some true) :
    ∃ kernel, beaconKernel result.1.1.2 = some kernel ∧
      kernel.control.send_sequence.val ≤ result.2.1.2.length := by
  rw [PqxdhInitialOriginPost.owner_interpretation] at supported
  obtain ⟨control, prekey, oneTime, kem, prepared, atTail, staged, phase, preparation, tail, finished, success, chosen⟩ :=
    PqxdhInitialFinishOrigin.origin (PqxdhInitialSelectedOrigin.mark source selected) _ _ _ _ decode raw entry state result supported true marked
  have actualTail : (staged, result.2) ∈ support ((simulateQ (handler (S := S) (B := B) source writer stage
      (withInitial source selected previousRoot response other))
      (PqxdhInitialGenericBeacon.tail calls applicationForward initialForward decode prepared)).run atTail) := by
    rw [PqxdhInitialPendingPost.tail_interpretation]
    exact tail
  have paths := selected_tail_counter source writer stage selected previousRoot response other decode prepared chosen.symm
    atTail (staged, result.2) actualTail
  have present : (beaconKernel (PqxdhInitialGenericBeacon.finish control entry staged).2).isSome = true := by
    rw [finish_some, ← finished]
    exact success
  cases found : beaconKernel (PqxdhInitialGenericBeacon.finish control entry staged).2 with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some kernel =>
    obtain ⟨actual, produced, same, _⟩ := finish_kernel control entry staged kernel found
    refine ⟨kernel, ?_, ?_⟩
    · rw [finished]
      exact found
    · simpa only [same] using paths actual produced

def Good (selected : RawCtxProtocolReveals.Owner S B)
    (roles : RawCtxGenericRoleFamily.Roles (RawCtxPendingOwnerQueries.Kernel RatchetChain) M P I D K S B)
    (state : State A N C) : Prop :=
  ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected roles = some kernel →
    kernel.control.send_sequence.val ≤ state.1.2.length

/-- The exact original LIVE record step preserves the selected sender counter and bounds any successful publication by the executed private-call log. -/
theorem records_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B)
    (state : State A N C) (valid : Good selected entry.1 state)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxSourceFamilyPath.LiveState M P I D K S B) × State A N C)
    (supported : result ∈ support ((PqxdhInitialNativePath.records source writer stage external sender route decode query entry).run state)) :
    Good selected result.1.2.1 result.2 ∧
      ∀ number, (selected, number) ∈ RawCtxPublishedRecords.record query result.1.1 → number.val ≤ result.2.1.2.length := by
  let primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec RatchetChain) (StateT (State A N C) ProbComp) :=
    handler (S := S) (B := B) source writer stage external ∘ₛ PqxdhInitialPendingPost.primitiveForward
  let reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (RawCtxPendingOwnerQueries.Kernel RatchetChain) S B)
      (StateT (State A N C) ProbComp) := fun request => handler source writer stage external (.inl (.inr request))
  have forwarding : handler source writer stage external ∘ₛ PqxdhInitialPendingPost.liveForward =
      RawCtxPendingFamilyLiveQueries.handler primitive reader := by
    funext request
    cases request <;> simp [QueryImpl.compose, PqxdhInitialPendingPost.liveForward,
      PqxdhInitialPendingPost.primitiveForward, RawCtxPendingFamilyLiveQueries.handler, primitive, reader, OracleSpec.query]
  have interpreted := supported
  rw [PqxdhInitialNativePath.records, ← QueryImpl.simulateQ_compose, forwarding,
    RawCtxPendingFamilyLiveQueries.step_interpretation] at interpreted
  have laws : RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
      (fun before after => before.1.2.length ≤ after.1.2.length)
      (fun kernel state => kernel.control.send_sequence.val ≤ state.1.2.length) := by
    simpa only [PqxdhInitialCounterBudget.calls, PqxdhInitialPendingPost.calls,
      RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, primitive] using
        PqxdhInitialCounterBudget.rules (S := S) (B := B) source writer stage external
  have preserved := RawCtxFamilyStateInvariant.live _ _ _ laws _
    (fun request before after reached => PqxdhInitialCounterBudget.program_mono source writer stage external
      (simulateQ PqxdhInitialPendingPost.primitiveForward (RawCtxPendingOwnerQueries.publicForward request)) before after
      (by simpa only [primitive, QueryImpl.simulateQ_compose] using reached))
    reader (fun request before after reached => (PqxdhInitialCounterBudget.step_length source writer stage external
      (.inl (.inr request)) before after reached).1)
    sender route decode query entry state result interpreted selected
  have kept : Good selected result.1.2.1 result.2 := preserved.2 valid
  refine ⟨kept, ?_⟩
  intro number recorded
  have projected : (result.1, result.2.1.1) ∈ support
      (((RawCtxSourceFamilyPath.impl source writer stage sender route decode query).run entry).run state.1.1) := by
    rw [← PqxdhInitialNativePath.records_projection source writer stage external sender route decode query entry state, support_map]
    exact ⟨result, supported, rfl⟩
  obtain ⟨kernel, found, numberEq⟩ := RawCtxPublishedKernel.live
    (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native source writer stage))
    (fun kernel => kernel.control.send_sequence) (RawCtxSourcePathCalls.published_call source writer stage)
    (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
    sender route decode query entry state.1.1 (result.1, result.2.1.1) projected selected number recorded
  simpa only [numberEq] using kept kernel found

abbrev Front (M P I D K : Type) (S B : Nat) := PqxdhInitialPendingPost.Front RatchetChain M P I D K S B
abbrev Snapshot (M P I D K : Type) (S B : Nat) := Front M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B
abbrev SourceState (A N : Type) := PqxdhInitialNativeLog.State A N RootOracle.QueryCache
open PqxdhInitialOriginPost
def Active (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (state : SourceState A N) : Prop :=
  before.2.installed selected = some true → Good selected before.1.roles.1 state

def Invariant (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (state : SourceState A N) : Prop :=
  Active selected before state ∧ ∀ number, ((selected, number), true) ∈ before.2.published →
    number.val ≤ state.1.2.length

private theorem active_mono (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (left right : SourceState A N)
    (valid : Active selected before left) (extension : left.1.2.length ≤ right.1.2.length) :
    Active selected before right := by
  intro installed kernel present
  exact (valid installed kernel present).trans extension

private theorem invariant_mono (selected : RawCtxProtocolReveals.Owner S B)
    (before : Snapshot M P I D K S B) (left right : SourceState A N)
    (valid : Invariant selected before left) (extension : left.1.2.length ≤ right.1.2.length) :
    Invariant selected before right :=
  ⟨active_mono selected before left right valid.1 extension,
   fun number recorded => (valid.2 number recorded).trans extension⟩

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Snapshot M P I D K S B) :=
  simulateQ (PqxdhInitialNativeLog.handler source writer stage (withInitial source selected previousRoot response other))
    ((PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark source selected) sender route decode query).run before)


/-- Every actual successful or rejected finish preserves the installed-session counter bound and all prior publications. -/
theorem finish_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : Snapshot M P I D K S B) (state : SourceState A N)
    (valid : Invariant selected before state)
    (result : (Option Pqxdh.Bytes × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode (.inr (.finish index raw)) before).run state)) :
    Invariant selected result.1.2 result.2 := by
  have extension := PqxdhInitialCounterBudget.program_mono source writer stage
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
      exact (valid.1 old kernel found).trans extension
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
          exact (valid.1 old kernel (by
            cases phase : (before.1.roles.1.2 index).beacon.phase <;>
              simpa only [RawCtxGenericRoleFamily.selectedKernel, beaconKernel, phase] using unchanged)).trans extension
        | some value =>
          have valueEq : value = true := by
            simpa only [PqxdhInitialOriginPost.finish, origin, Function.update_self, Option.some.injEq] using marked
          subst value
          obtain ⟨actual, present, path⟩ := marked_finish_counter source writer stage selectedMessage previousRoot response
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
        exact (valid.1 old kernel unchanged).trans extension
  · intro number published
    have old : ((selected, number), true) ∈ before.2.published := by
      cases origin : finished.1.2 <;>
        simpa only [PqxdhInitialOriginPost.finish, origin] using published
    exact (valid.2 number old).trans extension


/-- The actual record operation preserves the active sender-counter bound and records only already derived successful selected-origin sends. -/
theorem records_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : Snapshot M P I D K S B) (state : SourceState A N)
    (valid : Invariant selected before state)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode (.inl (.inl query)) before).run state)) :
    Invariant selected result.1.2 result.2 := by
  have extension := PqxdhInitialCounterBudget.program_mono source writer stage
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
    records_counter source writer stage (withInitial source selectedMessage previousRoot response other)
      selected sender route decode query before.1.roles state (valid.1 marked) completed reached
  refine ⟨fun marked => (preserved marked).1, ?_⟩
  intro number published
  obtain old | ⟨actual, marked⟩ := (PqxdhInitialOriginPost.record_member before.2 query completed.1.1 (selected, number) true).mp published
  · exact (valid.2 number old).trans extension
  · exact (preserved marked).2 number actual

/-- Every complete original post operation preserves the same selected installation and publication invariant, including initializer failures and other owners' finishes. -/
theorem step_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Snapshot M P I D K S B) (state : SourceState A N)
    (valid : Invariant selected before state)
    (result : ((PqxdhInitialGenericPost.Spec extra S B).Range query × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((impl source writer stage selectedMessage previousRoot response other
      sender route decode query before).run state)) :
    Invariant selected result.1.2 result.2 := by
  rcases query with (query | query) | ⟨index, raw⟩
  · exact records_invariant source writer stage selectedMessage previousRoot response other selected
      sender route decode query before state valid result supported
  · have extension := PqxdhInitialCounterBudget.program_mono source writer stage
      (withInitial source selectedMessage previousRoot response other) _ state result supported
    change result ∈ support ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
      (withInitial source selectedMessage previousRoot response other))
      ((fun reply => (reply, before)) <$> PqxdhInitialPendingPost.selectorForward query)).run state) at supported
    simp only [simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨completed, reached, rfl⟩ := supported
    exact invariant_mono selected before state completed.2 valid extension
  · exact finish_invariant source writer stage selectedMessage previousRoot response other selected
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

/-- The whole original adaptive post client retains its selected-session counter and successful-publication bounds, from the same full source prefix state. -/
theorem program_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Snapshot M P I D K S B) (state : SourceState A N)
    (valid : Invariant selected before state)
    (result : (Result × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((program source writer stage selectedMessage previousRoot response other
      sender route decode client before).run state)) :
    Invariant selected result.1.2 result.2 := by
  induction client using OracleComp.inductionOn generalizing before state with
  | pure value =>
    simp only [program, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact valid
  | query_bind query next ih =>
    simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    exact ih completed.1.1 completed.1.2 completed.2
      (step_invariant source writer stage selectedMessage previousRoot response other selected
        sender route decode query before state valid completed reached) rest


abbrev BuildState (M P : Type) :=
  PqxdhInitialGenericPublication.State (KernelOf RatchetChain) M P (List Pqxdh.Bytes)

/-- Successful serialization publishes the same advanced sender whose counter is bounded by the actual source log. -/
private theorem builder_after_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : KernelOf RatchetChain) (metadata : P) (before : BuildState M P)
    (state : PqxdhInitialNativeLog.State A N C)
    (result : (Option PqxdhServerRegistrationPublication.Response × BuildState M P) × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage external)
      (PqxdhInitialGenericPublication.afterInitialization (PqxdhInitialPendingPost.calls (S := S) (B := B))
        auxForward candidate authenticated entry metadata before)).run state))
    (valid : entry.control.send_sequence.val ≤ state.1.2.length)
    (response : PqxdhServerRegistrationPublication.Response) (returned : result.1.1 = some response) :
    ∃ peer, result.1.2.server.peers response.keyId = some peer ∧
      peer.kernel.control.send_sequence.val ≤ result.2.1.2.length := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sentSupport, erased, erasedSupport, rest⟩ := supported
  have sentPath := PqxdhInitialCounterBudget.send_counter source writer stage external entry _ state valid sent sentSupport
  have erasedPath := sentPath.trans
    (PqxdhInitialCounterBudget.program_mono source writer stage external _ sent.2 erased erasedSupport)
  cases encrypted : sent.1.2 <;> simp only [encrypted, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
  · cases rest
    cases returned
  · obtain ⟨written, writtenSupport, rest⟩ := rest
    have writtenPath := erasedPath.trans
      (PqxdhInitialCounterBudget.program_mono source writer stage external _ erased.2 written writtenSupport)
    cases serialized : written.1 <;> simp only [serialized, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at rest
    all_goals (cases rest; simp only [Option.some.injEq] at returned)
    all_goals cases returned
    exact ⟨⟨candidate.beacon_identity_public_key, sent.1.1, metadata⟩,
      Function.update_self _ _ _, writtenPath⟩

/-- Every admitted builder candidate publishes a bounded sender counter; rejected allocation, identity, application and Rust branches remain unsuccessful. -/
private theorem builder_candidate_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : P) (before : BuildState M P)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response) (updated : BuildState M P)
    (supported : (ok (some response, updated), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        (PqxdhInitialGenericBuilder.candidate (PqxdhInitialPendingPost.calls (S := S) (B := B))
          auxForward initial candidate data metadata before)).run state))
    (initialZero : ∀ entry, initial = ok entry → entry.control.send_sequence.val = 0) :
    ∃ peer, updated.server.peers response.keyId = some peer ∧ peer.kernel.control.send_sequence.val ≤ afterState.1.2.length := by
  simp only [PqxdhInitialGenericBuilder.candidate, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterCheck⟩, _, supported⟩ := supported
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported
  cases initialEq : initial <;> simp only [initialEq, PqxdhInitialGenericBuilder.continueRust,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨allocated, afterAllocation⟩, _, supported⟩ := supported
  cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported
  cases binding : candidate.key_id_binding <;> simp only [binding, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and, simulateQ_map, StateT.run_map,
    support_map] at supported
  obtain ⟨⟨⟨reply, output⟩, finalState⟩, actual, same⟩ := supported
  simp only [Prod.mk.injEq, RustM.ok.injEq] at same
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
  exact builder_after_counter source writer stage external candidate _ _ metadata before afterAllocation
    _ actual (by rw [initialZero _ initialEq]; exact Nat.zero_le _) response rfl

/-- Current key allocation and Ready preparation preserve the source-backed successful publication counter. -/
private theorem builder_ready_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P) (before : BuildState M P)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response) (updated : BuildState M P)
    (supported : (ok (some response, updated), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        (PqxdhInitialGenericBuilder.readyBuild source (PqxdhInitialPendingPost.calls (S := S) (B := B))
          auxForward initial binding ready metadata before)).run state))
    (initialZero : ∀ entry, initial = ok entry → entry.control.send_sequence.val = 0) :
    ∃ peer, updated.server.peers response.keyId = some peer ∧ peer.kernel.control.send_sequence.val ≤ afterState.1.2.length := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild at supported
  cases next : pqxdh.server_next_key_id before.control <;> simp only [next,
    PqxdhInitialGenericBuilder.continueRust, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, reduceCtorEq, false_and] at supported
  rename_i nextResult
  cases nextResult <;> simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, reduceCtorEq, false_and] at supported
  split at supported <;> try simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  exact builder_candidate_counter source writer stage external initial _ ready.application metadata before
    state afterState response updated supported initialZero

/-- The complete source builder installs a peer with its actual first-send counter bounded by the full source log. -/
private theorem builder_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (initial : RustM (KernelOf RatchetChain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : PqxdhInitialPendingPost.Front RatchetChain M P I D K S B)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((ok (some response), after), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        ((PqxdhInitialPendingBuilder.build source initial sender index metadata ready).run before)).run state))
    (initialZero : ∀ entry, initial = ok entry → entry.control.send_sequence.val = 0) :
    ∃ peer, (after.roles.1.1 index).server.peers response.keyId = some peer ∧
      peer.kernel.control.send_sequence.val ≤ afterState.1.2.length := by
  change ((ok (some response), after), afterState) ∈ support
    ((simulateQ (handler source writer stage external)
      (PqxdhInitialPendingBuilder.reinstall index (PqxdhInitialPendingBuilder.consume index ready before) <$>
        PqxdhInitialGenericBuilder.readyBuild source PqxdhInitialPendingPost.calls auxForward initial
          ⟨(PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)).server.identity,
            (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)).identityKeyId⟩
          ready metadata (PqxdhInitialPendingBuilder.selected sender index (PqxdhInitialPendingBuilder.consume index ready before)))).run state) at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, finalState⟩, actual, same⟩ := supported
  cases reply <;> simp only [PqxdhInitialPendingBuilder.reinstall, Prod.mk.injEq,
    reduceCtorEq, false_and, RustM.ok.injEq] at same
  rename_i built
  rcases built with ⟨reply, updated⟩
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
  simpa only [PqxdhInitialPendingBuilder.install, Function.update_self] using
    builder_ready_counter source writer stage external initial _ ready metadata _ state finalState
      response updated actual initialZero

private theorem supplied_zero (source : FixedHkdfSha512NoSaltSource)
    (supplied : pqxdh.concrete.InitialRatchetKdfResponse) (entry : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false supplied = ok entry) :
    entry.refined.control.send_sequence.val = 0 := by
  obtain ⟨_, _, _, server, _, created, _, _, _, refined⟩ :=
    PqxdhInitialSuppliedPositions.pair_refines source.crypto supplied
  have same : server = entry := RustM.ok.inj (created.symm.trans initialized)
  subst entry
  rw [refined.sendSequence]

/-- An actual supplied64 Server build derives its initialized zero counter and publishes only an already derived sender state; no caller path premise remains. -/
private theorem supplied_build_counter (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (supplied : pqxdh.concrete.InitialRatchetKdfResponse) (entry : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false supplied = ok entry)
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : PqxdhInitialPendingPost.Front RatchetChain M P I D K S B)
    (state afterState : PqxdhInitialNativeLog.State A N C)
    (response : PqxdhServerRegistrationPublication.Response)
    (supported : ((ok (some response), after), afterState) ∈ support
      ((simulateQ (handler source writer stage external)
        ((PqxdhInitialPendingBuilder.build source
          ((fun kernel : ConcreteRatchetKernel => kernel.refined) <$> PqxdhInitialReplyErasure.kernelOf false supplied)
          sender index metadata ready).run before)).run state)) :
    ∃ peer, (after.roles.1.1 index).server.peers response.keyId = some peer ∧
      peer.kernel.control.send_sequence.val ≤ afterState.1.2.length := by
  apply builder_counter source writer stage external _ sender index metadata ready before after state afterState response supported
  intro kernel returned
  rw [initialized, RawCtxMaterialInterpretation.rust_map_ok] at returned
  cases RustM.ok.inj returned
  exact supplied_zero source supplied entry initialized


open PqxdhInitialSourcePublication (empty)

/-- An uninstrumented original family starts with no asserted selected installation or publication. -/
private theorem empty_invariant (selected : RawCtxProtocolReveals.Owner S B)
    (before : Front M P I D K S B) (state : SourceState A N) : Invariant selected (before, empty) state := by
  constructor
  · intro installed
    cases installed
  · intro number recorded
    exact False.elim (List.not_mem_nil recorded)

/-- The complete actual first builder supplies the installed-session and publication counter bounds from the same initial64 constructor. -/
private theorem builder_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before after : Front M P I D K S B)
    (state afterState : SourceState A N) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (supported : ((reply, after), afterState) ∈ support
      ((simulateQ (PqxdhInitialNativeLog.handler source writer stage
        (withInitial source selectedMessage previousRoot response64 other))
        ((PqxdhInitialPendingBuilder.build source
          (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
          sender index metadata ready).run before)).run state)) :
    Invariant selected (after, PqxdhInitialOriginPost.afterBuilder empty after index true reply) afterState := by
  cases reply with
  | fail error => exact empty_invariant selected after afterState
  | div => exact empty_invariant selected after afterState
  | ok reply =>
    cases reply with
    | none => exact empty_invariant selected after afterState
    | some response =>
      cases found : (after.roles.1.1 index).server.peers response.keyId with
      | none =>
        simpa only [PqxdhInitialOriginPost.afterBuilder, found] using empty_invariant selected after afterState
      | some peer =>
        obtain ⟨actualPeer, actualPresent, path⟩ := supplied_build_counter source writer stage
          (withInitial source selectedMessage previousRoot response64 other) response64 entry initialized sender index metadata ready
          before after state afterState response supported
        have samePeer : actualPeer = peer := Option.some.inj (actualPresent.symm.trans found)
        subst actualPeer
        constructor
        · intro installed kernel present
          by_cases same : selected = .server index response.keyId
          · subst selected
            simp only [RawCtxGenericRoleFamily.selectedKernel, found, Option.map_some, Option.some.injEq] at present
            subst kernel
            exact path
          · simp only [PqxdhInitialOriginPost.afterBuilder, found, Function.update_of_ne same, empty] at installed
            cases installed
        · intro number recorded
          obtain ⟨actualResponse, actualPeer, sameReply, present, publication, origin⟩ :=
            PqxdhInitialOriginPost.builder_recorded empty after index true (.ok (some response)) (selected, number) true recorded
              (by simp [empty])
          have sameResponse : actualResponse = response := by cases sameReply; rfl
          subst actualResponse
          have samePeer : actualPeer = peer := Option.some.inj (present.symm.trans found)
          subst actualPeer
          have owner := congrArg Prod.fst publication
          have numberEq := congrArg Prod.snd publication
          simp only at owner numberEq
          subst selected
          subst number
          exact path


noncomputable def sequence (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front M P I D K S B) : StateT (SourceState A N) ProbComp (Result × Snapshot M P I D K S B) :=
  simulateQ (PqxdhInitialNativeLog.handler source writer stage
    (withInitial source selectedMessage previousRoot response64 other))
    ((PqxdhInitialOriginPost.sequence source
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
      (PqxdhInitialSelectedOrigin.mark source selectedMessage) true sender route decode index metadata ready post).run (before, empty))

/-- The actual constructor, complete first builder and original adaptive post establish the source publication invariant from an empty trace, with no incoming counter-bound premise. -/
theorem sequence_invariant (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front M P I D K S B) (state : SourceState A N)
    (result : (Result × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((sequence source writer stage selectedMessage previousRoot response64 other
      sender route decode index metadata ready post before).run state)) :
    Invariant selected result.1.2 result.2 := by
  change result ∈ support ((simulateQ
    (PqxdhInitialNativeLog.handler source writer stage (withInitial source selectedMessage previousRoot response64 other)) (do
      let built ← (PqxdhInitialPendingBuilder.build source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64) sender index metadata ready).run before
      (simulateQ (PqxdhInitialOriginPost.compiler (PqxdhInitialSelectedOrigin.mark source selectedMessage)
        sender route decode) (post built.1)).run
        (built.2, PqxdhInitialOriginPost.afterBuilder empty built.2 index true built.1))).run state) at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨built, reached, rest⟩ := supported
  exact program_invariant source writer stage selectedMessage previousRoot response64 other
    selected sender route decode (post built.1.1) _ built.2
    (builder_invariant source writer stage selectedMessage previousRoot response64 other entry initialized selected
      sender index metadata ready before built.1.2 state built.2 built.1.1 reached) result rest


/-- Every selected-origin record published by the complete original source has a finite position bounded by its actual initialized send counter and callback allowance. -/
theorem publication_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (before : Front M P I D K S B) (state : SourceState A N)
    (result : (Result × Snapshot M P I D K S B) × SourceState A N)
    (supported : result ∈ support ((sequence source writer stage selectedMessage previousRoot response64 other
      sender route decode index metadata ready post before).run state))
    (number : Std.U64) (published : ((selected, number), true) ∈ result.1.2.2.published) :
    number.val ≤ state.1.2.length + (7 + qPost * 67) := by
  have counted := (sequence_invariant source writer stage selectedMessage previousRoot response64 other
    entry initialized selected sender route decode index metadata ready post before state result supported).2 number published
  have total := PqxdhInitialOriginPost.sequence_total (X := X) (Response := Response)
    source (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
    (PqxdhInitialSelectedOrigin.mark source selectedMessage) true sender route decode index metadata ready
    post qPost bounded (before, empty)
  exact counted.trans (PqxdhInitialCounterBudget.program_length source writer stage
    (withInitial source selectedMessage previousRoot response64 other) _ (7 + qPost * 67) total state result supported)


/-- Adaptive selection among actual published positions costs the explicit finite sum over the source-derived position allowance, while retaining any same final source event. -/
theorem selection_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N RootOracle.QueryCache))
    (entry : ConcreteRatchetKernel) (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = ok entry)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost)
    (before : Front M P I D K S B) (state : SourceState A N)
    (event : Nat → (Result × Snapshot M P I D K S B) × SourceState A N → Prop) :
    Pr{let result ← sequence source writer stage selectedMessage previousRoot response64 other sender route decode index metadata ready post before state}[∃ number : Std.U64, ((selected, number), true) ∈ result.1.2.2.published ∧ event number.val result] ≤
      ∑ position ∈ Finset.range (state.1.2.length + (7 + qPost * 67) + 1),
        Pr{let result ← sequence source writer stage selectedMessage previousRoot response64 other sender route decode index metadata ready post before state}[∃ number : Std.U64, number.val = position ∧ ((selected, number), true) ∈ result.1.2.2.published ∧ event position result] := by
  classical
  calc
    _ ≤ Pr{let result ← sequence source writer stage selectedMessage previousRoot response64 other sender route decode index metadata ready post before state}[∃ position ∈ Finset.range (state.1.2.length + (7 + qPost * 67) + 1),
        ∃ number : Std.U64, number.val = position ∧ ((selected, number), true) ∈ result.1.2.2.published ∧ event position result] := by
      apply prEvent_mono_of_support
      intro result supported accepted
      obtain ⟨number, published, enabled⟩ := accepted
      exact ⟨number.val, Finset.mem_range.mpr (Nat.lt_succ_of_le
        (publication_bound source writer stage selectedMessage previousRoot response64 other entry initialized selected
          sender route decode index metadata ready post qPost bounded before state result supported number published)),
        number, rfl, published, enabled⟩
    _ ≤ _ := prEvent_exists_finset_le _ _ _

end BeaconcryptCore.Computational.PqxdhInitialCounterPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.after_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.after_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.selected_tail_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.selected_tail_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.marked_finish_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.marked_finish_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.records_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.records_counter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.finish_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.finish_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.records_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.records_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.step_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.step_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.sequence_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.sequence_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.publication_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCounterPublication.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCounterPublication.selection_bound
