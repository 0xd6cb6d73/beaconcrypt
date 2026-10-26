import BeaconcryptCore.Computational.PqxdhLaterSelectedPaths
import BeaconcryptCore.Computational.PqxdhLaterCommonRisk
import BeaconcryptCore.Computational.RawCtxRetainedFunctionalPath

/-! A reached selected directional path and the same actual cursor lineage identify the later send input under the retained table. No injectivity of chain bytes is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSendAddress
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxCursorLineage RawCtxSelectiveChainGame RawCtxSelectedParentTable
variable {AD PT CT : Type}

/-- The actual counter-length source send path meets the retained cursor's immediate successor at exactly the next position. Both walks use the same complete table, including repeated inputs and correlated output fields. -/
theorem retained_address (prior : Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (entry : ConcreteRatchetKernel)
    (reachable : RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin entry)
    (store : Store) (lineage : Lineage (RawCtxSelectedQueryTrace.rootVector sendOrigin) store)
    (extension : Extends store.1 (RawCtxRetainedFunctionalPath.table prior))
    (parent : FullOutput) (retained : prior (cursorAddress store.2) = parent)
    (position : entry.refined.control.send_sequence.val = store.2.depth + 1) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest entry.refined.send_chain) =
      RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) := by
  obtain ⟨earlier, walked⟩ := lineage
  have extended := walk_extends store.1 (RawCtxRetainedFunctionalPath.table prior) extension
    store.2.depth (RawCtxSelectedQueryTrace.rootVector sendOrigin) (earlier, store.2.input) walked
  have successor : walk (RawCtxRetainedFunctionalPath.table prior) (store.2.depth + 1)
      (RawCtxSelectedQueryTrace.rootVector sendOrigin) = some (earlier ++ [store.2.input], nextChain parent) := by
    rw [walk, extended]
    simp [RawCtxRetainedFunctionalPath.table,
      show RawCtxFirstParentRisk.inputAddress store.2.input = cursorAddress store.2 from rfl, retained]
  obtain ⟨inputs, path⟩ := RawCtxRetainedFunctionalPath.reachable_path prior cr sendOrigin receiveOrigin entry reachable
  rw [position, successor] at path
  have same : nextChain parent = RawCtxSelectedQueryTrace.rootVector entry.refined.send_chain :=
    congrArg Prod.snd (Option.some.inj path)
  rw [RawCtxRetainedFunctionalPath.request_address, ← same]
  exact (PqxdhLaterParentAlias.target_address (nextChain parent)).symm


open PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient PqxdhPreparedPendingReplay
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
local notation "Start" => PqxdhErasedParentSample.Start (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)
local notation "Pending" => PqxdhErasedParentSample.Pending (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K)
  (A := A) (N := N) (S := S) (B := B)
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The literal one-start sampler supplies its exact selected cursor depth, source address and directional lineage. No path or selected-address premise is imposed on an arbitrary descriptor. -/
theorem sample_one_cursor (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start)) :
    pending.2.1.1.1.2.2.depth = depth ∧
    PqxdhInitialBuilderContext.address pending.1.original = cursorAddress pending.2.1.1.1.2.2 ∧
    Lineage (PqxdhInitialSourceExperiment.root source zeroRoot (PqxdhInitialSampledParent.response start)
      start.1.selected) pending.2.1.1.1.2 := by
  have actual := (PqxdhInitialPreparedParent.supported_pending source writer _ _ _ _ _ _ sender route decode _ _
    depth _ pending.2 pending.1).mp supported
  have native := PqxdhInitialSourcePreparedSecrecy.supported_source source writer start.1.selectedMessage
    zeroRoot (PqxdhInitialSampledParent.response start) start.1.other sender route decode start.1.index
    start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before start.1.selected
    start.1.shared start.1.privateState start.1.cache depth ⟨pending, actual.1⟩
  have cases := PqxdhInitialNativeCarried.carried_cases source writer _ sender route decode _ depth
    (depth + 1) _ _ pending.2.1
    (PqxdhInitialSourceExperiment.initial_valid _ start.1.shared start.1.privateState start.1.cache depth).1.1
    pending.1 native
  have invariant := PqxdhLaterCommonRisk.carried_invariants source writer _ sender route decode _ depth
    (depth + 1) _ _ (PqxdhInitialSourceExperiment.initialState
      (PqxdhInitialSourceExperiment.root source zeroRoot (PqxdhInitialSampledParent.response start) start.1.selected)
      start.1.shared start.1.privateState start.1.cache)
    (Nat.zero_le depth) (RawCtxCursorLineage.initial _ _) (.pending pending.1 pending.2.1) native
  refine ⟨?_, ?_, invariant.2⟩
  · simpa only [actual.2, reduceCtorEq, exists_false, and_false, false_or, true_and] using cases.2
  · simpa only [RawCtxSelectiveChainGame.matched, decide_eq_true_eq] using cases.1


/-- The same actual input-alias complement makes the retained parent/child lookup extend the sampled prefix, and its parent coordinate remains the exact full response. -/
theorem sample_one_table (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original]) :
    Extends pending.2.1.1.1.2.1
      (RawCtxRetainedFunctionalPath.table (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output)) ∧
    PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output (cursorAddress pending.2.1.1.1.2.2) = parent := by
  have cursor := sample_one_cursor source writer sender route decode depth start pending supported
  have separate : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ≠
      PqxdhInitialBuilderContext.address pending.1.original :=
    fun same => safe (List.mem_append_right _ (List.mem_singleton.mpr same))
  constructor
  · intro request response found
    have kept := PqxdhLaterRetainedPatch.sample_one_extends source writer sender route decode depth start pending
      supported parent output safe request response found
    simp only [RawCtxRetainedFunctionalPath.table, QueryCache.toFn_ofFn, PqxdhLaterPatchedOccurrence.patchedPrior,
      ← PqxdhInitialNativeParentChild.child_view source pending.2.1 _ parent output separate,
      RawCtxSelectedParentTable.view, kept, Option.getD_some]
  · simp only [← cursor.2.1, PqxdhLaterPatchedOccurrence.patchedPrior, RawCtxSelectedParentTable.lookup,
      RawCtxSelectedParentEntry.realize_fromOutput]
    simp only [RawCtxSelectedParentEntry.fromOutput, ↓reduceIte]


/-- A source-selected initializer has the exact directional root used by the earlier cursor, for either actual role. This follows from constructor equality rather than equal-key injectivity. -/
theorem initial_root (source : FixedHkdfSha512NoSaltSource)
    (response : PqxdhInitialRootLabelService.Response) (owner : RawCtxProtocolReveals.Owner S B)
    (initial : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (selected : match owner with
      | .server _ _ => (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response) = .ok initial
      | .beacon _ => initial = (PqxdhInitialRootAudit.kernel (zeroRoot, response)).refined) :
    RawCtxSelectedQueryTrace.rootVector initial.send_chain =
      PqxdhInitialSourceExperiment.root source zeroRoot response owner := by
  cases owner with
  | server index peer =>
    simp only [PqxdhInitialSourceExperiment.server_created source response, RawCtxMaterialInterpretation.rust_map_ok, RustM.ok.injEq] at selected
    exact congrArg (fun kernel => RawCtxSelectedQueryTrace.rootVector kernel.send_chain) selected.symm
  | beacon index =>
    exact congrArg (fun kernel => RawCtxSelectedQueryTrace.rootVector kernel.send_chain) selected


/-- At a reached marked installation with the source positional counter, actual sampler lineage and the same retained directional paths identify the later send request. The marker is taken at this state, not inferred backwards from a later installation map. -/
theorem marked_address (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (front : PqxdhInitialPendingPost.Front RatchetChain M P I D K S B)
    (origins : PqxdhInitialOriginPost.Trace Bool S B)
    (receipts : PqxdhInitialInstallOccurrence.Trace RatchetChain Response PqxdhPhase2DecapsulationRouting.Shared S B)
    (selected : PqxdhRetainedSelectedOrigins.Selected
      (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false (PqxdhInitialSampledParent.response start))
      (PqxdhInitialRootAudit.kernel (zeroRoot, PqxdhInitialSampledParent.response start)).refined origins receipts)
    (paths : PqxdhInitialOccurrencePaths.Holds cr (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) front receipts)
    (marked : origins.installed start.1.selected = some true)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (found : RawCtxGenericRoleFamily.selectedKernel start.1.selected front.roles.1 = some kernel)
    (position : kernel.control.send_sequence.val = depth + 1) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest kernel.send_chain) =
      RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) := by
  obtain ⟨initial, exactInitial, reachable⟩ := PqxdhRetainedSelectedOrigins.selected_path cr
    (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) _ _ front origins receipts
    selected paths start.1.selected marked kernel found
  have cursor := sample_one_cursor source writer sender route decode depth start pending supported
  have table := sample_one_table source writer sender route decode depth start pending supported parent output safe
  apply retained_address (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) cr
    initial.send_chain initial.receive_chain ⟨kernel⟩ reachable pending.2.1.1.1.2 _ table.1 parent table.2
  · simpa only [cursor.1] using position
  · simpa only [initial_root source (PqxdhInitialSampledParent.response start) start.1.selected initial
      (by split at exactInitial <;> simp_all only)]
      using cursor.2.2


/-- Complete supported retained resumption supplies both source occurrence invariants used by the address join. The original Post may have any optional outcomes; the selected marker and positional counter are inspected at this exact returned state. -/
theorem completed_address (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (depth : Nat) (start : Start) (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhErasedParentSample.sampleOne source writer sender route decode depth start))
    (parent output : FullOutput)
    (safe : RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) ∉ pending.2.1.1.2 ++
      [PqxdhInitialBuilderContext.address pending.1.original])
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B ×
      PqxdhInitialNativeRetained.RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support ((simulateQ
      (PqxdhInitialNativeRetained.retained source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending parent output) (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original parent))).run
          (PqxdhInitialNativeRetained.project pending.2.1)))
    (marked : result.1.2.2.installed start.1.selected = some true)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (found : RawCtxGenericRoleFamily.selectedKernel start.1.selected result.1.2.1.roles.1 = some kernel)
    (position : kernel.control.send_sequence.val = depth + 1) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest kernel.send_chain) =
      RawCtxSelectedParentPrivatePatch.targetAddress (nextChain parent) := by
  obtain ⟨evidence, _, paths, selected⟩ := PqxdhLaterSelectedPaths.sample_one_selected source writer sender route decode
    cr depth start pending supported parent output safe result completed
  exact marked_address source writer sender route decode cr depth start pending supported parent output safe
    result.1.2.1 result.1.2.2 evidence selected paths marked kernel found position


local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := extra) (M := M) (P := P)
  (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B)

/-- Full material sampling and literal retained source completion discharge all path, initializer and cursor premises. The inspected marker/kernel belong to this exact returned state, and the prior remains the actual pre-normalization source draw. -/
theorem material_address (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (depth : Nat)
    (prior : ProbComp (PqxdhInitialSourceInitialSecrecy.Context extra M P I D K X Response A N S B))
    (context : MaterialContext)
    (sampled : context ∈ support (PqxdhErasedParentMaterial.prepare source writer sender route decode depth prior))
    (start : Start) (pending : Pending) (shape : context.1.1.1 = .inr (start, .inr pending))
    (safe : PqxdhLaterInputAlias.collision context = false) (output : FullOutput)
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B ×
      PqxdhInitialNativeRetained.RetainedState A N RootOracle.QueryCache)
    (completed : result ∈ support ((simulateQ
      (PqxdhInitialNativeRetained.retained source writer
        (PqxdhLaterPatchedOccurrence.patchedPrior source pending (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2) output)
        (sampleExternal source start))
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker source start) sender route decode pending.1
        (PqxdhInitialParentBuilderContext.reply sender route decode pending.1.original
          (RawCtxSelectedParentEntry.realize context.1.1.2 context.1.2)))).run (PqxdhInitialNativeRetained.project pending.2.1)))
    (marked : result.1.2.2.installed start.1.selected = some true)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (found : RawCtxGenericRoleFamily.selectedKernel start.1.selected result.1.2.1.roles.1 = some kernel)
    (position : kernel.control.send_sequence.val = depth + 1) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest kernel.send_chain) =
      RawCtxSelectedParentPrivatePatch.targetAddress context.1.2 := by
  simp only [PqxdhErasedParentMaterial.prepare, mem_support_bind_iff, mem_support_pure_iff] at sampled
  obtain ⟨packet, sampled, parent, _, nonce, _, chain, _, rfl⟩ := sampled
  simp only [RawCtxSelectedParentEntry.realize_fromOutput] at completed
  simp only [PqxdhErasedParentSample.sample, mem_support_bind_iff] at sampled
  obtain ⟨common | input, priorReached, block, _, sampled⟩ := sampled
  · simp only [mem_support_pure_iff] at sampled
    simp only [sampled, PqxdhErasedParentSample.normalize, reduceCtorEq] at shape

  · simp only [mem_support_bind_iff, mem_support_pure_iff] at sampled
    obtain ⟨common | reachedPending, reached, rfl⟩ := sampled
    · cases shape
    · simp only [PqxdhErasedParentSample.normalize, Sum.inr.injEq, Prod.mk.injEq] at shape
      rcases shape with ⟨rfl, rfl⟩
      exact completed_address source writer sender route decode cr depth (input, block) reachedPending reached
        parent output (of_decide_eq_false safe) result completed marked kernel found position

end BeaconcryptCore.Computational.PqxdhLaterSendAddress

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.retained_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.retained_address
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.sample_one_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.sample_one_cursor
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.sample_one_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.sample_one_table
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.initial_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.initial_root
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.marked_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.marked_address
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.completed_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.completed_address
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSendAddress.material_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSendAddress.material_address
