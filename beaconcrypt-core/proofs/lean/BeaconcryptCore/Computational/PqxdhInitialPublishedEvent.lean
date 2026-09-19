import BeaconcryptCore.Computational.PqxdhInitialSourcePublication
import BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness
import BeaconcryptCore.Computational.RawCtxPublishedLineage
import BeaconcryptCore.Computational.PqxdhInitialNativeCarried

/-!
One final source event retains the original Boolean result, an actual successful publication from the selected installed session, the fixed original directional root and record position, and the complete actual disclosure history. Every hybrid uses this same definition over its own final private-table view. The label observer uses the identical publication gate and the actual returned finite checker slots; no checker execution can create a publication.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialPublishedEvent
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedChain
open PqxdhInitialSourcePublication PqxdhInitialOriginPostPath
variable {ι Chain M P I D K X Response Shared A N C ContextId : Type} {extra : OracleSpec ι} {S B : Nat}

def Gate (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × (PqxdhInitialPendingPost.Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B)) : Prop :=
  result.1 = true ∧ ((selected, number), true) ∈ result.2.2.published

noncomputable def sourceEvent (source : FixedHkdfSha512NoSaltSource) (root : RootOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × Snapshot M P I D K S B) × State A N) : Prop :=
  Gate selected number result.1 ∧ RawCtxLiveLineage.Fresh
    (RawCtxPublishedLineage.lineage
      (RawCtxSelectedParentTable.view (productionStream source.crypto) result.2.1.1.2.1)
      (RawCtxFreshChainCut.concreteChain root) (number.val - 1) ++ ancestors)
    disclosed result.1.2.1.roles.2

noncomputable def sourceDecision (source : FixedHkdfSha512NoSaltSource) (root : RootOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × Snapshot M P I D K S B) × State A N) : Bool :=
  @decide (sourceEvent source root selected number ancestors disclosed result) (Classical.propDecidable _)

/-- Every substitution stage tests the same original decision, selected-session publication and complete original value freshness without conditioning. -/
theorem source_decision (source : FixedHkdfSha512NoSaltSource) (root : RootOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : (Bool × Snapshot M P I D K S B) × State A N) :
    sourceDecision source root selected number ancestors disclosed result = true ↔
      sourceEvent source root selected number ancestors disclosed result := by
  simp only [sourceDecision, decide_eq_true_eq]

/-- The source publication gate is unchanged by interpreting private chain slots; it examines only the actual original reply and installation/publication transcript. -/
theorem gate_map {Native : Type}
    (interpretKernel : PqxdhInitialPendingPost.KernelOf Chain → PqxdhInitialPendingPost.KernelOf Native)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × (PqxdhInitialPendingPost.Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B)) :
    Gate selected number
      (result.1, (PqxdhInitialParentPost.mapFront interpretKernel result.2.1, result.2.2)) ↔ Gate selected number result := Iff.rfl

/-- The shared publication gate can be used directly by the ordinary full stopped observer while the original native final lineage pays only the computed candidate event. -/
theorem checked_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : PqxdhInitialParentStoppedHop.Continuation ContextId extra M P I D K X Response Shared A N C Bool Bool S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (earlier : List RatchetChain)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    (PqxdhInitialCheckedFreshness.actualDecision target earlier disclosed (fun result => Gate selected number result.1.1) <$>
      PqxdhInitialCheckedFreshness.nativeRun source writer mark sender route decode continuation context target output disclosed state candidates).boolDistAdvantage
      (PqxdhInitialParentStoppedHop.decision
        (PqxdhInitialCheckedFreshness.remainingEvent earlier disclosed (fun result => Gate selected number result.1.1)) <$>
        PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode continuation context output disclosed state candidates) ≤
      3 * (Pr[fun result => target ∈ result.2.1.2 |
        PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode continuation context output disclosed state candidates]).toReal :=
  PqxdhInitialCheckedFreshness.bound source writer mark sender route decode continuation context target output disclosed state candidates
    earlier (fun result => Gate selected number result.1.1) n depth


/-- All actual source callbacks retain the same original directional cache walk; external effects cannot change its cursor or private table. -/
theorem callback_lineage (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (query : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C) (root : RootOutput)
    (valid : RawCtxCursorLineage.Lineage root state.1.1.2)
    (result : (PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response Shared S B).Range query × PqxdhInitialNativeLog.State A N C)
    (supported : result ∈ support ((PqxdhInitialNativeLog.handler source writer stage external query).run state)) :
    RawCtxCursorLineage.Lineage root result.2.1.1.2 := by
  cases query with
  | inl query =>
    rw [PqxdhInitialNativeLog.live_handler] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact (RawCtxCursorLineage.logged_state source writer stage query state.1 root valid reply reached).2
  | inr query =>
    rw [PqxdhInitialNativeLog.external_handler] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact valid

/-- The actual executable source cut carries its earlier cache walk from the original initial directional root, including every repeated or failed attempted derivation. -/
theorem carried_lineage {Result Origin : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (depth stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (root : RootOutput) (state reached : PqxdhInitialNativeLog.State A N C)
    (initialCursor : state.1.1.2.2 = ⟨root, 0⟩)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state)) :
    ∃ earlier, RawCtxCursorLineage.walk reached.1.1.2.1 reached.1.1.2.2.depth root =
      some (earlier, reached.1.1.2.2.input) := by
  have packed : RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (.pending context reached) ∈ support
      (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) <$>
        PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage external state) := by
    rw [support_map]
    exact ⟨.pending context reached, supported, rfl⟩
  rw [PqxdhInitialNativeCarried.carried_pack] at packed
  have valid : RawCtxCursorLineage.Lineage root state.1.1.2 := by
    change ∃ earlier, RawCtxCursorLineage.walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input)
    rw [initialCursor]
    exact ⟨[], rfl⟩
  exact RawCtxStatefulPrefixInvariant.scan_valid (PqxdhInitialNativePrefix.selected (extra := extra) depth)
    (PqxdhInitialNativeLog.handler source writer stage external)
    (fun result => RawCtxCursorLineage.Lineage root result.1.1.2)
    (fun query before valid _ reply actual => callback_lineage source writer stage external query before root valid reply actual)
    _ state valid _ packed


private theorem step_agrees (left right : RawCtxSelectedParentTable.Prior) (input : RootOutput)
    (same : left (RawCtxFirstParentRisk.inputAddress input) = right (RawCtxFirstParentRisk.inputAddress input)) :
    RawCtxPublishedLineage.step left (RawCtxFreshChainCut.concreteChain input) =
      RawCtxPublishedLineage.step right (RawCtxFreshChainCut.concreteChain input) := by
  have info : PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO
  have request : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain input)) =
      RawCtxFirstParentRisk.inputAddress input := by
    simp only [RawCtxKdfRequestTable.address, RawCtxChainSend.nativeRequest, info]
    change (⟨Pqxdh.INFO_R, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain input)).toList⟩ : JointKdfAddress) = _
    rw [RawCtxSelectedQueryTrace.rootVector_concrete]
    rfl
  simp only [RawCtxPublishedLineage.step, RawCtxFunctionalFamily.execute, request, same]

/-- Agreement on the actually published cached responses identifies the entire original finite lineage, including its target material key; no equality on unqueried fallback addresses is required. -/
theorem cached_lineage (fallback prior : RawCtxSelectedParentTable.Prior) (table : RawCtxKdfRequestTable.Table)
    (root : RootOutput) (number : Std.U64) (position : Nat) (sequence : number.val = position + 1)
    (cached : RawCtxSourcePublishedPath.Cached root number table)
    (agrees : ∀ address output, table address = some output → prior address = output) :
    RawCtxPublishedLineage.lineage (RawCtxSelectedParentTable.view fallback table)
      (RawCtxFreshChainCut.concreteChain root) position =
    RawCtxPublishedLineage.lineage prior (RawCtxFreshChainCut.concreteChain root) position := by
  obtain ⟨earlier, input, output, walked, present⟩ :=
    RawCtxSourcePublishedPath.cached_successor root number position table sequence cached
  have left := RawCtxPublishedLineage.walk_lineage table (RawCtxSelectedParentTable.view fallback table)
    (fun address output present => by simp only [RawCtxSelectedParentTable.view, present, Option.getD_some])
    position 0 root (earlier, input) walked
  have right := RawCtxPublishedLineage.walk_lineage table prior agrees position 0 root (earlier, input) walked
  simp only [Nat.add_zero] at left right
  rw [left, right]
  have equalStep := step_agrees (RawCtxSelectedParentTable.view fallback table) prior input (by
    simpa only [RawCtxSelectedParentTable.view, present, Option.getD_some] using (agrees _ output present).symm)
  simp only [RawCtxPublishedLineage.lineage, RawCtxFiniteLineageCheck.trace, equalStep]


/-- The original published source lineage splits into its actual earlier cache walk and the literal privately routed checker, using only the source cache bindings and the separately charged parent-input separation. -/
theorem source_checked_fresh (source : FixedHkdfSha512NoSaltSource)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (output : FullOutput)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address)
    (before after : RawCtxKdfRequestTable.Table) (extension : RawCtxCursorLineage.Extends before after)
    (root : RootOutput) (number : Std.U64) (depth remaining : Nat)
    (position : number.val = depth + remaining + 1)
    (cached : RawCtxSourcePublishedPath.Cached root number after)
    (earlier : List RootOutput)
    (walked : RawCtxCursorLineage.walk before depth root = some (earlier, target))
    (agrees : ∀ address response, after address = some response →
      RawCtxSelectedParentTable.lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target address = response)
    (ancestors disclosed : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    RawCtxLiveLineage.Fresh
      (RawCtxPublishedLineage.lineage (RawCtxSelectedParentTable.view (productionStream source.crypto) after)
        (RawCtxFreshChainCut.concreteChain root) (number.val - 1) ++ ancestors) disclosed history ↔
    RawCtxLiveLineage.Fresh
      ((PqxdhInitialParentStoppedHop.checkerTrace prior entry target output (some remaining)).map
          (interpret (RawCtxFreshChainCut.concreteChain target)) ++
        (earlier.map RawCtxFreshChainCut.concreteChain ++ ancestors)) disclosed history := by
  have index : number.val - 1 = depth + remaining := by omega
  rw [index, cached_lineage (productionStream source.crypto) _ after root number (depth + remaining) position cached agrees]
  rw [RawCtxPublishedLineage.walk_lineage before _
    (fun address response found => agrees address response (extension address response found))
    depth remaining root (earlier, target) walked]
  have checker := RawCtxFiniteLineageCheck.native_trace prior entry target output separate remaining .hidden
  change (PqxdhInitialParentStoppedHop.checkerTrace prior entry target output (some remaining)).map
      (interpret (RawCtxFreshChainCut.concreteChain target)) =
    RawCtxPublishedLineage.lineage
      (RawCtxSelectedParentTable.lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target)
      (RawCtxFreshChainCut.concreteChain target) remaining at checker
  rw [← checker]
  simp only [RawCtxLiveLineage.Fresh, RawCtxLiveLineage.FreshValues, List.mem_append]
  aesop

end BeaconcryptCore.Computational.PqxdhInitialPublishedEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.source_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.source_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.gate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.gate_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.checked_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.checked_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.callback_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.callback_lineage

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.carried_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.carried_lineage

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.cached_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.cached_lineage

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.source_checked_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPublishedEvent.source_checked_fresh
