import BeaconcryptCore.Computational.RawCtxSelectedParentContext

/-!
A selected child response patches only its exact private KDF address, retaining the prior private lookup and the predecessor entry's priority. The parent/child input collision is explicit and must be charged by the consuming source hybrid; it is not a freshness assumption or excluded source execution. The real public backend is untouched. These table equations realize an arbitrary child response under private alias-consistent routing.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

def targetAddress (target : RootOutput) : JointKdfAddress :=
  RawCtxSelectedPendingCut.requestAddress (RawCtxFreshChainCut.concreteChain target)

noncomputable def privatePatch (prior : Prior) (target : RootOutput) (output : FullOutput) : Prior :=
  fun address => if address = targetAddress target then output else prior address

/-- Exact private addresses compare the original byte values, without a distinct-key or handle-injectivity premise. -/
theorem address_eq (target : RootOutput) (chain : RatchetChain) :
    RawCtxSelectedPendingCut.requestAddress chain = targetAddress target ↔
      target = RawCtxSelectedQueryTrace.rootVector chain := by
  change (⟨_, (RawCtxSelectedQueryTrace.rootVector chain).toList⟩ : JointKdfAddress) =
    ⟨_, (RawCtxSelectedQueryTrace.rootVector (RawCtxFreshChainCut.concreteChain target)).toList⟩ ↔ _
  rw [RawCtxSelectedQueryTrace.rootVector_concrete]
  constructor
  · intro same
    exact Subtype.ext (congrArg JointKdfAddress.input same).symm
  · intro same
    rw [same]
    rfl

/-- The predecessor entry keeps priority, including collisions; the explicit source collision event is not silently removed. -/
theorem parent_retained (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput) :
    lookup (privatePatch prior target output) entry target entry.address = realize entry target := by
  simp [lookup]

/-- Away from the parent-input collision, the native selected child request uses the exact arbitrary full response. -/
theorem child_response (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (separate : targetAddress target ≠ entry.address) :
    childResponse (privatePatch prior target output) entry target = RawCtxKdfRequestTable.fullResponse output := by
  simp only [childResponse, RawCtxSelectedParentSource.response, lookup]
  change RawCtxKdfRequestTable.fullResponse
    (if targetAddress target = entry.address then realize entry target else privatePatch prior target output (targetAddress target)) = _
  simp [separate, privatePatch]

/-- The patched private table equals routing known byte aliases to the same hidden-input response, while preserving every nonalias and parent retry. -/
theorem step_patch (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (separate : targetAddress target ≠ entry.address) (slot : Slot) :
    step (privatePatch prior target output) entry (RawCtxKdfRequestTable.fullResponse output) slot =
      step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (match slot with
        | .hidden => .hidden
        | .known chain => if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain) := by
  cases slot with
  | hidden => rfl
  | known chain =>
    by_cases same : target = RawCtxSelectedQueryTrace.rootVector chain
    · have addressSame := (address_eq target chain).mpr same
      have notParent : RawCtxSelectedPendingCut.requestAddress chain ≠ entry.address := by
        rw [addressSame]
        exact separate
      simp only [if_pos same]
      simp only [RawCtxSelectedParentTable.step]
      change (if RawCtxSelectedPendingCut.requestAddress chain = entry.address then _ else _) = _
      rw [if_neg notParent]
      simp only [privatePatch]
      simp only [RawCtxSelectedPendingCut.requestAddress] at addressSame
      rw [if_pos addressSame]
    · have addressDifferent := (address_eq target chain).not.mpr same
      simp only [if_neg same]
      simp only [RawCtxSelectedParentTable.step]
      split <;> simp only [privatePatch, show RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) ≠ targetAddress target from addressDifferent, if_false]

/-- The actual native KDF response under the private patch is the interpretation of the same alias-consistent Slot response. -/
theorem native_step (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (separate : targetAddress target ≠ entry.address) (slot : Slot) :
    nativeStep (privatePatch prior target output) entry target
      (interpret (RawCtxFreshChainCut.concreteChain target) slot) =
      Prod.map (interpret (RawCtxFreshChainCut.concreteChain target)) id
        (step prior entry (RawCtxKdfRequestTable.fullResponse output)
          (match slot with
          | .hidden => .hidden
          | .known chain => if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)) := by
  rw [RawCtxSelectedParentTable.step_table]
  change Prod.map (interpret (RawCtxFreshChainCut.concreteChain target)) id
    (step (privatePatch prior target output) entry (childResponse (privatePatch prior target output) entry target) slot) = _
  rw [child_response prior entry target output separate, step_patch prior entry target output separate]

/-- The complete concrete reached-parent continuation admits an arbitrary privately patched child response; its real public backend and entire source client remain unchanged. -/
theorem native_cut {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : RawCtxSelectedParentContext.Context Metadata Result serverCount beaconCount)
    (parentOutput childOutput : FullOutput)
    (separate : targetAddress (PqxdhOrderedChainHybrids.nextChain parentOutput) ≠ RawCtxSelectedParentContext.address context) :
    RawCtxSelectedParentContext.native (Auxiliary := Auxiliary) source writer
      (privatePatch prior (PqxdhOrderedChainHybrids.nextChain parentOutput) childOutput) sender decode owner context parentOutput =
      Prod.map id (RawCtxSelectedParentLiveSource.project (PqxdhOrderedChainHybrids.nextChain parentOutput)) <$>
        simulateQ (RawCtxSelectedParentCompiler.live source writer
          (privatePatch prior (PqxdhOrderedChainHybrids.nextChain parentOutput) childOutput)
          (fromOutput (RawCtxSelectedParentContext.address context) parentOutput)
          (RawCtxKdfRequestTable.fullResponse childOutput)
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain parentOutput))))
          (RawCtxSelectedParentContext.stopped sender decode owner context (PqxdhOrderedChainHybrids.material parentOutput)) := by
  rw [RawCtxSelectedParentContext.native_cut,
    child_response prior (fromOutput (RawCtxSelectedParentContext.address context) parentOutput)
      (PqxdhOrderedChainHybrids.nextChain parentOutput) childOutput separate]

end BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.address_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.address_eq

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.parent_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.parent_retained

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.child_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.child_response

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.step_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.step_patch

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.native_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.native_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch.native_cut
