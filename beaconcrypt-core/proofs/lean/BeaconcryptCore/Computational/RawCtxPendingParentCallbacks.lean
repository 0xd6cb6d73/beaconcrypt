import BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily

/-!
The predecessor cut selects the original matched callback at its actual cursor depth, including a private-cache hit. A hit is retained as a real branch because it can advance the cursor before a fresh child draw. The private KDF callback equations retain the full original response and the complete cache/cursor update. Public HKDF and all other backend work remain unchanged.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingParentCallbacks
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily

def parentCut {Auxiliary : Type} {serverCount beaconCount : Nat} (depth : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary) : Bool :=
  match RawCtxSelectedFamilyContext.queryAddress query with
  | none => false
  | some address => matched state.2.2 address && decide (state.2.2.depth = depth)

private theorem native_kdf {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (chain : RatchetChain) (state : State Auxiliary) :
    ((RawCtxInterpretedReceive.decodeResponse <$>
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
        (.inl (RawCtxChainSend.nativeRequest chain))).run state) =
      (fun result => (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1),
        (state.1, result.2))) <$> privateStep source stage (RawCtxSelectedPendingCut.requestAddress chain) state.2 := by
  simp [backend, QueryImpl.compose, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler,
    OracleSpec.query, RawCtxSelectiveChainGame.handler, StateT.run_map,
    RawCtxSelectedPendingCut.requestAddress, Functor.map_map]
  simp only [StateT.run, Functor.map_map]

/-- The complete receive callback exposes the actual private hit-or-miss response and exact cache/cursor update before normal resume. -/
theorem receive_step {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : State Auxiliary) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage)
      (.inl (.inl (.inl request)))).run state =
      (fun result => (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1),
        (state.1, result.2))) <$> privateStep source stage (RawCtxSelectedPendingCut.requestAddress request.request) state.2 := by
  have equation := congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.receive_kdf
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) request)
  exact equation.trans (native_kdf source writer stage request.request state)

/-- The complete send callback exposes the actual private hit-or-miss response and exact cache/cursor update before normal resume. -/
theorem send_step {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (state : State Auxiliary) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage)
      (.inl (.inr (.inl (.inl request))))).run state =
      (fun result => (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1),
        (state.1, result.2))) <$> privateStep source stage (RawCtxSelectedPendingCut.requestAddress request.request) state.2 := by
  have equation := congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.send_kdf
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) request)
  exact equation.trans (native_kdf source writer stage request.request state)

private theorem mapped_state {Auxiliary Reply : Type}
    (source : FixedHkdfSha512NoSaltSource) (stage : Nat) (address : JointKdfAddress)
    (decode : FullOutput → Reply) (state : State Auxiliary) (result : Reply × State Auxiliary)
    (supported : result ∈ support ((fun reply => (decode reply.1, (state.1, reply.2))) <$>
      privateStep source stage address state.2)) :
    ∃ output : FullOutput, result.2 =
      (state.1, (state.2.1.cacheQuery address output, advance state.2.2 address output)) := by
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨reply, head, rfl⟩ := supported
  exact ⟨reply.1, congrArg (fun store => (state.1, store)) (private_state source stage address state.2 reply head)⟩

/-- Every actual private pending callback preserves the shared state and updates the exact original cache/cursor through its actual full response, including a cache hit. -/
theorem kdf_state {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (Spec serverCount beaconCount).Domain) (address : JointKdfAddress)
    (sameAddress : RawCtxSelectedFamilyContext.queryAddress query = some address)
    (state : State Auxiliary) (result : (Spec serverCount beaconCount).Range query × State Auxiliary)
    (supported : result ∈ support (((handler source writer stage) query).run state)) :
    ∃ output : FullOutput, result.2 =
      (state.1, (state.2.1.cacheQuery address output, advance state.2.2 address output)) := by
  rcases query with ((request | opening) | ((request | sealing) | request)) | request
  all_goals simp only [RawCtxSelectedFamilyContext.queryAddress,
    RawCtxSelectedFamilyContext.primitiveAddress] at sameAddress
  all_goals try cases sameAddress
  all_goals first | rw [receive_step] at supported | rw [send_step] at supported
  all_goals exact mapped_state source stage _ (fun output => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output)) state result supported

/-- The predecessor selector depends on the actual matched address and depth, independently of whether the private cache already contains that address. -/
theorem parentCut_iff {Auxiliary : Type} {serverCount beaconCount : Nat}
    (depth : Nat) (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary) :
    parentCut depth query state = true ↔ ∃ address : JointKdfAddress,
      RawCtxSelectedFamilyContext.queryAddress query = some address ∧
      matched state.2.2 address = true ∧ state.2.2.depth = depth := by
  cases found : RawCtxSelectedFamilyContext.queryAddress query <;> simp [parentCut, found]

/-- Before the predecessor callback is selected, a supported private callback cannot pass the predecessor depth. -/
theorem kdf_preserve {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage depth : Nat)
    (query : (Spec serverCount beaconCount).Domain) (address : JointKdfAddress)
    (sameAddress : RawCtxSelectedFamilyContext.queryAddress query = some address)
    (state : State Auxiliary) (valid : state.2.2.depth ≤ depth) (unchosen : parentCut depth query state = false)
    (result : (Spec serverCount beaconCount).Range query × State Auxiliary)
    (supported : result ∈ support (((handler source writer stage) query).run state)) :
    result.2.2.2.depth ≤ depth := by
  obtain ⟨output, exactState⟩ := kdf_state source writer stage query address sameAddress state result supported
  rw [exactState, advance_depth]
  cases isMatch : matched state.2.2 address with
  | false => simpa only [isMatch, Bool.false_eq_true, if_false, Nat.add_zero] using valid
  | true =>
    have different : state.2.2.depth ≠ depth := by simpa [parentCut, sameAddress, isMatch] using unchosen
    simp only [if_true]
    omega

/-- A state at or before the predecessor depth cannot already be the selected fresh child cut. -/
theorem before_child {Auxiliary : Type} {serverCount beaconCount : Nat}
    (depth : Nat) (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary)
    (valid : state.2.2.depth ≤ depth) : isCut (depth + 1) query state = false := by
  have different : state.2.2.depth ≠ depth + 1 := by omega
  cases found : RawCtxSelectedFamilyContext.queryAddress query <;>
    simp [isCut, found, RawCtxSelectiveChainPrefix.isCut, different]

end BeaconcryptCore.Computational.RawCtxPendingParentCallbacks

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.receive_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.receive_step

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.send_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.send_step

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.kdf_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.kdf_state

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.parentCut_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.parentCut_iff

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.kdf_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.kdf_preserve

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.before_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingParentCallbacks.before_child
