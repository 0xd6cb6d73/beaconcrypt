import BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks
import BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix
import BeaconcryptCore.Computational.RawCtxSelectiveChainPrefix

/-!
The actual selective private-table family game is executed through the enriched original LIVE source compiler. A state-dependent scan retains the complete original pending receive/send payload while the same mutable table and cursor choose the actual selected miss. Public HKDF stays the original real backend. The initial family may be arbitrary here: these operational laws do not establish an initial root distribution, identify cursor depth with a source sequence, or derive child-address separation from the parent miss. Those consuming source and alias obligations remain explicit.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily
open PqxdhJointKdf PqxdhJointKdfGame RawCtxSelectiveChainGame

abbrev Spec := RawCtxPendingFamilyLiveQueries.Spec RatchetChain
abbrev State (Auxiliary : Type) := RawCtxSharedPrimitive.SharedState Auxiliary × Store

noncomputable def backend {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :=
  RawCtxSelectiveChainGame.handler source stage (RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer) ∘ₛ
    RawCtxSelectiveKdfFamily.compiler

noncomputable def handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat) :
    QueryImpl (Spec serverCount beaconCount) (StateT (State Auxiliary) ProbComp) :=
  RawCtxPendingFamilyNative.handler (backend source writer stage)

def isCut {Auxiliary : Type} {serverCount beaconCount : Nat} (stage : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary) : Bool :=
  match RawCtxSelectedFamilyContext.queryAddress query with
  | none => false
  | some address => RawCtxSelectiveChainPrefix.isCut (spec := RawCtxServerServices.BackendSpec) stage (.inr address) state

noncomputable def program {Metadata PeerMetadata Identity DhPair KemPair Result : Type} {serverCount beaconCount : Nat}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :=
  RawCtxPendingFamilyLiveTails.program sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)

noncomputable def scan {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : State Auxiliary) :=
  RawCtxStatefulPendingPrefix.scan (isCut cutStage) (handler source writer runStage)
    (program sender route decode client state) primitive

/-- The complete enriched program is exactly the original selective native family game, retaining every original role/history field and complete mutable table, cursor and primitive state. -/
theorem source_program {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    RawCtxSelectiveChainGame.family source writer stage serverCount beaconCount sender route decode client state primitive store =
      Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
        ((simulateQ (handler source writer stage) (program sender route decode client state)).run (primitive, store)) := by
  have actual := congrArg (fun computation => computation.run (primitive, store))
    (RawCtxPendingFamilyNative.actual (backend source writer stage) sender route decode client state)
  simpa only [RawCtxSelectiveChainGame.family, RawCtxSelectiveKdfFamily.program,
    ← QueryImpl.simulateQ_compose, backend, StateT.run_map, handler, program, Prod.map_def, id_eq] using actual

private theorem native_same {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (left right : Nat)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (notKdf : query.isLeft = false) :
    ((backend (Auxiliary := Auxiliary) source writer left) ∘ₛ RawCtxServerServices.nativeLift) query =
      ((backend source writer right) ∘ₛ RawCtxServerServices.nativeLift) query := by
  cases query with
  | inl _ => cases notKdf
  | inr query =>
    simp [backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
      RawCtxSelectiveKdfFamily.compiler, RawCtxSelectiveChainGame.handler, OracleSpec.query]

private theorem public_same {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (left right : Nat) :
    (backend (Auxiliary := Auxiliary) source writer left) ∘ₛ RawCtxServerServices.publicLift =
      (backend source writer right) ∘ₛ RawCtxServerServices.publicLift := by
  funext query
  rcases query with query | (query | query) <;>
    simp [backend, QueryImpl.compose, RawCtxServerServices.publicLift,
      RawCtxSelectiveKdfFamily.compiler, RawCtxSelectiveChainGame.handler, OracleSpec.query]

private theorem kdf_same {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (chain : RatchetChain) (state : State Auxiliary)
    (unchosen : RawCtxSelectiveChainPrefix.isCut (spec := RawCtxServerServices.BackendSpec) stage
      (.inr (RawCtxSelectedPendingCut.requestAddress chain)) state = false) :
    ((RawCtxInterpretedReceive.decodeResponse <$>
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift) (.inl (RawCtxChainSend.nativeRequest chain))).run state) =
    ((RawCtxInterpretedReceive.decodeResponse <$>
      ((backend source writer (stage + 1)) ∘ₛ RawCtxServerServices.nativeLift) (.inl (RawCtxChainSend.nativeRequest chain))).run state) := by
  have same := RawCtxSelectiveChainPrefix.handler_same source stage (RawCtxProtocolBackend.backend source writer)
    (.inr (RawCtxSelectedPendingCut.requestAddress chain)) state unchosen
  simpa [backend, QueryImpl.compose, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler,
    OracleSpec.query, StateT.run_map, RawCtxSelectedPendingCut.requestAddress, Functor.map_map] using
    congrArg (fun computation => (fun result =>
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1), result.2)) <$> computation) same

private theorem non_kdf_same {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain) (state : State Auxiliary)
    (notKdf : RawCtxPendingMixedPrefix.ownerSelected query = false) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage) (.inl query)).run state =
      ((handler source writer (stage + 1)) (.inl query)).run state := by
  change (RawCtxPendingNativeCalls.pending ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
    ((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) query).run state =
    (RawCtxPendingNativeCalls.pending ((backend source writer (stage + 1)) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer (stage + 1)) ∘ₛ RawCtxServerServices.publicLift) query).run state
  rw [public_same source writer (stage + 1) stage]
  exact congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.non_kdf _ _ _ (native_same source writer stage (stage + 1)) query notKdf)

private theorem receive_handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : State Auxiliary) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage)
      (.inl (.inl (.inl request)))).run state =
      ((RawCtxInterpretedReceive.decodeResponse <$>
        ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
          (.inl (RawCtxChainSend.nativeRequest request.request))).run state) := by
  exact congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.receive_kdf
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) request)

private theorem send_handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (state : State Auxiliary) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage)
      (.inl (.inr (.inl (.inl request))))).run state =
      ((RawCtxInterpretedReceive.decodeResponse <$>
        ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
          (.inl (RawCtxChainSend.nativeRequest request.request))).run state) := by
  exact congrArg (fun computation => computation.run state)
    (RawCtxPendingNativeCallbacks.send_kdf
      ((backend source writer stage) ∘ₛ RawCtxServerServices.nativeLift)
      ((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) request)

private theorem public_handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : RawCtxServerServices.PublicSpec.Domain) (state : State Auxiliary) :
    ((handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage)
      (.inl (.inr (.inr request)))).run state =
      (((backend source writer stage) ∘ₛ RawCtxServerServices.publicLift) request).run state := by
  simp [handler, RawCtxPendingFamilyNative.handler, RawCtxPendingFamilyLiveQueries.handler,
    RawCtxPendingNativeCalls.pending, QueryImpl.compose, RawCtxPendingOwnerQueries.erase,
    RawCtxPendingNativeCalls.original, OracleSpec.query]

private theorem read_handler {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (request : (RawCtxGenericFamilyRead.ReadSpec (RawCtxPendingOwnerQueries.Kernel RatchetChain) serverCount beaconCount).Domain)
    (state : State Auxiliary) :
    ((handler source writer stage) (.inr request)).run state =
      ((RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk request : StateT (State Auxiliary) ProbComp _).run state) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Adjacent selective stages agree literally on every complete enriched callback execution before the actual selected miss. -/
theorem handler_same {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary)
    (unchosen : isCut stage query state = false) :
    ((handler source writer stage) query).run state = ((handler source writer (stage + 1)) query).run state := by
  cases query with
  | inr request =>
    exact (read_handler source writer stage request state).trans (read_handler source writer (stage + 1) request state).symm
  | inl query =>
    rcases query with (request | opening) | ((request | sealing) | request)
    · exact (receive_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage request state).trans
        ((kdf_same source writer stage request.request state unchosen).trans
          (receive_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer (stage + 1) request state).symm)
    · exact non_kdf_same (serverCount := serverCount) (beaconCount := beaconCount) source writer stage (.inl (.inr opening)) state rfl
    · exact (send_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage request state).trans
        ((kdf_same source writer stage request.request state unchosen).trans
          (send_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer (stage + 1) request state).symm)
    · exact non_kdf_same (serverCount := serverCount) (beaconCount := beaconCount) source writer stage (.inr (.inl (.inr sealing))) state rfl
    · exact (public_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer stage request state).trans
        ((congrArg (fun impl => (impl request).run state) (public_same source writer stage (stage + 1))).trans
          (public_handler (serverCount := serverCount) (beaconCount := beaconCount) source writer (stage + 1) request state).symm)

/-- Adjacent complete source stages have the same enriched prefix before the selected miss. -/
theorem scan_same {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : State Auxiliary) :
    scan source writer stage stage sender route decode client state primitive =
      scan source writer stage (stage + 1) sender route decode client state primitive :=
  RawCtxStatefulPendingPrefix.scan_same (isCut stage) _ _ (handler_same source writer stage)
    (program sender route decode client state) primitive

/-- Completing the enriched scan retains the exact original selective source family at every cut depth and run stage, including early completion. -/
theorem scan_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (scan source writer cutStage runStage sender route decode client state (primitive, store) >>=
        RawCtxPendingMixedPrefix.finish (handler source writer runStage)) =
      RawCtxSelectiveChainGame.family source writer runStage serverCount beaconCount sender route decode client state primitive store := by
  rw [scan, RawCtxStatefulPendingPrefix.scan_finish]
  exact (source_program source writer runStage sender route decode client state primitive store).symm

/-- Both adjacent actual family stages resume the same source-derived complete prefix with their original pending callbacks and full states. -/
theorem adjacent_complete {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store) :
    let common := scan source writer stage stage sender route decode client state (primitive, store)
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (handler source writer stage)) =
      RawCtxSelectiveChainGame.family source writer stage serverCount beaconCount sender route decode client state primitive store) ∧
    (Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
      (common >>= RawCtxPendingMixedPrefix.finish (handler source writer (stage + 1))) =
      RawCtxSelectiveChainGame.family source writer (stage + 1) serverCount beaconCount sender route decode client state primitive store) := by
  refine ⟨scan_complete source writer stage stage sender route decode client state primitive store, ?_⟩
  rw [scan_same]
  exact scan_complete source writer stage (stage + 1) sender route decode client state primitive store

private theorem cut_selected {Auxiliary : Type} {serverCount beaconCount : Nat}
    (stage : Nat) (query : (Spec serverCount beaconCount).Domain) (state : State Auxiliary)
    (chosen : isCut stage query state = true) : RawCtxPendingFamilyLiveTails.selected query = true := by
  rcases query with ((request | opening) | ((request | sealing) | request)) | request
  all_goals first | rfl | simp [isCut, RawCtxSelectedFamilyContext.queryAddress,
    RawCtxSelectedFamilyContext.primitiveAddress] at chosen

/-- Every supported dynamic selected miss derives the original complete source context, exact pending address and actual cache/match/depth facts from that same reached interpreter state. -/
theorem reached_context {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (cutStage runStage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive reached : State Auxiliary) (query : (Spec serverCount beaconCount).Domain)
    (next : (Spec serverCount beaconCount).Range query → OracleComp (Spec serverCount beaconCount)
      (Result × RawCtxSelectedFamilyContext.NativeLive Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (scan source writer cutStage runStage sender route decode client state primitive)) :
    ∃ context : RawCtxSelectedFamilyContext.Context Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount,
      (⟨query, next⟩ : RawCtxSelectedFamilyContext.Frame Metadata PeerMetadata Identity DhPair KemPair Result serverCount beaconCount) =
        RawCtxSelectedFamilyContext.frame sender route decode context ∧
      RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) ∧
      Eligible cutStage (RawCtxSelectedFamilyContext.address context) reached.2 := by
  have origin := RawCtxStatefulPendingPrefix.pending_origin (isCut cutStage) (handler source writer runStage)
    (program sender route decode client state) primitive reached query next supported
  have tail := RawCtxPendingFamilyLiveTails.program_tail sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)
    query next origin.2 (cut_selected cutStage query reached origin.1)
  obtain ⟨context, same⟩ := RawCtxSelectedFamilyContext.tail_context sender route decode query next tail
  have sameQuery := congrArg Sigma.fst same
  change query = (RawCtxSelectedFamilyContext.frame sender route decode context).1 at sameQuery
  have sameAddress : RawCtxSelectedFamilyContext.queryAddress query = some (RawCtxSelectedFamilyContext.address context) := by
    rw [sameQuery]
    exact RawCtxSelectedFamilyContext.frame_address sender route decode context
  have chosen := origin.1
  rw [isCut, sameAddress] at chosen
  exact ⟨context, same, sameAddress,
    (RawCtxSelectiveChainPrefix.private_isCut RawCtxServerServices.BackendSpec cutStage
      (RawCtxSelectedFamilyContext.address context) reached).mp chosen⟩

/-- The same actual selective source and enriched program have identical selective underlying query caps by literal execution equality, retaining all complete state. -/
theorem source_query_bounds {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : Store)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (RawCtxSelectiveChainGame.family source writer stage serverCount beaconCount sender route decode client state primitive store).IsQueryBoundP predicate budget ↔
      ((simulateQ (handler source writer stage) (program sender route decode client state)).run (primitive, store)).IsQueryBoundP predicate budget := by
  rw [source_program, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.source_program
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.handler_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.handler_same
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.scan_same
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.scan_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.scan_complete
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.adjacent_complete
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.reached_context
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.source_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.source_query_bounds
