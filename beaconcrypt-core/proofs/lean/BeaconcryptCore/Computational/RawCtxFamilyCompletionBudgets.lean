import BeaconcryptCore.Computational.RawCtxFamilyResidualBudget
import BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets
import BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler

/-!
The exact material-only pending completion retains its source-derived quiet owner, Server and family continuations. The actual U8 counter permits at most 254 further receive KDF callbacks, followed by one possible opening; a selected send needs only its sealing completion. The exact pending eraser then resumes the original bounded LIVE client. Seven separate primitive bounds preserve all state, optional results and public evaluations without a hidden whole-observer budget.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets
open RawCtxSelectedChain RawCtxSelectedFamilyContext RawCtxFamilyPrimitiveBudgets RawCtxPendingOwnerQueries
open PqxdhOrderedChainHybrids

/-- The actual U8 remaining field gives at most 254 further KDF calls after the selected pending reply. -/
theorem pending_kdf {Context : Type}
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial Context) (value : Material) :
    RawCtxChainReceiveBounds.kdfCost (RawCtxSelectedPendingCut.receiveStop pending value) ≤ 254 := by
  have upper : pending.remaining.val ≤ 255 := by scalar_tac
  have cost := RawCtxChainReceiveBounds.resume_cost (RawCtxSelectedPendingCut.receivePending pending)
    (Slot.hidden, RawCtxFreshChainCut.concreteMaterial value)
  change RawCtxChainReceiveBounds.kdfCost (RawCtxSelectedPendingCut.receiveStop pending value) + 1 ≤
    max 1 pending.remaining.val at cost
  omega

def receiveReserve : Class → Nat
  | .kdf => 254
  | .open => 1
  | _ => 0

def sendReserve : Class → Nat
  | .seal => 1
  | _ => 0

/-- The exact material-only receive resumption retains every remaining skip and its one optional opening. -/
theorem receive_effect
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (value : Material) (selected : Class) :
    (simulateQ originalReceive (RawCtxChainReceive.program (RawCtxSelectedPendingCut.receiveStop pending value))).IsQueryBoundP
      (fun query => primitiveClass query = selected) (receiveReserve selected) := by
  cases selected
  case kdf =>
    apply RawCtxSourceOpen.simulate_bound originalReceive
      (fun query => query.isLeft = true) _ _ 254
      ((RawCtxChainReceiveBounds.program_cost _).mono (pending_kdf pending value))
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  case «open» =>
    apply RawCtxSourceOpen.simulate_bound originalReceive
      (fun query => query.isRight = true) _ _ 1 (RawCtxChainReceiveBounds.program_open_bound _)
    intro query
    cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])
  all_goals
    apply RawCtxSourceOpen.simulate_bound originalReceive
      (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  all_goals intro query
  all_goals cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [primitiveClass])

private theorem quiet_owner {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (quiet : client.IsTotalQueryBound 0)
    (state : RawCtxPendingOwnerTails.Owner Slot Metadata) (selected : Class) :
    (simulateQ erase (RawCtxPendingOwnerTails.program sender decode client state)).IsQueryBoundP
      (fun query => primitiveClass query = selected) 0 := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client quiet
  trivial

/-- Exact receive publication followed by its derived quiet owner client preserves the pending completion bill. -/
theorem receive_owner {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (before : NativeOwner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (value : Material) (selected : Class) :
    (simulateQ erase (RawCtxSelectedParentOwnerCut.receiveStop sender decode before outside pending value)).IsQueryBoundP
      (fun query => primitiveClass query = selected) (receiveReserve selected) := by
  simp only [RawCtxSelectedParentOwnerCut.receiveStop, RawCtxPendingOwnerTails.receiveTail, simulateQ_bind]
  have first : (simulateQ erase (simulateQ receiveForward
      (RawCtxPendingReceiveQueries.program (RawCtxSelectedPendingCut.receiveStop pending value)))).IsQueryBoundP
      (fun query => primitiveClass query = selected) (receiveReserve selected) := by
    rw [← QueryImpl.simulateQ_compose, receive_erase, QueryImpl.simulateQ_compose,
      RawCtxPendingReceiveQueries.program_forward]
    exact receive_effect pending value selected
  have after : ∀ result, (simulateQ erase (RawCtxPendingOwnerTails.receiveRest sender decode
      (RawCtxSelectedParentOwnerCut.knownOwner before) outside result)).IsQueryBoundP
      (fun query => primitiveClass query = selected) 0 := by
    intro result
    exact quiet_owner sender decode _ (quiet _) _ selected
  simpa only [Nat.add_zero, RawCtxSelectedPendingCut.receiveStop] using isQueryBoundP_bind first (fun result _ => after result)

/-- The selected send has already received its KDF reply; its exact completion performs only sealing before quiet owner publication. -/
theorem send_owner {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (before : NativeOwner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp RawCtxSelectedPublicTrace.SourceSpec Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (value : Material) (selected : Class) :
    (simulateQ erase (RawCtxSelectedParentOwnerCut.sendStop sender decode before outside pending value)).IsQueryBoundP
      (fun query => primitiveClass query = selected) (sendReserve selected) := by
  let ready := RawCtxSelectedPendingCut.sendStop pending value
  have first : (erase (.inr (.inl (.inr ready)))).IsQueryBoundP
      (fun query => primitiveClass query = selected) (sendReserve selected) := by
    apply (isQueryBoundP_query_iff _ _ _).mpr
    cases selected <;> simp [primitiveClass, sendReserve]
  have after : ∀ sealed, (simulateQ erase (RawCtxPendingOwnerTails.sendRest sender decode
      (RawCtxSelectedParentOwnerCut.knownOwner before) outside (ready.advanced, sealed))).IsQueryBoundP
      (fun query => primitiveClass query = selected) 0 := by
    intro sealed
    exact quiet_owner sender decode _ (quiet sealed) _ selected
  simpa only [Nat.add_zero, RawCtxSelectedParentOwnerCut.sendStop, RawCtxPendingOwnerTails.sendTail,
    simulateQ_bind, simulateQ_spec_query, ready, RawCtxSelectedPendingCut.sendStop] using
    isQueryBoundP_bind first (fun result _ => after result)

def ownerReserve {Metadata Result : Type} : OwnerContext Metadata Result → Class → Nat
  | .receive _ _ _ => receiveReserve
  | .send _ _ _ => sendReserve

/-- Every concrete quiet owner context has a branch-specific completion cap, without counting a new selected KDF request. -/
theorem owner_stopped {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (context : OwnerContext Metadata Result)
    (quiet : RawCtxQuietOwnerTails.Quiet context) (value : Material) (selected : Class) :
    (simulateQ erase (ownerStopped sender decode context value)).IsQueryBoundP
      (fun query => primitiveClass query = selected) (ownerReserve context selected) := by
  cases context with
  | receive before outside pending => exact receive_owner sender decode before outside quiet pending value selected
  | send before outside pending => exact send_owner sender decode before outside quiet pending value selected

private theorem quiet_server {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result) (quiet : client.IsTotalQueryBound 0)
    (state : RawCtxPendingServerTails.State Slot Metadata PeerMetadata) (selected : Class) :
    (simulateQ erase (RawCtxPendingServerTails.program sender route decode client state)).IsQueryBoundP
      (fun query => primitiveClass query = selected) 0 := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client quiet
  trivial

def serverReserve {Metadata PeerMetadata Result : Type} : ServerContext Metadata PeerMetadata Result → Class → Nat
  | .owner _ _ _ _ _ inner => ownerReserve inner

/-- The original Server peer installer and its quiet outside client add no primitive query to the selected completion. -/
theorem server_stopped {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : ServerContext Metadata PeerMetadata Result)
    (quiet : RawCtxQuietServerTails.Quiet context) (value : Material) (selected : Class) :
    (simulateQ erase (serverStopped sender route decode context value)).IsQueryBoundP
      (fun query => primitiveClass query = selected) (serverReserve context selected) := by
  cases context with
  | owner request before kid peer outside inner =>
    have first := owner_stopped (sender before.server.metadata) decode inner quiet.2 value selected
    have after : ∀ result, (simulateQ erase (RawCtxPendingServerTails.afterOwner sender route decode
        (RawCtxGenericRoleStorage.mapServer knownKernel before) kid (RawCtxGenericRoleStorage.mapPeer knownKernel peer)
        outside result)).IsQueryBoundP (fun query => primitiveClass query = selected) 0 := by
      intro result
      exact quiet_server sender route decode _ (quiet.1 result.1) _ selected
    simpa only [Nat.add_zero, serverStopped, RawCtxPendingServerTails.liftOwner,
      simulateQ_bind, serverReserve] using isQueryBoundP_bind first (fun result _ => after result)

private theorem quiet_family {M P I D K Result : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result) (quiet : client.IsTotalQueryBound 0)
    (state : RawCtxPendingFamilyTails.State Slot M P I D K S B) (selected : Class) :
    (simulateQ erase (RawCtxPendingFamilyTails.program sender route decode client state)).IsQueryBoundP
      (fun query => primitiveClass query = selected) 0 := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client quiet
  trivial

def familyReserve {M P I D K Result : Type} {S B : Nat} : FamilyContext M P I D K Result S B → Class → Nat
  | .server _ _ _ _ inner => serverReserve inner
  | .beacon _ _ _ _ _ _ inner => ownerReserve inner

/-- Original indexed family publication retains the exact branch-specific pending completion cap and all quiet saved source clients. -/
theorem family_stopped {M P I D K Result : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : FamilyContext M P I D K Result S B)
    (quiet : RawCtxQuietFamilyTails.Quiet context) (value : Material) (selected : Class) :
    (simulateQ erase (familyStopped sender route decode context value)).IsQueryBoundP
      (fun query => primitiveClass query = selected) (familyReserve context selected) := by
  cases context with
  | server request before index outside inner =>
    have first := server_stopped sender route decode inner quiet.2 value selected
    have after : ∀ result, (simulateQ erase (RawCtxPendingFamilyTails.afterServer sender route decode
        (RawCtxGenericRoleFamily.mapRoles knownKernel before) index outside result)).IsQueryBoundP
        (fun query => primitiveClass query = selected) 0 := by
      intro result
      exact quiet_family sender route decode _ (quiet.1 result.1) _ selected
    simpa only [Nat.add_zero, familyStopped, RawCtxPendingFamilyTails.liftServer,
      simulateQ_bind, familyReserve] using isQueryBoundP_bind first (fun result _ => after result)
  | beacon request before index control associatedData outside inner =>
    have first := owner_stopped (before.2 index).beacon.identityKeyId decode inner quiet.2 value selected
    have after : ∀ result, (simulateQ erase (RawCtxPendingFamilyTails.afterBeacon sender route decode
        (RawCtxGenericRoleFamily.mapRoles knownKernel before) index control associatedData outside result)).IsQueryBoundP
        (fun query => primitiveClass query = selected) 0 := by
      intro result
      exact quiet_family sender route decode _ (quiet.1 result.1) _ selected
    simpa only [Nat.add_zero, familyStopped, RawCtxPendingFamilyTails.liftBeacon,
      simulateQ_bind, familyReserve] using isQueryBoundP_bind first (fun result _ => after result)

def contextReserve {M P I D K Result : Type} {S B : Nat} : Context M P I D K Result S B → Class → Nat
  | .family _ _ _ inner => familyReserve inner

/-- Coordinatewise source residual bounds preserve each actual seven-class primitive bill. -/
theorem source_cost_mono (selected : Class) (small large : RawCtxRevealBudgets.Budget)
    (below : RawCtxFamilyResidualBudget.Below small large) : sourceCost selected small ≤ sourceCost selected large := by
  cases selected
  case kdf => exact Nat.add_le_add (below.1 .send) (Nat.mul_le_mul_left _ (below.1 .raw))
  case «seal» => exact below.1 .send
  case «open» => exact below.1 .raw
  case coin => exact below.1 .coin
  case hash => exact below.1 .hash
  case hkdf => exact below.1 .hkdf
  case read => exact below.2

/-- The exact material-only stopped LIVE context has its branch-specific pending reserve plus the original source primitive bill. -/
theorem stopped_class {M P I D K Result : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material) (selected : Class) :
    (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value)).IsQueryBoundP
      (fun query => liveClass query = selected) (contextReserve context selected + sourceCost selected budget) := by
  cases context with
  | family request history outside inner =>
    rcases fits with ⟨residual, below, outsideBound, quiet⟩
    rw [RawCtxFamilyPendingCompiler.stopped_source]
    have first := primitive_forward _ selected _ (family_stopped sender route decode inner quiet value selected)
    have after : ∀ result : (RawCtxProtocolRoles.SourceSpec S B).Range request ×
        RawCtxPendingFamilyTails.State Slot M P I D K S B, ((simulateQ (RawCtxFamilySourceFreshness.compiler
        RawCtxFamilyPendingCompiler.calls RawCtxFamilyPendingCompiler.publicCalls sender route decode)
        (outside result.1)).run (result.2, RawCtxProtocolReveals.tick history)).IsQueryBoundP
        (fun query => liveClass query = selected) (sourceCost selected budget) := by
      intro result
      exact (source_class sender route decode _ residual (outsideBound result.1) _ selected).mono
        (source_cost_mono selected residual budget below)
    exact isQueryBoundP_bind first (fun result _ => after result)

/-- Every selected context completes either a receive or a send, so opening and sealing reserves never accumulate in one pending operation. -/
theorem reserve_shape {M P I D K Result : Type} {S B : Nat} (context : Context M P I D K Result S B) :
    contextReserve context = receiveReserve ∨ contextReserve context = sendReserve := by
  cases context with
  | family request history outside inner =>
    cases inner with
    | server request before index outside inner =>
      cases inner with
      | owner request before kid peer outside inner =>
        cases inner with
        | receive => exact Or.inl rfl
        | send => exact Or.inr rfl
    | beacon request before index control associatedData outside inner =>
      cases inner with
      | receive => exact Or.inl rfl
      | send => exact Or.inr rfl

end BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.pending_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.pending_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.receive_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.receive_effect

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.receive_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.receive_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.send_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.send_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.owner_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.owner_stopped

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.server_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.server_stopped

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.family_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.family_stopped

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.source_cost_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.source_cost_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.stopped_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.stopped_class

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.reserve_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets.reserve_shape
